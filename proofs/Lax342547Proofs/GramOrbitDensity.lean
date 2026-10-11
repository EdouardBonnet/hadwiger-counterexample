import Lax342547.GramOrbitDensity
import Lax342547Proofs.GramNormalization
import Lax342547Proofs.RealCellLaws
import Lax342547Proofs.CrossGramBasis

namespace Lax342547Proofs.GramOrbitDensity
noncomputable section

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.GramOrbitDensity Lax342547.RelativeEntropy
open scoped ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.GramOrbitDensity.batch_probability
---
-/
theorem batch_probability {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    [Nonempty (Orbit N G)] : Probability (batchLaw (N := N) G) := by
  classical
  exact ⟨Lax342547Proofs.RealCellLaws.weights_nonneg _,Lax342547Proofs.RealCellLaws.weights_total _⟩

/--
---
conclusion: Lax342547.GramOrbitDensity.batch_point_cap
---
-/
theorem batch_point_cap {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    [Nonempty (Orbit N G)] (hN : Fintype.card I+Fintype.card J+1 ≤ Fintype.card N)
    (x : N × (I ⊕ J) → Binary) :
    batchLaw G x ≤ (2 : ℝ)^(Fintype.card I*Fintype.card J+2)/
      (2 : ℝ)^(Fintype.card N*(Fintype.card I+Fintype.card J)) := by
  classical
  let c : ℝ≥0∞ := 2^(Fintype.card I*Fintype.card J+2)
  have hq : 1 ≤ c*Lax342547.GramNormalization.probability (N := N) G := by
    have hg := Lax342547Proofs.GramNormalization.normalization_quarter (N := N) G hN
    change 1/c ≤ Lax342547.GramNormalization.probability (N := N) G at hg
    calc
      1 = c*(1/c) := by simp [c,ENNReal.mul_inv_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_left hg zero_le
  have hp (z : Matrix N I Binary × Matrix N J Binary) :
      (PMF.uniformOfFintype (Orbit N G)).map Subtype.val z ≤
        c*PMF.uniformOfFintype (Matrix N I Binary × Matrix N J Binary) z := by
    exact @Lax342547Proofs.FiniteProbability.uniform_subtype_point_factor
      (Matrix N I Binary × Matrix N J Binary) inferInstance inferInstance
      {z | Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose*z.2 = G}
      (inferInstanceAs (Fintype (Orbit N G))) (inferInstanceAs (Nonempty (Orbit N G))) c hq z
  have hm := Lax342547Proofs.FiniteProbability.map_density
    ((PMF.uniformOfFintype (Orbit N G)).map Subtype.val)
    (PMF.uniformOfFintype (Matrix N I Binary × Matrix N J Binary)) c hp batchEquiv x
  rw [PMF.map_comp,Lax342547Proofs.FiniteUniform.map_equiv] at hm
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [c]) (PMF.apply_ne_top _ _)) hm
  change (batchLaw G x) ≤ _ at hr
  simp only [c,PMF.uniformOfFintype_apply,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_inv,ENNReal.toReal_natCast] at hr
  have hcard : Fintype.card (N × (I ⊕ J) → Binary) =
      2^(Fintype.card N*(Fintype.card I+Fintype.card J)) := by
    simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_sum,ZMod.card]
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat] at hr
  simpa only [div_eq_mul_inv] using hr

/--
---
conclusion: Lax342547.GramOrbitDensity.mutual_gram_comparison
---
-/
theorem mutual_gram_comparison {I J K L : Type} [Fintype I] [Fintype J]
    [Fintype K] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (N : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit (Fin N) G)] [Nonempty (Orbit (Fin N) H)]
    (f : (Fin N × (I ⊕ J) → Binary) → ℝ) (g : (Fin N × (K ⊕ L) → Binary) → ℝ)
    (target : Lax342547.CrossGramBasis.Slots I J K L → Binary)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ N)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ N)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |Lax342547.FourierTests.patternMass (fun xy => batchLaw G xy.1*batchLaw H xy.2*(f xy.1*g xy.2))
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests N) target /
      Lax342547.FourierTests.patternMass (fun xy => batchLaw G xy.1*batchLaw H xy.2)
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests N) target -
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^N)) := by
  apply Lax342547Proofs.CrossBatchMixing.cross_batch_comparison
    Lax342547.CrossGramBasis.tests N (batchLaw G) f (batchLaw H) g target
    ((2 : ℝ)^(Fintype.card I*Fintype.card J+2)) ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))
    (batch_probability (N := Fin N) G) (batch_probability (N := Fin N) H)
  · intro x
    simpa using batch_point_cap G (by simpa using hN₁) x
  · intro x
    simpa using batch_point_cap H (by simpa using hN₂) x
  · exact hf
  · exact hg
  · exact Lax342547Proofs.CrossGramBasis.nonzero_coefficient
  · exact hsmall

end
end Lax342547Proofs.GramOrbitDensity
