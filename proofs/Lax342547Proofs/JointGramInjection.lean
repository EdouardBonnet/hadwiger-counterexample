import Lax342547.JointGramInjection
import Lax342547.CrossBatchMixing
import Lax342547.CrossGramBasis
import Lax342547.FourierTests
import Lax342547.GramNormalization
import Lax342547.GramOrbitDensity
import Lax342547.RealCellLaws
import Lax342547Proofs.FiniteProbability
import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.JointGramInjection
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.GramOrbitDensity Lax342547.RetainedImages Lax342547.JointGramInjection
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

/--
---
conclusion: Lax342547.JointGramInjection.ambient_failure
---
-/
theorem ambient_failure :
    (PMF.uniformOfFintype ((N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary))).toOuterMeasure
        {z | ¬ Good z} ≤
      ((2 : ℝ≥0∞)^(Fintype.card I+Fintype.card K)+(2 : ℝ≥0∞)^(Fintype.card J+Fintype.card L))/
        (2 : ℝ≥0∞)^Fintype.card N := by
  classical
  let p := PMF.uniformOfFintype (Matrix N (I ⊕ K) Binary × Matrix N (J ⊕ L) Binary)
  have hm : p.toOuterMeasure {z | ¬ Function.Injective z.1.mulVec ∧ True} =
      (PMF.uniformOfFintype (Matrix N (I ⊕ K) Binary)).toOuterMeasure
        {z | ¬ Function.Injective z.mulVec} := by
    rw [Lax342547Proofs.FiniteProbability.uniform_product_event,PMF.toOuterMeasure_apply_fintype]
    apply Finset.sum_congr rfl
    intro a _
    have hc : (Fintype.card (Matrix N (J ⊕ L) Binary) : ℝ≥0∞) *
        (Fintype.card (Matrix N (J ⊕ L) Binary) : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)
    by_cases h : Function.Injective a.mulVec <;> simp [h,Set.indicator_apply,hc]
  have hn : p.toOuterMeasure {z | ¬ Function.Injective z.2.mulVec} =
      (PMF.uniformOfFintype (Matrix N (J ⊕ L) Binary)).toOuterMeasure
        {z | ¬ Function.Injective z.mulVec} := by
    rw [Lax342547Proofs.FiniteProbability.uniform_product_event]
    simp only [Set.mem_ofPred_eq,← Finset.sum_mul]
    have hs : ∑ a,PMF.uniformOfFintype (Matrix N (I ⊕ K) Binary) a = 1 := by
      simpa only [tsum_fintype] using (PMF.uniformOfFintype (Matrix N (I ⊕ K) Binary)).tsum_coe
    rw [hs,one_mul]
  have he : {z : Matrix N (I ⊕ K) Binary × Matrix N (J ⊕ L) Binary |
      ¬ (Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec)} =
      {z | ¬ Function.Injective z.1.mulVec ∧ True} ∪ {z | ¬ Function.Injective z.2.mulVec} := by
    ext z; simp only [Set.mem_ofPred_eq,Set.mem_union,and_true,not_and_or]
  have hb₁ : p.toOuterMeasure {z | ¬ Function.Injective z.1.mulVec ∧ True} ≤
      (2 : ℝ≥0∞)^Fintype.card (I ⊕ K)/(2 : ℝ≥0∞)^Fintype.card N := by
    rw [hm]
    exact Lax342547.GramNormalization.column_failure
  have hb₂ : p.toOuterMeasure {z | ¬ Function.Injective z.2.mulVec} ≤
      (2 : ℝ≥0∞)^Fintype.card (J ⊕ L)/(2 : ℝ≥0∞)^Fintype.card N := by
    rw [hn]
    exact Lax342547.GramNormalization.column_failure
  have hh := (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) _ _).trans (add_le_add hb₁ hb₂)
  rw [← he] at hh
  have hmap := Lax342547Proofs.FiniteUniform.map_equiv (ambientEquiv (I := I) (J := J) (K := K) (L := L) (N := N))
  have ht := congrArg (fun q => q.toOuterMeasure
      {z | ¬ (Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec)}) hmap
  rw [PMF.toOuterMeasure_map_apply] at ht
  rw [show {z | ¬ Good z} = ambientEquiv ⁻¹'
      {z | ¬ (Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec)} from rfl,ht]
  simpa only [p,Fintype.card_sum,ENNReal.add_div] using hh

/--
---
conclusion: Lax342547.JointGramInjection.reference_failure
---
-/
theorem reference_failure (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ Fintype.card N)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ Fintype.card N) :
    cellMass (fun z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary) =>
        batchLaw (N := N) G z.1*batchLaw (N := N) H z.2) (fun z => ¬ Good z) ≤
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
        (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/
          (2 : ℝ)^Fintype.card N) := by
  classical
  let u := PMF.uniformOfFintype ((N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary))
  let C := ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
    ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))
  have hc (z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) :
      batchLaw (N := N) G z.1*batchLaw (N := N) H z.2 ≤ C*weights u z := by
    have hh := mul_le_mul (Lax342547.GramOrbitDensity.batch_point_cap G hN₁ z.1)
      (Lax342547.GramOrbitDensity.batch_point_cap H hN₂ z.2)
      ((Lax342547.GramOrbitDensity.batch_probability H).1 z.2) (by positivity)
    have hu : weights u z =
        1/((2 : ℝ)^(Fintype.card N*(Fintype.card I+Fintype.card J))*(2 : ℝ)^(Fintype.card N*(Fintype.card K+Fintype.card L))) := by
      simp [u,weights,PMF.uniformOfFintype_apply,Fintype.card_prod,Fintype.card_fun,Fintype.card_sum,ZMod.card]
    rw [hu]
    simpa only [C,div_mul_div_comm,mul_one_div] using hh
  have hcell : cellMass (fun z => batchLaw (N := N) G z.1*batchLaw (N := N) H z.2) (fun z => ¬ Good z) ≤
      C*cellMass (weights u) (fun z => ¬ Good z) := by
    unfold cellMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    split_ifs
    · exact hc z
    · simp
  have hf := ENNReal.toReal_mono (by apply ENNReal.div_ne_top <;> simp :
      ((2 : ℝ≥0∞)^(Fintype.card I+Fintype.card K)+(2 : ℝ≥0∞)^(Fintype.card J+Fintype.card L))/
        (2 : ℝ≥0∞)^Fintype.card N ≠ ⊤)
      (Lax342547.JointGramInjection.ambient_failure (I := I) (J := J) (K := K) (L := L) (N := N))
  rw [← Lax342547.RealCellLaws.event_mass] at hf
  rw [ENNReal.toReal_div,ENNReal.toReal_add (by simp) (by simp)] at hf
  simp only [ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hf
  exact hcell.trans (mul_le_mul_of_nonneg_left hf (by positivity))

/--
---
conclusion: Lax342547.JointGramInjection.conditioned_reference_failure
---
-/
theorem conditioned_reference_failure {I J K L : Type} [Fintype I] [Fintype J]
    [Fintype K] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    (target : Lax342547.CrossGramBasis.Slots I J K L → Binary)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    cellMass (fun z : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) =>
        batchLaw G z.1*batchLaw H z.2)
      (fun z => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n z = target ∧ ¬ Good z)/
      Lax342547.FourierTests.patternMass (fun z => batchLaw G z.1*batchLaw H z.2)
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) target ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)*
        (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
          (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)) := by
  classical
  let ρ := fun z : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) =>
    batchLaw G z.1*batchLaw H z.2
  let ε := ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
    ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n)
  have hG := Lax342547.GramOrbitDensity.batch_probability (N := Fin n) G
  have hH := Lax342547.GramOrbitDensity.batch_probability (N := Fin n) H
  have htotal : ∑ z,ρ z = 1 := by
    simp only [ρ,Fintype.sum_prod_type,← Finset.mul_sum,hH.2,mul_one,hG.2]
  have hc (t : Lax342547.CrossGramBasis.Slots I J K L → Binary) (ht : t ≠ 0) :
      |Lax342547.FourierTests.characterMean ρ
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) target t| ≤ ε := by
    simpa only [ρ,mul_one] using Lax342547.CrossBatchMixing.weighted_character_bound
      Lax342547.CrossGramBasis.tests n (batchLaw G) (fun _ => 1) (batchLaw H) (fun _ => 1) target t
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2)) ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))
      (fun x => ⟨hG.1 x,by simpa using Lax342547.GramOrbitDensity.batch_point_cap G (by simpa using hN₁) x⟩)
      (fun y => ⟨hH.1 y,by simpa using Lax342547.GramOrbitDensity.batch_point_cap H (by simpa using hN₂) y⟩)
      (by norm_num) (by norm_num) (Lax342547.CrossGramBasis.nonzero_coefficient t ht)
  have hq := Lax342547.FourierTests.scalar_agreement_half ρ
    (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) target ε
    (by dsimp [ε]; positivity) htotal (fun t ht => (abs_le.mp (hc t ht)).1) hsmall
  have hevent : cellMass ρ (fun z =>
      Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n z = target ∧ ¬ Good z) ≤
        cellMass ρ (fun z => ¬ Good z) := by
    unfold cellMass
    apply Finset.sum_le_sum
    intro z _
    by_cases hb : Good z <;> simp [hb]
    split_ifs <;> try rfl
    exact mul_nonneg (hG.1 _) (hH.1 _)
  have hf := Lax342547.JointGramInjection.reference_failure (N := Fin n) G H (by simpa using hN₁) (by simpa using hN₂)
  have hb := hevent.trans hf
  simp only [Fintype.card_fin] at hb
  have hp : (0 : ℝ) < 1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1) := by positivity
  have hd := div_le_div₀ (by positivity : (0 : ℝ) ≤
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
      (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n))
    hb hp hq
  simpa only [Fintype.card_fin,div_div_eq_mul_div,div_one,one_div,div_inv_eq_mul,mul_comm] using hd

end
end Lax342547Proofs.JointGramInjection
