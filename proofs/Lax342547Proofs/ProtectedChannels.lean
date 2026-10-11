import Lax342547.ProtectedChannels
import Lax342547Proofs.FiniteLinearLaw
import Lax342547.InjectiveFrames
import Lax342547.RealCellLaws

namespace Lax342547Proofs.ProtectedChannels
open Lax342547.ProtectedChannels

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal

/--
---
conclusion: Lax342547.ProtectedChannels.protected_columns_card
---
-/
theorem protected_columns_card {I H : Type} [Fintype I] [Fintype H]
    (S : Submodule Binary (H → Binary)) :
    Nat.card {Z : Matrix H I Binary // ∀ i,(fun h => Z h i) ∈ S} =
      2^(Module.finrank Binary S*Fintype.card I) := by
  classical
  rw [Nat.card_congr (columnSpaceEquiv (I := I) S),Nat.card_eq_fintype_card,Fintype.card_fun,
    Lax342547Proofs.FiniteLinearLaw.binary_card S,← pow_mul]

/--
---
conclusion: Lax342547.ProtectedChannels.independent_protected_probability
---
-/
theorem independent_protected_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Submodule Binary (H → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S) =
      (2 : ℝ)^(Module.finrank Binary S*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) := by
  classical
  rw [Lax342547.RealCellLaws.event_mass]
  have ht := Lax342547.InjectiveFrames.transpose_uniform (H := H) D hD
  have hm := congrArg (fun p : PMF (Matrix H I Binary) => p.toOuterMeasure
    {Z | ∀ i,(fun h => Z h i) ∈ S}) ht
  rw [PMF.toOuterMeasure_map_apply] at hm
  change ((PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure
    ((fun Y => Y.transpose*D) ⁻¹' {Z : Matrix H I Binary | ∀ i,(fun h => Z h i) ∈ S})).toReal = _
  rw [hm,PMF.toOuterMeasure_uniformOfFintype_apply]
  have hc := Lax342547.ProtectedChannels.protected_columns_card (I := I) S
  rw [Nat.card_eq_fintype_card] at hc
  have hfull : Fintype.card (Matrix H I Binary) = 2^(Fintype.card H*Fintype.card I) := by
    simp [Matrix,Fintype.card_fun,ZMod.card,← pow_mul,Nat.mul_comm]
  change ((Fintype.card {Z : Matrix H I Binary // ∀ i,(fun h => Z h i) ∈ S} : ℝ≥0∞)/
    (Fintype.card (Matrix H I Binary) : ℝ≥0∞)).toReal = _
  rw [hc,hfull,ENNReal.toReal_div]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_ofNat]

/--
---
conclusion: Lax342547.ProtectedChannels.protected_probability_rank_bound
---
-/
theorem protected_probability_rank_bound {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Submodule Binary (H → Binary)) (K : ℕ) (hS : Module.finrank Binary S ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S) ≤
      (2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) := by
  rw [Lax342547.ProtectedChannels.independent_protected_probability D hD S]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hS)) (by positivity)

end Lax342547Proofs.ProtectedChannels
