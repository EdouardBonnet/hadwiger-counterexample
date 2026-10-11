import Lax342547.AdaptiveProtection
import Lax342547Proofs.ProtectedChannels
import Lax342547Proofs.SmallSubspaceCount
import Lax342547Proofs.ChannelColumns
import Lax342547Proofs.InjectiveFrames

namespace Lax342547Proofs.AdaptiveProtection
open Lax342547.AdaptiveProtection

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators

/--
---
conclusion: Lax342547.AdaptiveProtection.adaptive_protected_probability
---
-/
theorem adaptive_protected_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Matrix N H Binary → Submodule Binary (H → Binary)) (K : ℕ)
    (hS : ∀ Y,Module.finrank Binary (S Y) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S Y) ≤
      (2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) := by
  classical
  let C := {T : Submodule Binary (H → Binary) // Module.finrank Binary T ≤ K}
  letI : Fintype C := Fintype.ofFinite C
  let ρ := weights (PMF.uniformOfFintype (Matrix N H Binary))
  let P := fun c : C => fun Y : Matrix N H Binary => ∀ i,(fun h => (Y.transpose*D) h i) ∈ c.val
  have hm : cellMass ρ (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S Y) ≤
      cellMass ρ (fun Y => ∃ c : C,P c Y) :=
    Lax342547Proofs.FiniteSampling.cell_mass_mono _ _ _
      (Lax342547Proofs.RealCellLaws.weights_nonneg _) (fun Y hY => ⟨⟨S Y,hS Y⟩,hY⟩)
  have hu := Lax342547Proofs.FiniteSampling.cell_mass_union_bound ρ P Finset.univ
    (Lax342547Proofs.RealCellLaws.weights_nonneg _)
  simp only [Finset.mem_univ,true_and] at hu
  have hp (c : C) : cellMass ρ (P c) ≤
      (2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) :=
    Lax342547Proofs.ProtectedChannels.protected_probability_rank_bound D hD c.val K c.property
  have hc : (Fintype.card C : ℝ) ≤ (2 : ℝ)^(Fintype.card H*K) := by
    have hh := Lax342547Proofs.SmallSubspaceCount.small_subspace_card (H := H) K
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ c : C,cellMass ρ (P c) := hm.trans hu
    _ ≤ ∑ _c : C,(2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) :=
      Finset.sum_le_sum (fun c _ => hp c)
    _ = (Fintype.card C : ℝ)*((2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)) := by simp
    _ ≤ (2 : ℝ)^(Fintype.card H*K)*((2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_div_assoc,← pow_add]

end Lax342547Proofs.AdaptiveProtection
