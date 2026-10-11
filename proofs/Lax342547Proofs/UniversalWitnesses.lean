import Lax342547.UniversalWitnesses
import Lax342547.ChannelColumns
import Lax342547.FiniteSampling
import Lax342547.IndependentWitnesses
import Lax342547.PhaseAverages
import Lax342547.RealCellLaws

namespace Lax342547Proofs.UniversalWitnesses
open Lax342547.UniversalWitnesses

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

/--
---
conclusion: Lax342547.UniversalWitnesses.some_protected_witness_probability
---
-/
theorem some_protected_witness_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (K : ℕ) (hK : ∀ i,Module.finrank Binary (V i) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∃ S : Submodule Binary (H → Binary),Module.finrank Binary S ≤ K ∧
        ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S) ≤
      (2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) := by
  classical
  let P := fun Y : Matrix N H Binary => ∃ S : Submodule Binary (H → Binary),Module.finrank Binary S ≤ K ∧
    ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S
  let S := fun Y => if h : P Y then h.choose else (⊥ : Submodule Binary (H → Binary))
  have hS (Y : Matrix N H Binary) : Module.finrank Binary (S Y) ≤ K := by
    by_cases h : P Y
    · have he : S Y = h.choose := by dsimp [S];rw [dif_pos h]
      rw [he]
      exact h.choose_spec.1
    · have he : S Y = ⊥ := by dsimp [S];rw [dif_neg h]
      rw [he]
      simp
  have hm : cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary))) P ≤
      cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
        (fun Y => ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S Y) := by
    apply Lax342547.FiniteSampling.cell_mass_mono _ _ _ (Lax342547.RealCellLaws.weights_nonneg _)
    intro Y hY
    simpa only [S,dif_pos hY] using hY.choose_spec.2
  exact hm.trans (Lax342547.IndependentWitnesses.adaptive_independent_witness_probability V hV S K hK hS)

/--
---
conclusion: Lax342547.UniversalWitnesses.marked_unit_witness_probability
---
-/
theorem marked_unit_witness_probability {I H N B : Type}
    [Fintype I] [Fintype H] [Fintype N] [Fintype B] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (β : B → ℝ) (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K : ℕ) (L : ℝ) (hβ : ∀ b,0 ≤ β b) (hL : 0 ≤ L) (hK : ∀ i,Module.finrank Binary (V i) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y) :
    cellMass β (fun b => ∀ i,∃ v : V i,v.val ≠ 0 ∧ (Y b).transpose.mulVec v.val ∈ S b) ≤
      L*((2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)) := by
  classical
  let P := fun y : Matrix N H Binary => ∃ T : Submodule Binary (H → Binary),Module.finrank Binary T ≤ K ∧
    ∀ i,∃ v : V i,v.val ≠ 0 ∧ y.transpose.mulVec v.val ∈ T
  have hm : cellMass β (fun b => ∀ i,∃ v : V i,v.val ≠ 0 ∧ (Y b).transpose.mulVec v.val ∈ S b) ≤
      cellMass β (fun b => P (Y b)) := by
    apply Lax342547.FiniteSampling.cell_mass_mono _ _ _ hβ
    intro b hb
    exact ⟨S b,hS b,hb⟩
  have hp := Lax342547.ChannelColumns.push_cell_mass β Y P
  have hd := Lax342547.PhaseAverages.finite_event_density
    (weights (PMF.uniformOfFintype (Matrix N H Binary))) (push β Y) L hcap P
  have hu := Lax342547.UniversalWitnesses.some_protected_witness_probability (H := H) V hV K hK
  exact (hm.trans_eq hp.symm).trans (hd.trans (mul_le_mul_of_nonneg_left hu hL))

end Lax342547Proofs.UniversalWitnesses
