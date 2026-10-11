import Lax342547.CellRepresentatives

namespace Lax342547Proofs.CellRepresentatives
open Lax342547.CellRepresentatives

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealCellLaws Lax342547.RetainedImages

/--
---
conclusion: Lax342547.CellRepresentatives.positive_cell_member
---
-/
theorem positive_cell_member {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hC : 0 < cellMass ρ C) :
    ∃ ω, C ω ∧ 0 < ρ ω := by
  classical
  by_contra! h
  have hz : cellMass ρ C ≤ 0 := by
    unfold cellMass
    apply Finset.sum_nonpos
    intro ω _
    split_ifs with hc
    · exact h ω hc
    · exact le_rfl
  exact (not_le_of_gt hC) hz

/--
---
conclusion: Lax342547.CellRepresentatives.retained_cell_representatives
---
-/
theorem retained_cell_representatives {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (τ : ℝ) (hτ : 0 < τ) (hC : τ ≤ cellMass α C) (hD : τ ≤ cellMass β D) :
    ∃ a b, C a ∧ D b ∧ 0 < α a ∧ 0 < β b := by
  obtain ⟨a,ha,hα⟩ := Lax342547.CellRepresentatives.positive_cell_member α C (lt_of_lt_of_le hτ hC)
  obtain ⟨b,hb,hβ⟩ := Lax342547.CellRepresentatives.positive_cell_member β D (lt_of_lt_of_le hτ hD)
  exact ⟨a,b,ha,hb,hα,hβ⟩

end Lax342547Proofs.CellRepresentatives
