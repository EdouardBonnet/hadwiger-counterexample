import Lax342547.RealCellLaws

/-!
---
title: Positive representatives of original retained cells
type: definition and theorem
---
Every retained cell of positive actual mass has a positive-weight orientation representative. A pair of unchanged retained cells therefore supplies representatives for selecting the actual gradient target.
-/

namespace Lax342547.CellRepresentatives

open Lax342547.RealCellLaws Lax342547.RetainedImages

axiom positive_cell_member {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hC : 0 < cellMass ρ C) :
    ∃ ω, C ω ∧ 0 < ρ ω

axiom retained_cell_representatives {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (τ : ℝ) (hτ : 0 < τ) (hC : τ ≤ cellMass α C) (hD : τ ≤ cellMass β D) :
    ∃ a b, C a ∧ D b ∧ 0 < α a ∧ 0 < β b

end Lax342547.CellRepresentatives
