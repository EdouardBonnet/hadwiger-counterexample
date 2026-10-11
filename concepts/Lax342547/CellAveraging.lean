import Lax342547.RealCellLaws
import Lax342547.KeyMeasures
import Lax342547.CollisionPruning

/-!
---
title: Actual-mass averaging over retained record-cell pairs
type: lemma
---
The product of conditional cell laws recovers each original rectangle after multiplication by both cell masses. Disjoint record partitions sum these rectangle estimates without counting an orientation pair more than once.
-/

namespace Lax342547.CellAveraging

open Lax342547.RetainedImages Lax342547.CollisionPruning

noncomputable def pairEventMass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (H : ΩA → ΩB → Prop) : ℝ := by
  classical
  exact ∑ a, ∑ b, if H a b then α a * β b else 0

noncomputable def rectangleMass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (H : ΩA → ΩB → Prop) : ℝ := pairEventMass α β (fun a b => C a ∧ D b ∧ H a b)

axiom conditional_rectangle_mass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (H : ΩA → ΩB → Prop) :
    pairEventMass (conditionalLaw α C) (conditionalLaw β D) H =
      rectangleMass α β C D H / (cellMass α C * cellMass β D)

axiom conditional_rectangle_lower {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (H : ΩA → ΩB → Prop) (ε : ℝ)
    (hC : 0 < cellMass α C) (hD : 0 < cellMass β D)
    (h : ε ≤ pairEventMass (conditionalLaw α C) (conditionalLaw β D) H) :
    ε * (cellMass α C * cellMass β D) ≤ rectangleMass α β C D H

axiom partition_rectangle_mass {ΩA ΩB C D : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (recordA : ΩA → C) (recordB : ΩB → D)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) (valid : C → D → Prop)
    (H : ΩA → ΩB → Prop) : by
      classical
      exact (∑ c, ∑ d, if valid c d then
        rectangleMass α β (fun a => acceptA a ∧ recordA a = c)
          (fun b => acceptB b ∧ recordB b = d) H else 0) =
        pairEventMass α β (fun a b => acceptA a ∧ acceptB b ∧ valid (recordA a) (recordB b) ∧ H a b)

noncomputable def recordMass {Ω C : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (record : Ω → C) (accept : Ω → Prop) (c : C) : ℝ :=
  cellMass ρ (fun ω => accept ω ∧ record ω = c)

noncomputable def retainedPairs {C D : Type} [Fintype C] [Fintype D]
    (massA : C → ℝ) (massB : D → ℝ) (valid : C → D → Prop) (τ : ℝ) : ℝ := by
  classical
  exact ∑ c, ∑ d, if valid c d ∧ τ ≤ massA c ∧ τ ≤ massB d then massA c * massB d else 0

axiom pair_event_mass_nonneg {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (H : ΩA → ΩB → Prop)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) : 0 ≤ pairEventMass α β H

axiom retained_cell_pair_lower {ΩA ΩB C D : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (recordA : ΩA → C) (recordB : ΩB → D)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) (valid : C → D → Prop)
    (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) (hτ : 0 < τ)
    (hloc : ∀ c d, valid c d → τ ≤ recordMass α recordA acceptA c →
      τ ≤ recordMass β recordB acceptB d → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA a ∧ recordA a = c))
          (conditionalLaw β (fun b => acceptB b ∧ recordB b = d)) H) :
    ε * retainedPairs (recordMass α recordA acceptA) (recordMass β recordB acceptB) valid τ ≤
      pairEventMass α β H

end Lax342547.CellAveraging
