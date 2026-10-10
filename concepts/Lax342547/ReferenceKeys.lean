import Lax342547.GramNormalization

/-!
---
title: Constrained key reference spaces have positive density
type: definition and theorem
---
Independent component Gram constraints have an explicit product lower bound independent of ambient dimension once the slot count fits. The constrained key space has at most two to the number of ambient key bits elements.
-/

namespace Lax342547.ReferenceKeys

open Lax342547.MomentSpace
open scoped ENNReal

abbrev Tuples (Comp : Type) (Pos : Comp → Type) (N : Type) :=
  ∀ e, Matrix N (Pos e) Binary × Matrix N (Pos e) Binary

noncomputable def space {Comp : Type} (Pos : Comp → Type) (N : Type)
    [∀ e, Fintype (Pos e)] [Fintype N] (G : ∀ e, Matrix (Pos e) (Pos e) Binary) :
    Set (Tuples Comp Pos N) := {x | ∀ e, (x e).1.transpose * (x e).2 = G e}

axiom space_card_upper {Comp N : Type} [Fintype Comp] [Fintype N]
    (Pos : Comp → Type) [∀ e, Fintype (Pos e)]
    (G : ∀ e, Matrix (Pos e) (Pos e) Binary) : by
      classical
      exact Fintype.card (space Pos N G) ≤
        2 ^ ((2 * ∑ e, Fintype.card (Pos e)) * Fintype.card N)

axiom block_reference_lower {I N : Type} [Fintype I] [Fintype N]
    [DecidableEq I] [DecidableEq N] (G : Matrix I I Binary)
    (hN : 2 * Fintype.card I + 1 ≤ Fintype.card N) :
    1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card I + 2) ≤
      ((PMF.uniformOfFintype (Matrix N I Binary × Matrix N I Binary)).map
        (fun x => x.1.transpose * x.2)) G

axiom reference_density_lower {Comp N : Type} [Fintype Comp] [Fintype N]
    [DecidableEq Comp] [DecidableEq N]
    (Pos : Comp → Type) [∀ e, Fintype (Pos e)] [∀ e, DecidableEq (Pos e)]
    (G : ∀ e, Matrix (Pos e) (Pos e) Binary)
    (hN : ∀ e, 2 * Fintype.card (Pos e) + 1 ≤ Fintype.card N) :
    (∏ e, 1 / (2 : ℝ≥0∞) ^ (Fintype.card (Pos e) * Fintype.card (Pos e) + 2)) ≤
      (PMF.uniformOfFintype (Tuples Comp Pos N)).toOuterMeasure (space Pos N G)

end Lax342547.ReferenceKeys
