import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
---
title: Joint binary projections for commuting idempotents
type: theorem
---
The simultaneous splitting used in Lemma 5.2, with both dimension bounds.
The projections are indexed by all binary labels; at most dim(V) are nonzero.
-/

namespace Lax342547.JointProjectors

open Lax342547.MomentSpace

axiom exists_joint_decomposition {ι V : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module Binary V] [FiniteDimensional Binary V]
    (M : ι → Module.End Binary V)
    (hid : ∀ i, M i * M i = M i) (hcomm : ∀ i j, M i * M j = M j * M i) :
    ∃ P : (ι → Binary) → Module.End Binary V,
      (∑ s, P s) = 1 ∧ (∀ s, P s * P s = P s) ∧
      (∀ s t, s ≠ t → P s * P t = 0) ∧
      (∀ i s, M i * P s = s i • P s) ∧
      (∑ s, Module.finrank Binary (LinearMap.range (P s))) = Module.finrank Binary V ∧
      Nat.card {s // P s ≠ 0} ≤ Module.finrank Binary V

end Lax342547.JointProjectors
