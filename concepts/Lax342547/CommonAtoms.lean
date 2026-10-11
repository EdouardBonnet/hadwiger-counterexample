import Lax342547.Atoms

/-!
---
title: Common star atoms eliminate the diagonal predictor coefficient
type: definition and theorem
---
Actual equal shared atoms sum to zero across the odd tag star; a linear cut functional constant on those atoms must have constant zero.
-/

namespace Lax342547.CommonAtoms

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.ConcreteGeometry
open Lax342547.CutProfiles
open scoped BigOperators

axiom common_atom_sum_zero {k n b degree : ℕ} (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ l i, i ∉ allowedBase k n l → z i = 0) :
    (∑ l : Tag k, atom (degree := degree) l s z (hz l)) = 0

axiom common_atom_constant_zero {k n b degree : ℕ} (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ l i, i ∉ allowedBase k n l → z i = 0)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (heq : ∀ l, φ (atom (degree := degree) l s z (hz l)) = γ) : γ = 0

end Lax342547.CommonAtoms
