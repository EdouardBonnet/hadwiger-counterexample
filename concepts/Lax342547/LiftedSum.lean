import Lax342547.BlockDeficits

/-!
---
title: Identification of the lifted tensor sum
type: lemma
---
The abstract block addition map is exactly the sum of the individually included tensors with their actual dual restrictions.
-/

namespace Lax342547.LiftedSum

open Lax342547.SpanDeficits Lax342547.BlockDeficits
open scoped BigOperators

axiom lifted_sum_apply {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) (f : Module.Dual K V) :
    liftedSum S T M f = ∑ i, (M i ((T i).subtype.dualMap f)).val

end Lax342547.LiftedSum
