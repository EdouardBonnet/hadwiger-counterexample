import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
---
title: Rank loss under restriction of a bilinear form
type: theorem
---
Restricting both arguments to a subspace of codimension c loses at
most 2c in rank. No symmetry, positivity, or characteristic assumption
is needed. Applied to the polar form, this is the rank-loss step in
the unary mixer estimate of Lemma 5.5.
-/

namespace Lax342547.RestrictionRank

axiom bilinear_restriction_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (S : Submodule K V) :
    Module.finrank K (LinearMap.range B) ≤ Module.finrank K (LinearMap.range (B.restrict S)) +
      2 * (Module.finrank K V - Module.finrank K S)

end Lax342547.RestrictionRank
