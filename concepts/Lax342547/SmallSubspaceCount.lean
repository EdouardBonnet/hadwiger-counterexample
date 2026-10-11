import Lax342547.FiniteLinearLaw
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
---
title: Counting all bounded-dimensional protected spaces
type: definition and theorem
---
Padding an actual basis gives a generator encoding of every subspace of dimension at most r and the uniform count 2 to the ambient-dimension times r.
-/

namespace Lax342547.SmallSubspaceCount

open Lax342547.MomentSpace

axiom padded_generators {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) (r : ℕ) (hr : Module.finrank K S ≤ r) :
    ∃ f : Fin r → V, Submodule.span K (Set.range f) = S

axiom small_subspace_card {H : Type} [Fintype H] (r : ℕ) :
    Nat.card {S : Submodule Binary (H → Binary) // Module.finrank Binary S ≤ r} ≤
      2^(Fintype.card H*r)

end Lax342547.SmallSubspaceCount
