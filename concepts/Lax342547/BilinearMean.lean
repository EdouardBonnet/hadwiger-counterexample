import Lax342547.BilinearWalsh

/-!
---
title: Exact uniform bilinear character mean
type: lemma
---
The mean binary bilinear character under independent uniform coordinates is exactly two to minus the actual matrix rank, by orthogonality and the kernel cardinality.
-/

namespace Lax342547.BilinearMean

open Lax342547.MomentSpace Lax342547.Walsh
open scoped BigOperators

axiom bilinear_character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) :
    (∑ x : I → Binary, ∑ y : J → Binary, phase x (A.mulVec y))/
      ((2 : ℝ)^Fintype.card I*2^Fintype.card J) = 1/(2 : ℝ)^A.rank

end Lax342547.BilinearMean
