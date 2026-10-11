import Lax342547.ConcreteGeometry

/-!
---
title: Dimensions of the concrete coefficient space
type: lemma
---
The selector dimension counts squarefree monomials by cardinality.
The base coordinates comprise g² ordinary blocks and three common blocks,
each of length n; the coefficient space has one extra constant coordinate.
-/

namespace Lax342547.CoordinateCounts

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

axiom coordinate_dimensions (k n b degree : ℕ) :
    Fintype.card (SelectorCoordinates b degree) = ∑ j ∈ Finset.range (degree + 1), b.choose j ∧
    Fintype.card (Base k n) = ((2 * k + 1) ^ 2 + 3) * n ∧
    Fintype.card (Coordinate k n b degree) =
      (∑ j ∈ Finset.range (degree + 1), b.choose j) * (1 + ((2 * k + 1) ^ 2 + 3) * n)

end Lax342547.CoordinateCounts
