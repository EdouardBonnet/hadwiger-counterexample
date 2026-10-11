import Lax342547.GreedySpans

/-!
---
title: Dimensions of projected mode spaces
type: lemma
---
The dimension of an actual mode space in an exposed quotient equals its span dimension increase.
-/

namespace Lax342547.ProjectedSpans

open Lax342547.GreedySpans
open scoped BigOperators

axiom projected_dimension_gain {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) :
    (Module.finrank K (S.map W.mkQ) : ℝ) = gain W S

end Lax342547.ProjectedSpans
