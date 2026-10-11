import Lax342547.SpanDeficits

/-!
---
title: Monotonicity of span deficits
type: definition and theorem
---
Enlarging each mode space can only increase its addition-map kernel dimension and its span deficit.
-/

namespace Lax342547.SpanDeficitMono

open Lax342547.SpanDeficits
open scoped BigOperators

axiom deficit_monotone {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S T : ι → Submodule K V) (h : ∀ i, S i ≤ T i) :
    ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V)) ≤
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V))

end Lax342547.SpanDeficitMono
