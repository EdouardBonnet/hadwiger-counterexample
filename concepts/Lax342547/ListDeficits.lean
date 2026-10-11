import Lax342547.SumEnvelope
import Lax342547.MappedSpans

/-!
---
title: Actual deficits indexed by a distinct list
type: definition and theorem
---
For distinct remaining indices, the finite family dimension deficit is exactly the mapped list deficit used by greedy exposure.
-/

namespace Lax342547.ListDeficits

open Lax342547.SumEnvelope Lax342547.MappedSpans
open scoped BigOperators

axiom finset_span_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) (I : Finset ι) :
    (⨆ i : I, S i.val) = I.sup S

axiom list_mapped_deficit {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] [FiniteDimensional K U]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (l : List ι) (hl : l.Nodup) :
    dimensionDeficit (fun i : l.toFinset => (S i.val).map f) = mappedDeficit S f l

end Lax342547.ListDeficits
