import Lax342547.ListDeficits

namespace Lax342547Proofs.ListDeficits
open Lax342547.ListDeficits

set_option backward.isDefEq.respectTransparency false
open Lax342547.SumEnvelope Lax342547.MappedSpans
open scoped BigOperators

/--
---
conclusion: Lax342547.ListDeficits.finset_span_eq
---
-/
theorem finset_span_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) (I : Finset ι) :
    (⨆ i : I, S i.val) = I.sup S := by
  rw [Finset.sup_eq_iSup]
  exact iSup_subtype

/--
---
conclusion: Lax342547.ListDeficits.list_mapped_deficit
---
-/
theorem list_mapped_deficit {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] [FiniteDimensional K U]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (l : List ι) (hl : l.Nodup) :
    dimensionDeficit (fun i : l.toFinset => (S i.val).map f) = mappedDeficit S f l := by
  unfold dimensionDeficit mappedDeficit
  dsimp only
  rw [Lax342547.ListDeficits.finset_span_eq (fun i => (S i).map f) l.toFinset,Finset.sum_coe_sort l.toFinset (fun i => (Module.finrank K ((S i).map f) : ℝ)),List.sum_toFinset _ hl]

end Lax342547Proofs.ListDeficits
