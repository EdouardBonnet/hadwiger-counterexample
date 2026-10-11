import Lax342547.SpanDeficits
import Mathlib.LinearAlgebra.Pi

namespace Lax342547Proofs.SpanDeficits
open Lax342547.SpanDeficits

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.SpanDeficits.addition_single
---
-/
theorem addition_single {K V ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) (i : ι) (v : S i) :
    addition S (Pi.single i v) = v.val := by
  exact LinearMap.lsum_piSingle K (fun j => S j) K (fun j => (S j).subtype) i v

/--
---
conclusion: Lax342547.SpanDeficits.addition_range
---
-/
theorem addition_range {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) :
    LinearMap.range (addition S) = ⨆ i, S i := by
  classical
  apply le_antisymm
  · rintro v ⟨x,rfl⟩
    have hh : (∑ i, (x i).val) ∈ ⨆ i, S i :=
      Submodule.sum_mem _ (fun i _ => (le_iSup S i) (x i).property)
    simpa only [addition,LinearMap.lsum_apply,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,Submodule.subtype_apply] using hh
  · apply iSup_le
    intro i v hv
    exact ⟨Pi.single i ⟨v,hv⟩,Lax342547.SpanDeficits.addition_single S i ⟨v,hv⟩⟩

/--
---
conclusion: Lax342547.SpanDeficits.addition_kernel_deficit
---
-/
theorem addition_kernel_deficit {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    Module.finrank K (LinearMap.ker (addition S)) =
      (∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V) := by
  have hh := (addition S).finrank_range_add_finrank_ker
  rw [Lax342547.SpanDeficits.addition_range,Module.finrank_pi_fintype] at hh
  omega

end Lax342547Proofs.SpanDeficits
