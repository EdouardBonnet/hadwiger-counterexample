import Lax342547.SpanDeficitMono
import Lax342547Proofs.SpanDeficits

namespace Lax342547Proofs.SpanDeficitMono
open Lax342547.SpanDeficitMono

set_option backward.isDefEq.respectTransparency false
open Lax342547.SpanDeficits
open scoped BigOperators

/--
---
conclusion: Lax342547.SpanDeficitMono.deficit_monotone
---
-/
theorem deficit_monotone {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S T : ι → Submodule K V) (h : ∀ i, S i ≤ T i) :
    ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V)) ≤
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V)) := by
  classical
  let f : LinearMap.ker (addition S) →ₗ[K] LinearMap.ker (addition T) :=
    { toFun := fun x => ⟨fun i => ⟨(x.val i).val,h i (x.val i).property⟩,by
        have hx := x.property
        simpa only [LinearMap.mem_ker,addition,LinearMap.lsum_apply,LinearMap.sum_apply,
          LinearMap.comp_apply,LinearMap.proj_apply,Submodule.subtype_apply] using hx⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrArg (fun z : LinearMap.ker (addition T) => (z.val i).val) hxy)
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  rwa [Lax342547Proofs.SpanDeficits.addition_kernel_deficit,
    Lax342547Proofs.SpanDeficits.addition_kernel_deficit] at hh

end Lax342547Proofs.SpanDeficitMono
