import Lax342547.ProjectedSpans
import Lax342547Proofs.GreedySpans

namespace Lax342547Proofs.ProjectedSpans
open Lax342547.ProjectedSpans

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans
open scoped BigOperators

/--
---
conclusion: Lax342547.ProjectedSpans.projected_dimension_gain
---
-/
theorem projected_dimension_gain {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) :
    (Module.finrank K (S.map W.mkQ) : ℝ) = gain W S := by
  let f := W.mkQ.comp S.subtype
  let e : LinearMap.ker f ≃ₗ[K] (S ⊓ W : Submodule K V) :=
    { toFun := fun v => ⟨v.val.val,v.val.property,by
        have hv : v.val.val ∈ LinearMap.ker W.mkQ := v.property
        rwa [Submodule.ker_mkQ] at hv⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,by
        change W.mkQ x.val = 0
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_mkQ]
        exact x.property.2⟩
      left_inv := fun v => by rfl
      right_inv := fun v => by rfl
      map_add' := fun v w => by rfl
      map_smul' := fun a v => by rfl }
  have hn := f.finrank_range_add_finrank_ker
  have he := e.finrank_eq
  have hr : LinearMap.range f = S.map W.mkQ := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [he,hr] at hn
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W S
  rw [inf_comm] at hs
  unfold gain
  have hn' : (Module.finrank K (S.map W.mkQ) : ℝ)+Module.finrank K (S ⊓ W : Submodule K V) = Module.finrank K S := by exact_mod_cast hn
  have hs' : (Module.finrank K (W ⊔ S : Submodule K V) : ℝ)+Module.finrank K (S ⊓ W : Submodule K V) = Module.finrank K W+Module.finrank K S := by exact_mod_cast hs
  linarith

end Lax342547Proofs.ProjectedSpans
