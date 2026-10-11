import Lax342547.MappedSpans
import Lax342547.ActualDeficits
import Lax342547.GreedySpans

namespace Lax342547Proofs.MappedSpans
open Lax342547.MappedSpans

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

/--
---
conclusion: Lax342547.MappedSpans.mapped_dimension_gain
---
-/
theorem mapped_dimension_gain {K V U : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (f : V →ₗ[K] U) (S : Submodule K V) :
    (Module.finrank K (S.map f) : ℝ) = gain (LinearMap.ker f) S := by
  let g := f.comp S.subtype
  let e : LinearMap.ker g ≃ₗ[K] (S ⊓ LinearMap.ker f : Submodule K V) :=
    { toFun := fun v => ⟨v.val.val,v.val.property,v.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hn := g.finrank_range_add_finrank_ker
  have he := e.finrank_eq
  have hr : LinearMap.range g = S.map f := by rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [he,hr] at hn
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) S
  rw [inf_comm] at hs
  unfold gain
  have hn' : (Module.finrank K (S.map f) : ℝ)+Module.finrank K (S ⊓ LinearMap.ker f : Submodule K V) = Module.finrank K S := by exact_mod_cast hn
  have hs' : (Module.finrank K (LinearMap.ker f ⊔ S : Submodule K V) : ℝ)+Module.finrank K (S ⊓ LinearMap.ker f : Submodule K V) = Module.finrank K (LinearMap.ker f)+Module.finrank K S := by exact_mod_cast hs
  linarith

/--
---
conclusion: Lax342547.MappedSpans.mapped_deficit_eq
---
-/
theorem mapped_deficit_eq {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (l : List ι) :
    mappedDeficit S f l = deficit S (LinearMap.ker f) l := by
  unfold mappedDeficit deficit
  simp_rw [Lax342547.MappedSpans.mapped_dimension_gain]
  rw [← Lax342547.ActualDeficits.map_finset_sup,Lax342547.MappedSpans.mapped_dimension_gain,
    Lax342547.GreedySpans.increments_sum,Lax342547.GreedySpans.span_after_eq]
  rfl

end Lax342547Proofs.MappedSpans
