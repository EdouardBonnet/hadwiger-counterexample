import Lax342547.RestrictionRank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.RestrictionRank

set_option backward.isDefEq.respectTransparency false

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V]

theorem finrank_le_map_add_ker (f : V →ₗ[K] W) (S : Submodule K V) :
    Module.finrank K S ≤ Module.finrank K (S.map f) + Module.finrank K (LinearMap.ker f) := by
  let fS := f.comp S.subtype
  let i : LinearMap.ker fS →ₗ[K] LinearMap.ker f := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have h := fS.finrank_range_add_finrank_ker
  have hmap : LinearMap.range fS = S.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hmap] at h
  omega

theorem domain_restriction_rank (f : V →ₗ[K] W) (S : Submodule K V) :
    Module.finrank K (LinearMap.range f) ≤ Module.finrank K (LinearMap.range (f.comp S.subtype)) +
      (Module.finrank K V - Module.finrank K S) := by
  have h := finrank_le_map_add_ker f S
  have hr := f.finrank_range_add_finrank_ker
  have hS := S.finrank_le
  rw [LinearMap.range_comp, Submodule.range_subtype]
  omega

/--
---
conclusion: Lax342547.RestrictionRank.bilinear_restriction_rank
---
Restricting the domain loses at most the subspace codimension. Restricting
the output functional to that subspace loses at most the dimension of
its annihilator, which is the same codimension. Rank-nullity combines
the two losses.
-/
theorem bilinear_restriction_rank (B : LinearMap.BilinForm K V) (S : Submodule K V) :
    Module.finrank K (LinearMap.range B) ≤ Module.finrank K (LinearMap.range (B.restrict S)) +
      2 * (Module.finrank K V - Module.finrank K S) := by
  have hdom := domain_restriction_rank B S
  have hout := finrank_le_map_add_ker S.subtype.dualMap (LinearMap.range (LinearMap.comp B S.subtype))
  have hdual := S.subtype.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective S.subtype_injective),
    finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at hdual
  have heq : B.restrict S = S.subtype.dualMap.comp (LinearMap.comp B S.subtype) := rfl
  rw [← LinearMap.range_comp, ← heq] at hout
  have hk : Module.finrank K (LinearMap.ker S.subtype.dualMap) =
      Module.finrank K V - Module.finrank K S := by omega
  calc
    _ ≤ Module.finrank K (LinearMap.range (LinearMap.comp B S.subtype)) +
        (Module.finrank K V - Module.finrank K S) := hdom
    _ ≤ (Module.finrank K (LinearMap.range (B.restrict S)) +
        Module.finrank K (LinearMap.ker S.subtype.dualMap)) +
        (Module.finrank K V - Module.finrank K S) := Nat.add_le_add_right hout _
    _ = _ := by rw [hk]; omega

end Lax342547Proofs.RestrictionRank
