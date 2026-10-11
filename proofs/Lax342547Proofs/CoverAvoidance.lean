import Lax342547.CoverAvoidance
import Lax342547Proofs.CoverProjection

namespace Lax342547Proofs.CoverAvoidance
open Lax342547.CoverAvoidance

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverProjection

/--
---
conclusion: Lax342547.CoverAvoidance.finrank_map_of_disjoint_kernel
---
-/
theorem finrank_map_of_disjoint_kernel {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (S : Submodule K V) (h : Disjoint S (LinearMap.ker f)) :
    Module.finrank K (S.map f) = Module.finrank K S := by
  have hi : Function.Injective (f.domRestrict S) := LinearMap.injective_domRestrict_iff.mpr h
  have hr := LinearMap.finrank_range_of_inj hi
  change Module.finrank K (LinearMap.range (f.comp S.subtype)) = _ at hr
  rw [LinearMap.range_comp,Submodule.range_subtype] at hr
  exact hr

/--
---
conclusion: Lax342547.CoverAvoidance.quotient_rank_of_avoidance
---
-/
theorem quotient_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (h : Disjoint (LinearMap.range M) S) :
    Module.finrank K (LinearMap.range (S.mkQ.comp M)) = Module.finrank K (LinearMap.range M) := by
  rw [LinearMap.range_comp]
  apply finrank_map_of_disjoint_kernel
  simpa only [Submodule.ker_mkQ] using h

/--
---
conclusion: Lax342547.CoverAvoidance.restriction_rank_of_avoidance
---
-/
theorem restriction_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (T : Submodule K (Module.Dual K V))
    (h : Disjoint (LinearMap.range M.dualMap) T) :
    Module.finrank K (LinearMap.range (M.comp T.dualCoannihilator.subtype)) =
      Module.finrank K (LinearMap.range M) := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,← LinearMap.dualMap_comp_dualMap,
    LinearMap.range_comp]
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f := M)]
  apply finrank_map_of_disjoint_kernel
  simpa only [Lax342547Proofs.CoverProjection.cover_restriction_kernel] using h

/--
---
conclusion: Lax342547.CoverAvoidance.projection_rank_of_avoidance
---
-/
theorem projection_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (hS : Disjoint (LinearMap.range M) S) (hT : Disjoint (LinearMap.range M.dualMap) T) :
    Module.finrank K (LinearMap.range (projection M S T)) = Module.finrank K (LinearMap.range M) := by
  unfold projection
  rw [quotient_rank_of_avoidance]
  · exact restriction_rank_of_avoidance M T hT
  · apply hS.mono_left
    rw [LinearMap.range_comp]
    exact LinearMap.map_le_range

end Lax342547Proofs.CoverAvoidance
