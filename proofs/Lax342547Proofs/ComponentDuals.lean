import Lax342547.ComponentDuals
import Lax342547.ComponentSpaces

namespace Lax342547Proofs.ComponentDuals
open Lax342547.ComponentDuals

set_option backward.isDefEq.respectTransparency false
open Lax342547.ComponentSpaces Lax342547.CoverClasses
open scoped BigOperators

/--
---
conclusion: Lax342547.ComponentDuals.dual_componentwise_join_closed
---
-/
theorem dual_componentwise_join_closed {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    JoinClosed (DualComponentwise (K := K) (V := V)) := by
  constructor
  · unfold DualComponentwise
    rw [Submodule.map_bot]
    exact Lax342547.ComponentSpaces.componentwise_join_closed.1
  · intro S T hS hT
    unfold DualComponentwise at *
    rw [Submodule.map_sup]
    exact Lax342547.ComponentSpaces.componentwise_join_closed.2 _ _ hS hT

/--
---
conclusion: Lax342547.ComponentDuals.diagonal_dual_identity
---
-/
theorem diagonal_dual_identity {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    (LinearMap.piMap M).dualMap.comp (LinearMap.lsum K W K).toLinearMap =
      (LinearMap.lsum K V K).toLinearMap.comp (LinearMap.piMap (fun i => (M i).dualMap)) := by
  ext f v
  simp [LinearMap.lsum_apply,LinearMap.dualMap_apply]

/--
---
conclusion: Lax342547.ComponentDuals.diagonal_dual_range
---
-/
theorem diagonal_dual_range {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    (LinearMap.range (LinearMap.piMap M).dualMap).map (LinearMap.lsum K V K).symm.toLinearMap =
      coordinateSpace (fun i => LinearMap.range (M i).dualMap) := by
  let A : (∀ i, Module.Dual K (W i)) ≃ₗ[K] Module.Dual K (∀ i, W i) := LinearMap.lsum K W K
  let B : (∀ i, Module.Dual K (V i)) ≃ₗ[K] Module.Dual K (∀ i, V i) := LinearMap.lsum K V K
  have hA : LinearMap.range ((LinearMap.piMap M).dualMap.comp A.toLinearMap) =
      LinearMap.range (LinearMap.piMap M).dualMap := by
    rw [LinearMap.range_comp,A.range,Submodule.map_top]
  rw [← hA,Lax342547.ComponentDuals.diagonal_dual_identity,LinearMap.range_comp,← Submodule.map_comp]
  have hb : B.symm.toLinearMap.comp B.toLinearMap = LinearMap.id := by apply LinearMap.ext; intro v; exact B.symm_apply_apply v
  rw [hb,Submodule.map_id,Lax342547.ComponentSpaces.diagonal_range]

end Lax342547Proofs.ComponentDuals
