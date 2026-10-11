import Lax342547.ComponentSpaces

/-!
---
title: Rows of diagonal tensor maps
type: lemma
---
Dualizing a componentwise tensor map preserves its componentwise row spaces through the finite product dual equivalence; these row cover spaces are closed under joins.
-/

namespace Lax342547.ComponentDuals

open Lax342547.ComponentSpaces Lax342547.CoverClasses
open scoped BigOperators

def DualComponentwise {K e : Type} [Field K] [Fintype e] [DecidableEq e] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : Submodule K (Module.Dual K (∀ i, V i))) : Prop :=
    Componentwise (T.map (LinearMap.lsum K V K).symm.toLinearMap)

axiom dual_componentwise_join_closed {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    JoinClosed (DualComponentwise (K := K) (V := V))

axiom diagonal_dual_identity {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    (LinearMap.piMap M).dualMap.comp (LinearMap.lsum K W K).toLinearMap =
      (LinearMap.lsum K V K).toLinearMap.comp (LinearMap.piMap (fun i => (M i).dualMap))

axiom diagonal_dual_range {K e : Type} [Field K] [Fintype e] [DecidableEq e]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    (LinearMap.range (LinearMap.piMap M).dualMap).map (LinearMap.lsum K V K).symm.toLinearMap =
      coordinateSpace (fun i => LinearMap.range (M i).dualMap)

end Lax342547.ComponentDuals
