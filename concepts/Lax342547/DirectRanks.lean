import Lax342547.RestrictionRank
import Mathlib.LinearAlgebra.Pi

/-!
---
title: Rank of a diagonal family
type: lemma
---
The range of a coordinatewise linear map is the product of its coordinate ranges, so its rank is the sum of their ranks.
-/

namespace Lax342547.DirectRanks

open scoped BigOperators

noncomputable def rangeProductEquiv {K ι : Type} [Field K]
    {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (M : ∀ i, V i →ₗ[K] W i) :
    LinearMap.range (LinearMap.piMap M) ≃ₗ[K] (∀ i, LinearMap.range (M i)) := by
  classical
  let f : LinearMap.range (LinearMap.piMap M) →ₗ[K] (∀ i, LinearMap.range (M i)) :=
    { toFun := fun w i => ⟨w.val i,by obtain ⟨v,hv⟩ := w.property; exact ⟨v i,congrFun hv i⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine LinearEquiv.ofBijective f ?_
  constructor
  · intro w z h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro w
    have hex : ∀ i, ∃ v, M i v = (w i).val := fun i => (w i).property
    choose v hv using hex
    refine ⟨⟨fun i => (w i).val,⟨v,?_⟩⟩,?_⟩
    · funext i
      exact hv i
    · rfl

axiom diagonal_rank_sum {K ι : Type} [Field K] [Fintype ι]
    {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    Module.finrank K (LinearMap.range (LinearMap.piMap M)) =
      ∑ i, Module.finrank K (LinearMap.range (M i))

end Lax342547.DirectRanks
