import Lax342547.CoverClasses
import Lax342547.DirectRanks

/-!
---
title: Componentwise mode spaces and diagonal tensors
type: lemma
---
Coordinatewise mode subspaces form a join-stable cover class, and the range of a diagonal tensor map is the product of its component ranges.
-/

namespace Lax342547.ComponentSpaces

open Lax342547.CoverClasses
open scoped BigOperators

noncomputable def coordinateSpace {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (S : ∀ i, Submodule K (V i)) :
    Submodule K (∀ i, V i) where
  carrier := {v | ∀ i, v i ∈ S i}
  zero_mem' := fun i => (S i).zero_mem
  add_mem' := fun h g i => (S i).add_mem (h i) (g i)
  smul_mem' := fun c _ h i => (S i).smul_mem c (h i)

def Componentwise {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : Submodule K (∀ i, V i)) : Prop := ∃ S, T = coordinateSpace S

axiom coordinate_space_bot {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    coordinateSpace (fun i => (⊥ : Submodule K (V i))) = ⊥

axiom coordinate_space_sup {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (S T : ∀ i, Submodule K (V i)) :
    coordinateSpace S ⊔ coordinateSpace T = coordinateSpace (fun i => S i ⊔ T i)

axiom componentwise_join_closed {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] : JoinClosed (Componentwise (K := K) (V := V))

axiom diagonal_range {K e : Type} [Field K] {V W : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    LinearMap.range (LinearMap.piMap M) = coordinateSpace (fun i => LinearMap.range (M i))

end Lax342547.ComponentSpaces
