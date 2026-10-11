import Lax342547.FrozenRecords
import Lax342547.RawQueryImages

/-!
---
title: Frozen pin and key records with nominal column budgets
type: lemma
---
Joined pin/key spaces have total dimension bounded by the original pin rank plus the key rank. Unary pairings with their known images cost only nominal columns times that rank, and determine all frozen cross entries. The concrete coordinate count is linear in n.
-/

namespace Lax342547.JoinedRecords

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.FrozenRecords
open Lax342547.ConcreteGeometry Lax342547.TagGeometry

noncomputable def joined {Axis I N : Type} {U : Axis → Type}
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)]
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary)) (a : Axis) :
    Submodule Binary (I → Binary) := P.space a ⊔ LinearMap.range (keys a)

axiom joined_rank_budget {Axis I N : Type} {U : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary)) :
    (∑ a, Module.finrank Binary (joined P keys a)) ≤ P.rank + ∑ a, Module.finrank Binary (U a)

abbrev RecordType (Axis I : Type) (dims : Axis → ℕ) (Status : Type) :=
  (∀ a, Matrix I (Fin (dims a)) Binary) × Status

axiom joined_record_count {Axis I Status : Type}
    [Fintype Axis] [Fintype I] [Fintype Status] (dims : Axis → ℕ) : by
    classical
    exact Fintype.card (RecordType Axis I dims Status) = 2 ^ (Fintype.card I * ∑ a, dims a) * Fintype.card Status

axiom joined_record_bound {Axis I N Status : Type} {U : Axis → Type}
    [Fintype Axis] [Fintype I] [Fintype Status]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (K k s : ℕ) (hP : P.rank ≤ K) (hkeys : (∑ a, Module.finrank Binary (U a)) ≤ k)
    (hstatus : Fintype.card Status ≤ 2^s) : by
    classical
    exact Fintype.card (RecordType Axis I (fun a => Module.finrank Binary (joined P keys a)) Status) ≤
      2 ^ (Fintype.card I * (K+k) + s)

axiom nominal_column_count {B H : Type} [Fintype B] [Fintype H] :
    Fintype.card (Fin 2 × (B ⊕ H)) = 2 * (Fintype.card B + Fintype.card H)

axiom coordinate_linear_budget (k n b degree : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Coordinate k n b degree) ≤
      Fintype.card (SelectorCoordinates b degree) * (Fintype.card (Tag k)^2 + 4) * n

noncomputable def basisVectors {I : Type} [Fintype I]
    (S : Submodule Binary (I → Binary)) : Fin (Module.finrank Binary S) → I → Binary :=
  fun i => (Module.finBasis Binary S i).val

axiom basis_vectors_span {I : Type} [Fintype I]
    (S : Submodule Binary (I → Binary)) : Submodule.span Binary (Set.range (basisVectors S)) = S

axiom basis_records_cross_agreement {I N : Type} [Fintype I] [Fintype N]
    (D E : Submodule Binary (I → Binary))
    (A A' B B' : (I → Binary) →ₗ[Binary] (N → Binary))
    (leftImages : Fin (Module.finrank Binary D) → N → Binary)
    (rightImages : Fin (Module.finrank Binary E) → N → Binary)
    (hleft : ∀ x, A (basisVectors D x) = leftImages x ∧ A' (basisVectors D x) = leftImages x)
    (hright : ∀ y, B (basisVectors E y) = rightImages y ∧ B' (basisVectors E y) = rightImages y)
    (hrecA : record A rightImages = record A' rightImages)
    (hrecB : record B leftImages = record B' leftImages) :
    (∀ v ∈ D, ∀ w, dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) ∧
    (∀ v w, w ∈ E → dotProduct (A v) (B w) = dotProduct (A' v) (B' w))

end Lax342547.JoinedRecords
