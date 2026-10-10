import Lax342547.JoinedRecords
import Lax342547Proofs.FrozenRecords
import Lax342547Proofs.RawQueryImages

namespace Lax342547Proofs.JoinedRecords
open Lax342547.JoinedRecords

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.FrozenRecords
open Lax342547.ConcreteGeometry Lax342547.TagGeometry

/--
---
conclusion: Lax342547.JoinedRecords.joined_rank_budget
---
-/
theorem joined_rank_budget {Axis I N : Type} {U : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary)) :
    (∑ a, Module.finrank Binary (joined P keys a)) ≤ P.rank + ∑ a, Module.finrank Binary (U a) := by
  classical
  unfold joined Pin.rank
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (P.space a) (LinearMap.range (keys a))
  have hr := LinearMap.finrank_range_le (keys a)
  omega

/--
---
conclusion: Lax342547.JoinedRecords.joined_record_count
---
-/
theorem joined_record_count {Axis I Status : Type}
    [Fintype Axis] [Fintype I] [Fintype Status] (dims : Axis → ℕ) : by
    classical
    exact Fintype.card (RecordType Axis I dims Status) = 2 ^ (Fintype.card I * ∑ a, dims a) * Fintype.card Status := by
  classical
  have hc (a : Axis) : Fintype.card (Matrix I (Fin (dims a)) Binary) = 2^(Fintype.card I * dims a) := by
    change Fintype.card (I → Fin (dims a) → Binary) = _
    simp only [Fintype.card_fun, Fintype.card_fin, Binary, ZMod.card]
    rw [← pow_mul, Nat.mul_comm]
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [hc]
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]

/--
---
conclusion: Lax342547.JoinedRecords.joined_record_bound
---
-/
theorem joined_record_bound {Axis I N Status : Type} {U : Axis → Type}
    [Fintype Axis] [Fintype I] [Fintype Status]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (K k s : ℕ) (hP : P.rank ≤ K) (hkeys : (∑ a, Module.finrank Binary (U a)) ≤ k)
    (hstatus : Fintype.card Status ≤ 2^s) : by
    classical
    exact Fintype.card (RecordType Axis I (fun a => Module.finrank Binary (joined P keys a)) Status) ≤
      2 ^ (Fintype.card I * (K+k) + s) := by
  classical
  rw [joined_record_count, pow_add]
  apply Nat.mul_le_mul _ hstatus
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  apply Nat.mul_le_mul_left
  exact (joined_rank_budget P keys).trans (Nat.add_le_add hP hkeys)

/--
---
conclusion: Lax342547.JoinedRecords.nominal_column_count
---
-/
theorem nominal_column_count {B H : Type} [Fintype B] [Fintype H] :
    Fintype.card (Fin 2 × (B ⊕ H)) = 2 * (Fintype.card B + Fintype.card H) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]

/--
---
conclusion: Lax342547.JoinedRecords.coordinate_linear_budget
---
-/
theorem coordinate_linear_budget (k n b degree : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Coordinate k n b degree) ≤
      Fintype.card (SelectorCoordinates b degree) * (Fintype.card (Tag k)^2 + 4) * n := by
  classical
  simp only [Coordinate, Base, Fintype.card_prod, Fintype.card_option, Fintype.card_sum,
    Fintype.card_fin]
  have h : (Fintype.card (Tag k) * Fintype.card (Tag k) * n + 3*n + 1) ≤
      (Fintype.card (Tag k)^2 + 4) * n := by nlinarith
  nlinarith

/--
---
conclusion: Lax342547.JoinedRecords.basis_vectors_span
---
-/
theorem basis_vectors_span {I : Type} [Fintype I]
    (S : Submodule Binary (I → Binary)) : Submodule.span Binary (Set.range (basisVectors S)) = S := by
  classical
  change Submodule.span Binary (Set.range (S.subtype ∘ Module.finBasis Binary S)) = S
  rw [Set.range_comp, ← Submodule.map_span, (Module.finBasis Binary S).span_eq,
    Submodule.map_top, Submodule.range_subtype]

/--
---
conclusion: Lax342547.JoinedRecords.basis_records_cross_agreement
---
-/
theorem basis_records_cross_agreement {I N : Type} [Fintype I] [Fintype N]
    (D E : Submodule Binary (I → Binary))
    (A A' B B' : (I → Binary) →ₗ[Binary] (N → Binary))
    (leftImages : Fin (Module.finrank Binary D) → N → Binary)
    (rightImages : Fin (Module.finrank Binary E) → N → Binary)
    (hleft : ∀ x, A (basisVectors D x) = leftImages x ∧ A' (basisVectors D x) = leftImages x)
    (hright : ∀ y, B (basisVectors E y) = rightImages y ∧ B' (basisVectors E y) = rightImages y)
    (hrecA : record A rightImages = record A' rightImages)
    (hrecB : record B leftImages = record B' leftImages) :
    (∀ v ∈ D, ∀ w, dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) ∧
    (∀ v w, w ∈ E → dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) := by
  have h := Lax342547Proofs.FrozenRecords.two_records_cross_agreement A A' B B'
    (basisVectors D) (basisVectors E) leftImages rightImages hleft hright hrecA hrecB
  rwa [basis_vectors_span, basis_vectors_span] at h

end Lax342547Proofs.JoinedRecords
