import Lax342547.SymmetricPrescriptions

namespace Lax342547Proofs.SymmetricPrescriptions

open Lax342547.MomentSpace

theorem zero_diagonal_rows {I : Type} [Fintype I] [Nonempty I]
    (r : I → Binary) (h : ∑ i, r i = 0) :
    ∃ M : Matrix I I Binary, (∀ i j, M i j = M j i) ∧
      (∀ i, M i i = 0) ∧ ∀ i, ∑ j, M i j = r i := by
  classical
  let p : I := Classical.choice inferInstance
  let M : Matrix I I Binary := fun i j => (if i = p then r j else 0) + (if j = p then r i else 0)
  refine ⟨M, fun i j => add_comm _ _, ?_, ?_⟩
  · intro i
    exact ZModModule.add_self _
  · intro i
    by_cases hi : i = p <;> simp [M, hi, h, Finset.sum_add_distrib]

/--
---
conclusion: Lax342547.SymmetricPrescriptions.diagonal_rows
---
Subtract the diagonal in characteristic two. The desired remaining row
sums total zero, and a symmetric star at one index realizes them with
zero diagonal. Add the prescribed diagonal back.
-/
theorem diagonal_rows {I : Type} [Fintype I] [Nonempty I]
    (a c : I → Binary) (h : ∑ i, c i = ∑ i, a i) :
    ∃ M : Matrix I I Binary, (∀ i j, M i j = M j i) ∧
      (∀ i, M i i = a i) ∧ ∀ i, ∑ j, M i j = c i := by
  classical
  have hz : ∑ i, (c i + a i) = 0 := by
    rw [Finset.sum_add_distrib, h, ZModModule.add_self]
  obtain ⟨M, hs, hd, hr⟩ := zero_diagonal_rows (fun i => c i + a i) hz
  refine ⟨Matrix.diagonal a + M, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij, hs]
  · intro i
    simp [hd]
  · intro i
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    rw [hr]
    simp only [Matrix.diagonal_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm (c i), ← add_assoc, ZModModule.add_self, zero_add]

/--
---
conclusion: Lax342547.SymmetricPrescriptions.rectangular_sums
---
Use one distinguished row and column. They carry the requested column
and row sums, and their common entry corrects the shared total.
-/
theorem rectangular_sums {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (r : I → Binary) (c : J → Binary) (h : ∑ i, r i = ∑ j, c j) :
    ∃ M : Matrix I J Binary, (∀ i, ∑ j, M i j = r i) ∧ ∀ j, ∑ i, M i j = c j := by
  classical
  let p : I := Classical.choice inferInstance
  let q : J := Classical.choice inferInstance
  let M : Matrix I J Binary := fun i j =>
    (if j = q then r i else 0) + (if i = p then c j else 0) +
      (if i = p ∧ j = q then ∑ i, r i else 0)
  refine ⟨M, ?_, ?_⟩
  · intro i
    by_cases hi : i = p
    · simp [M, hi, Finset.sum_add_distrib, h, add_assoc, ZModModule.add_self]
    · simp [M, hi]
  · intro j
    by_cases hj : j = q
    · simp only [M, hj, if_true, and_true, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [add_right_comm, ZModModule.add_self, zero_add]
    · simp [M, hj]

/--
---
conclusion: Lax342547.SymmetricPrescriptions.two_lists
---
Construct the two symmetric diagonal blocks from the self-sum conditions
and the cross block from the equality of its row and column totals.
Its transpose gives the reverse block, so the full matrix has exactly
the required diagonal and both list sums of every row.
-/
theorem two_lists {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a c₁ c₂ : I ⊕ J → Binary)
    (h₁ : ∑ i : I, c₁ (Sum.inl i) = ∑ i : I, a (Sum.inl i))
    (h₂ : ∑ j : J, c₂ (Sum.inr j) = ∑ j : J, a (Sum.inr j))
    (hcross : ∑ i : I, c₂ (Sum.inl i) = ∑ j : J, c₁ (Sum.inr j)) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) Binary, (∀ x y, M x y = M y x) ∧
      (∀ x, M x x = a x) ∧ (∀ x, ∑ i : I, M x (Sum.inl i) = c₁ x) ∧
      ∀ x, ∑ j : J, M x (Sum.inr j) = c₂ x := by
  obtain ⟨M₁, hs₁, hd₁, hr₁⟩ := diagonal_rows (fun i => a (Sum.inl i)) (fun i => c₁ (Sum.inl i)) h₁
  obtain ⟨M₂, hs₂, hd₂, hr₂⟩ := diagonal_rows (fun j => a (Sum.inr j)) (fun j => c₂ (Sum.inr j)) h₂
  obtain ⟨B, hBr, hBc⟩ := rectangular_sums (fun i => c₂ (Sum.inl i)) (fun j => c₁ (Sum.inr j)) hcross
  refine ⟨Matrix.fromBlocks M₁ B B.transpose M₂, ?_, ?_, ?_, ?_⟩
  · intro x y
    cases x with
    | inl i => cases y with
      | inl j => exact hs₁ i j
      | inr j => rfl
    | inr i => cases y with
      | inl j => rfl
      | inr j => exact hs₂ i j
  · intro x
    cases x with
    | inl i => exact hd₁ i
    | inr j => exact hd₂ j
  · intro x
    cases x with
    | inl i => exact hr₁ i
    | inr j => exact hBc j
  · intro x
    cases x with
    | inl i => exact hBr i
    | inr j => exact hr₂ j

end Lax342547Proofs.SymmetricPrescriptions
