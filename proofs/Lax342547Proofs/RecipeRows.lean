import Lax342547.RecipeRows
import Lax342547Proofs.SymmetricPrescriptions
import Lax342547Proofs.BinaryPrescriptions

namespace Lax342547Proofs.RecipeRows

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.BinaryPrescriptions

/--
---
conclusion: Lax342547.RecipeRows.recipe_matrix
---
The two role equations turn the opposite coupled equation into equality
of the cross row totals. The two self totals already equal the prescribed
diagonal sums. Construct the symmetric matrix with those row sums; its
symmetry converts them into exactly the two list-gradient requirements.
-/
theorem recipe_matrix {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a opposite p : I ⊕ J → Binary)
    (hrole₁ : (∑ i : I, a (Sum.inl i)) + (∑ i : I, opposite (Sum.inl i)) = 1)
    (hrole₂ : (∑ j : J, a (Sum.inr j)) + (∑ j : J, opposite (Sum.inr j)) = 1)
    (hcoupled : (∑ i : I, (p (Sum.inl i) + opposite (Sum.inl i))) =
      ∑ j : J, (p (Sum.inr j) + opposite (Sum.inr j))) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) Binary, (∀ x y, M x y = M y x) ∧
      (∀ x, M x x = a x) ∧
      (∀ i : I, a (Sum.inl i) + ∑ t : I, M (Sum.inl t) (Sum.inl i) = 0) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : I, M (Sum.inl t) (Sum.inr j) = p (Sum.inr j)) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : J, M (Sum.inr t) (Sum.inr j) = 0) ∧
      (∀ i : I, a (Sum.inl i) + ∑ t : J, M (Sum.inr t) (Sum.inl i) = p (Sum.inl i)) := by
  have hcancel (x y : Binary) : x + (x + y) = y := by
    rw [← add_assoc, ZModModule.add_self, zero_add]
  have hc := hcoupled
  simp only [Finset.sum_add_distrib] at hc
  have hcross : (∑ i : I, (a (Sum.inl i) + p (Sum.inl i))) =
      ∑ j : J, (a (Sum.inr j) + p (Sum.inr j)) := by
    simp only [Finset.sum_add_distrib]
    calc
      _ = ((∑ i : I, a (Sum.inl i)) + (∑ i : I, opposite (Sum.inl i))) +
          ((∑ i : I, p (Sum.inl i)) + (∑ i : I, opposite (Sum.inl i))) := by
        simp [add_assoc, add_left_comm, add_comm, hcancel]
      _ = ((∑ j : J, a (Sum.inr j)) + (∑ j : J, opposite (Sum.inr j))) +
          ((∑ j : J, p (Sum.inr j)) + (∑ j : J, opposite (Sum.inr j))) := by
        rw [hrole₁, hrole₂, hc]
      _ = _ := by simp [add_assoc, add_left_comm, add_comm, hcancel]
  let c₁ : I ⊕ J → Binary := Sum.elim (fun i => a (.inl i)) (fun j => a (.inr j) + p (.inr j))
  let c₂ : I ⊕ J → Binary := Sum.elim (fun i => a (.inl i) + p (.inl i)) (fun j => a (.inr j))
  obtain ⟨M, hsym, hdiag, h₁, h₂⟩ := SymmetricPrescriptions.two_lists a c₁ c₂ rfl rfl hcross
  refine ⟨M, hsym, hdiag, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Finset.sum_congr rfl (fun t _ => hsym _ _), h₁]
    exact ZModModule.add_self _
  · intro j
    rw [Finset.sum_congr rfl (fun t _ => hsym _ _), h₁]
    exact hcancel _ _
  · intro j
    rw [Finset.sum_congr rfl (fun t _ => hsym _ _), h₂]
    exact ZModModule.add_self _
  · intro i
    rw [Finset.sum_congr rfl (fun t _ => hsym _ _), h₂]
    exact hcancel _ _

/--
---
conclusion: Lax342547.RecipeRows.recipe_bits
---
First construct the compatible symmetric atom matrix from the numerical
role and p data. Then realize its difference from the fixed tester matrix
using one allowed formal ordered L/R product per distinct atom pair.
-/
theorem recipe_bits {I J Term : Type} [Fintype I] [Fintype J] [Fintype Term]
    [Nonempty I] [Nonempty J]
    (a opposite p : I ⊕ J → Binary)
    (hrole₁ : (∑ i : I, a (Sum.inl i)) + (∑ i : I, opposite (Sum.inl i)) = 1)
    (hrole₂ : (∑ j : J, a (Sum.inr j)) + (∑ j : J, opposite (Sum.inr j)) = 1)
    (hcoupled : (∑ i : I, (p (Sum.inl i) + opposite (Sum.inl i))) =
      ∑ j : J, (p (Sum.inr j) + opposite (Sum.inr j)))
    (allowed : (I ⊕ J) → (I ⊕ J) → Term → Prop) (hallowed : ∀ x y, ∃ t, allowed x y t)
    (T₀ : Matrix (I ⊕ J) (I ⊕ J) Binary) (hsym : ∀ x y, T₀ x y = T₀ y x)
    (hdiag : ∀ x, T₀ x x = a x) :
    ∃ L R : (I ⊕ J) → (I ⊕ J) → Term → Binary,
      (∀ x y t, ¬ allowed x y t → L x y t = 0 ∧ R x y t = 0) ∧
      let T := fun x y => T₀ x y + productSum L R x y + productSum L R y x
      (∀ i : I, a (Sum.inl i) + ∑ t : I, T (Sum.inl t) (Sum.inl i) = 0) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : I, T (Sum.inl t) (Sum.inr j) = p (Sum.inr j)) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : J, T (Sum.inr t) (Sum.inr j) = 0) ∧
      (∀ i : I, a (Sum.inl i) + ∑ t : J, T (Sum.inr t) (Sum.inl i) = p (Sum.inl i)) := by
  obtain ⟨M, hMsym, hMdiag, hM⟩ := recipe_matrix a opposite p hrole₁ hrole₂ hcoupled
  obtain ⟨L, R, hallowed', hT⟩ := BinaryPrescriptions.realize allowed hallowed T₀ M hsym hMsym
    (fun x => (hMdiag x).trans (hdiag x).symm)
  exact ⟨L, R, hallowed', by simpa only [hT] using hM⟩

end Lax342547Proofs.RecipeRows
