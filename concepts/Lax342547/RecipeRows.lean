import Lax342547.SymmetricPrescriptions
import Lax342547.BinaryPrescriptions

/-!
---
title: Coupled scalar recipes give consistent atom gradients
type: theorem
---
At one endpoint, a and the opposite matched a-values satisfy the two
role equations. The opposite p-values satisfy the coupled equation.
These numerical data determine compatible row sums on the two lists,
and hence formal ordered product prescriptions for the desired gradients.
-/

namespace Lax342547.RecipeRows

open Lax342547.MomentSpace Lax342547.BinaryPrescriptions

axiom recipe_matrix {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
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
      (∀ i : I, a (Sum.inl i) + ∑ t : J, M (Sum.inr t) (Sum.inl i) = p (Sum.inl i))

axiom recipe_bits {I J Term : Type} [Fintype I] [Fintype J] [Fintype Term]
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
      (∀ i : I, a (Sum.inl i) + ∑ t : J, T (Sum.inr t) (Sum.inl i) = p (Sum.inl i))

end Lax342547.RecipeRows
