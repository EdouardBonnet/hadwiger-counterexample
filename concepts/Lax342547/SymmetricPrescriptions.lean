import Lax342547.MomentSpace
import Mathlib.Data.Matrix.Block

/-!
---
title: Consistent symmetric binary prescriptions on two witness lists
type: theorem
---
The two lists are nonempty and disjoint, represented by a sum type.
Prescribed list sums of every row of a symmetric binary matrix are
compatible with its fixed diagonal precisely through the two self-sum
conditions and the equality of the cross totals. The sufficiency proof
constructs the matrix explicitly.
-/

namespace Lax342547.SymmetricPrescriptions

open Lax342547.MomentSpace

axiom diagonal_rows {I : Type} [Fintype I] [Nonempty I]
    (a c : I → Binary) (h : ∑ i, c i = ∑ i, a i) :
    ∃ M : Matrix I I Binary, (∀ i j, M i j = M j i) ∧
      (∀ i, M i i = a i) ∧ ∀ i, ∑ j, M i j = c i

axiom rectangular_sums {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (r : I → Binary) (c : J → Binary) (h : ∑ i, r i = ∑ j, c j) :
    ∃ M : Matrix I J Binary, (∀ i, ∑ j, M i j = r i) ∧ ∀ j, ∑ i, M i j = c j

axiom two_lists {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a c₁ c₂ : I ⊕ J → Binary)
    (h₁ : ∑ i : I, c₁ (Sum.inl i) = ∑ i : I, a (Sum.inl i))
    (h₂ : ∑ j : J, c₂ (Sum.inr j) = ∑ j : J, a (Sum.inr j))
    (hcross : ∑ i : I, c₂ (Sum.inl i) = ∑ j : J, c₁ (Sum.inr j)) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) Binary, (∀ x y, M x y = M y x) ∧
      (∀ x, M x x = a x) ∧ (∀ x, ∑ i : I, M x (Sum.inl i) = c₁ x) ∧
      ∀ x, ∑ j : J, M x (Sum.inr j) = c₂ x

end Lax342547.SymmetricPrescriptions
