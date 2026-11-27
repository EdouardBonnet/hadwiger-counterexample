import Lax793645.ConstructionData

/-!
---
title: Completing a Gram matrix by ordering its slots
type: lemma
---
A symmetric binary matrix is indexed by batches of $k$ slots. If the largest
rank between disjoint sets of batches is $r$, the entries between batches
have a symmetric completion of rank at most $2k(1+4k)r$. It preserves the
prescribed zero entries. The difference from the given matrix is block diagonal.
-/

namespace Lax793645.OrderedSlotCompletion
open Lax793645.ConstructionData.Binary.HadwigerCounterexample

/-- The greatest size of an invertible minor with disjoint row and column batches. -/
noncomputable def crossRank {I J : Type} (M : Mat (I × J) (I × J)) : ℕ :=
  sSup {t : ℕ | ∃ f g : Fin t → I × J,
    (∀ i j, (f i).1 ≠ (g j).1) ∧ Function.Injective (M.submatrix f g).mulVec}

open Matrix
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

axiom ordered_slot_completion (P : J → J → Prop) [DecidableRel P]
    (hP : ∀ u v, P u v → P v u) (M : Mat (I × J) (I × J))
    (hM : ∀ x y, ¬P x.2 y.2 → M x y = 0) (hs : Mᵀ = M) :
    ∃ D R : Mat (I × J) (I × J), M = D + R ∧ Dᵀ = D ∧ Rᵀ = R ∧
      (∀ x y, x.1 ≠ y.1 → D x y = 0) ∧
      (∀ x y, ¬P x.2 y.2 → D x y = 0 ∧ R x y = 0) ∧
      R.rank ≤ 2 * Fintype.card J * (1 + 4 * Fintype.card J) * crossRank M

end Lax793645.OrderedSlotCompletion
