import Lax342547.CoordinateCounts
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.CoordinateCounts

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

def degreeEquiv (b degree : ℕ) :
    SelectorCoordinates b degree ≃ Σ j : Fin (degree + 1), {S : Finset (Fin b) // S.card = j.val} where
  toFun S := ⟨⟨S.val.card, Nat.lt_succ_of_le S.property⟩, ⟨S.val, rfl⟩⟩
  invFun T := ⟨T.2.val, by have h := T.1.isLt; rw [T.2.property]; omega⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, hj⟩, S, hS⟩
    change S.card = j at hS
    subst j
    rfl

theorem selector_card (b degree : ℕ) :
    Fintype.card (SelectorCoordinates b degree) = ∑ j ∈ Finset.range (degree + 1), b.choose j := by
  rw [Fintype.card_congr (degreeEquiv b degree)]
  simp only [Fintype.card_sigma, Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j => b.choose j) (degree + 1)

theorem base_card (k n : ℕ) : Fintype.card (Base k n) = ((2 * k + 1) ^ 2 + 3) * n := by
  simp only [Base, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Tag, ZMod.card]
  ring

/--
---
conclusion: Lax342547.CoordinateCounts.coordinate_dimensions
---
Partition selector monomials by their degree, then count the product and
sum types indexing the ordinary, common, and constant base coordinates.
-/
theorem coordinate_dimensions (k n b degree : ℕ) :
    Fintype.card (SelectorCoordinates b degree) = ∑ j ∈ Finset.range (degree + 1), b.choose j ∧
    Fintype.card (Base k n) = ((2 * k + 1) ^ 2 + 3) * n ∧
    Fintype.card (Coordinate k n b degree) =
      (∑ j ∈ Finset.range (degree + 1), b.choose j) * (1 + ((2 * k + 1) ^ 2 + 3) * n) := by
  refine ⟨selector_card b degree, base_card k n, ?_⟩
  simp only [Coordinate, Fintype.card_prod, Fintype.card_option, selector_card, base_card]
  ring

end Lax342547Proofs.CoordinateCounts
