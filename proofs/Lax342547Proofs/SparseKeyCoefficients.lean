import Lax342547.SparseKeyCoefficients
import Lax342547Proofs.QuotientExtractors

namespace Lax342547Proofs.SparseKeyCoefficients

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.PinLabelExclusions Lax342547.SparsePins

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.SparseKeyCoefficients.coefficients_zero
---
Adjoin the at most fourteen key labels to the sparse support and extract
each fresh key coefficient through the pin quotient. The unselected
support contributes zero, and list injectivity isolates the tested key.
-/
theorem coefficients_zero {Base Comp H N I : Type} [Fintype I] {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (v : (Fin b → Binary) → Option Base → Binary)
    (label : I → Fin b → Binary) (hlabel : Function.Injective label)
    (base : I → Option Base → Binary) (hcard : Fintype.card I ≤ 14)
    (hfresh : ∀ j, label j ∉ A i)
    (hdisjoint : Disjoint L (Finset.univ.image label)) (c : I → Binary)
    (h : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) -
      (∑ j, c j • labelTensor (selectorEval (degree := degree)) (label j) (base j)) ∈ projected P i a) :
    ∀ j, c j • base j = 0 := by
  classical
  intro j
  let J := Finset.univ.image label
  have hJ : J.card ≤ 14 := Finset.card_image_le.trans (by simpa using hcard)
  have hsize : (L ∪ J).card ≤ R + 14 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hL hJ)
  have hj : label j ∈ J := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hq⟩ := QuotientExtractors.pin_extractor P A hA i a (L ∪ J) hsize
    (label j) (Finset.mem_union_right _ hj) (hfresh j)
  let f := q.comp (projected P i a).mkQ
  have hf (s : Fin b → Binary) (hs : s ∈ L ∪ J) (w : Option Base → Binary) :
      f (labelTensor (selectorEval (degree := degree)) s w) = if s = label j then w else 0 :=
    hq s hs w
  have hleft : f (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro s hs
    rw [hf s (Finset.mem_union_left _ hs)]
    have hne : s ≠ label j := by
      intro heq
      subst s
      exact Finset.disjoint_left.mp hdisjoint hs hj
    simp [hne]
  have hright : f (∑ t, c t • labelTensor (selectorEval (degree := degree)) (label t) (base t)) =
      c j • base j := by
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single j]
    · rw [hf _ (Finset.mem_union_right _ hj)]
      simp
    · intro t _ htj
      have ht : label t ∈ J := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
      rw [hf _ (Finset.mem_union_right _ ht)]
      have hne : label t ≠ label j := fun heq => htj (hlabel heq)
      simp [hne]
    · simp
  have hz : f ((∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) -
      (∑ t, c t • labelTensor (selectorEval (degree := degree)) (label t) (base t))) = 0 := by
    have hzero : (projected P i a).mkQ
        ((∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) -
          (∑ t, c t • labelTensor (selectorEval (degree := degree)) (label t) (base t))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h
    change q ((projected P i a).mkQ _) = 0
    rw [hzero, map_zero]
  rw [map_sub, hleft, hright, zero_sub, neg_eq_zero] at hz
  exact hz

end Lax342547Proofs.SparseKeyCoefficients
