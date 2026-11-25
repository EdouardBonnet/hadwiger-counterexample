import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
Explicit shifted diagonals for the proposed binary mixer. These results are
independent of the random construction. The full mixer interface is a separate
obligation: in particular, its protected Z block must be preserved.
-/
namespace Lax793645Proofs.Simplifications
open Matrix
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- The matrix with coefficient `a k` on its kth upper diagonal. -/
def shiftCombination (d : ℕ) (a : ℕ → K) : Matrix (Fin d) (Fin d) K :=
  fun i j => if i.val ≤ j.val then a (j.val - i.val) else 0

/-- A nonzero first diagonal gives an invertible square minor of size `d-k`. -/
theorem shiftCombination_rank (d k : ℕ) (a : ℕ → K)
    (hk : a k ≠ 0) (hlow : ∀ j < k, a j = 0) :
    d - k ≤ (shiftCombination d a).rank := by
  by_cases hkd : k ≤ d
  · let row : Fin (d-k) → Fin d := fun i => ⟨i.val, by omega⟩
    let col : Fin (d-k) → Fin d := fun i => ⟨i.val+k, by omega⟩
    let B := (shiftCombination d a).submatrix row col
    have htri : B.IsUpperTriangular := by
      intro i j hij
      change (if (row i).val ≤ (col j).val then
        a ((col j).val - (row i).val) else 0) = 0
      split_ifs with h
      · apply hlow
        change j.val < i.val at hij
        dsimp [row, col] at *
        omega
      · rfl
    have hdiag (i : Fin (d-k)) : B i i = a k := by
      simp [B, Matrix.submatrix, shiftCombination, row, col]
    have hr : B.rank = d-k := by
      have hd : B.det ≠ 0 := by
        rw [Matrix.det_of_isUpperTriangular htri]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => by rw [hdiag]; exact hk)
      simpa using Matrix.rank_of_det_ne_zero hd
    rw [← hr]
    exact Matrix.rank_submatrix_le _ _ _
  · have : d-k = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [this]
    exact Nat.zero_le _

/-- The degree bound alone gives the advertised rank loss. -/
theorem shiftCombination_rank_of_nonzero (d R : ℕ) (a : ℕ → K)
    (ha : ∃ k ≤ R, a k ≠ 0) :
    d-R ≤ (shiftCombination d a).rank := by
  classical
  have hex : ∃ k, a k ≠ 0 := by obtain ⟨k, _, hk⟩ := ha; exact ⟨k, hk⟩
  let k := Nat.find hex
  have hk : a k ≠ 0 := Nat.find_spec hex
  have hlo : ∀ j < k, a j = 0 := by
    intro j hj
    by_contra hn
    have := Nat.find_min' hex hn
    omega
  have hkR : k ≤ R := by
    obtain ⟨j, hj, hne⟩ := ha
    exact (Nat.find_min' hex hne).trans hj
  exact (Nat.sub_le_sub_left hkR d).trans (shiftCombination_rank d k a hk hlo)

/-- Placing a matrix in the forward half block cannot decrease its rank. -/
theorem forward_block_rank {d : ℕ} (P Q : Matrix (Fin d) (Fin d) K) :
    P.rank ≤ (Matrix.fromBlocks 0 P Q.transpose 0).rank := by
  have h := Matrix.rank_submatrix_le (Matrix.fromBlocks 0 P Q.transpose 0)
    (Sum.inl : Fin d → Fin d ⊕ Fin d) (Sum.inr : Fin d → Fin d ⊕ Fin d)
  exact h

/-- The numerical margin needed by the proposed mixer. -/
theorem shift_rank_fifth {n R : ℕ} (h : 4*R+4 ≤ n) :
    n ≤ 5*(n/2-R) := by omega

/-- Literal kth shifted diagonal; this is usable as an explicit mixer matrix
without first introducing matrix polynomials. -/
def shiftedDiagonal (d k : ℕ) : Matrix (Fin d) (Fin d) K :=
  fun i j => if i.val+k=j.val then 1 else 0

theorem diagonal_sum_eq (d R : ℕ) (a : Fin R → K) :
    (∑ k : Fin R, a k • shiftedDiagonal d k.val) =
      shiftCombination d (fun k => if hk : k < R then a ⟨k,hk⟩ else 0) := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, shiftedDiagonal, shiftCombination,
    smul_eq_mul]
  by_cases hij : i.val ≤ j.val
  · rw [if_pos hij]
    by_cases hk : j.val-i.val < R
    · rw [dif_pos hk]
      rw [Finset.sum_eq_single ⟨j.val-i.val,hk⟩]
      · simp [Nat.add_sub_of_le hij]
      · intro k _ hne
        have h : i.val+k.val ≠ j.val := by
          intro he
          apply hne
          apply Fin.ext
          change k.val = j.val-i.val
          omega
        simp [h]
      · simp
    · rw [dif_neg hk]
      apply Finset.sum_eq_zero
      intro k _
      have h : i.val+k.val ≠ j.val := by omega
      simp [h]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    have h : i.val+k.val ≠ j.val := by omega
    simp [h]

theorem diagonal_sum_rank (d R : ℕ) (a : Fin R → K) (ha : a ≠ 0) :
    d-(R-1) ≤ (∑ k : Fin R, a k • shiftedDiagonal (K:=K) d k.val).rank := by
  classical
  rw [diagonal_sum_eq]
  apply shiftCombination_rank_of_nonzero
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    ext i
    simpa using not_not.mp (show ¬a i ≠ 0 from fun hi => h ⟨i,hi⟩)
  refine ⟨i.val, by omega, ?_⟩
  simpa [i.isLt] using hi

theorem reverse_block_rank {d : ℕ} (P Q : Matrix (Fin d) (Fin d) K) :
    Q.rank ≤ (Matrix.fromBlocks 0 P Q.transpose 0).rank := by
  have h := Matrix.rank_submatrix_le (Matrix.fromBlocks 0 P Q.transpose 0)
    (Sum.inr : Fin d → Fin d ⊕ Fin d) (Sum.inl : Fin d → Fin d ⊕ Fin d)
  change Q.transpose.rank ≤ _ at h
  simpa using h

/-- Every nonzero parity of forward and reverse explicit diagonals has large
rank. Disjoint exponent ranges for indexed and label coefficients can therefore
be checked purely as a coefficient-vector statement. -/
theorem bidirectional_diagonal_rank (d R : ℕ) (a b : Fin R → K)
    (h : a ≠ 0 ∨ b ≠ 0) :
    d-(R-1) ≤ (Matrix.fromBlocks 0
      (∑ k : Fin R, a k • shiftedDiagonal (K:=K) d k.val)
      (∑ k : Fin R, b k • shiftedDiagonal (K:=K) d k.val).transpose 0).rank := by
  rcases h with ha | hb
  · exact (diagonal_sum_rank d R a ha).trans (forward_block_rank _ _)
  · exact (diagonal_sum_rank d R b hb).trans (reverse_block_rank _ _)

/-- Indexed coefficients and label-difference coefficients use disjoint ranges. -/
def mixerCoefficients {r b : ℕ} (a : Fin r → ZMod 2) (β : ZMod 2)
    (s t : Fin b → ZMod 2) : Fin (r+b) → ZMod 2 :=
  Fin.addCases a (fun ρ => β*(s ρ+t ρ))

theorem mixerCoefficients_nonzero {r b : ℕ} (a : Fin r → ZMod 2) (β : ZMod 2)
    (s t : Fin b → ZMod 2) (hst : s ≠ t) (h : a ≠ 0 ∨ β ≠ 0) :
    mixerCoefficients a β s t ≠ 0 := by
  intro hz
  have ha : a=0 := by
    funext i
    have he := congr_fun hz (Fin.castAdd b i)
    simpa [mixerCoefficients] using he
  have hβ : β ≠ 0 := h.resolve_left (not_not.mpr ha)
  apply hst
  funext ρ
  have he := congr_fun hz (Fin.natAdd r ρ)
  have hp : β*(s ρ+t ρ)=0 := by simpa [mixerCoefficients] using he
  have hs : s ρ+t ρ=0 := (mul_eq_zero.mp hp).resolve_left hβ
  have := add_eq_zero_iff_eq_neg.mp hs
  simpa [CharTwo.neg_eq] using this

/-- The explicit binary parity argument, including noncancellation of indexed
and label terms, is entirely deterministic. -/
theorem explicit_binary_rank {r b : ℕ} (d : ℕ)
    (a a' : Fin r → ZMod 2) (β β' : ZMod 2) (s t : Fin b → ZMod 2)
    (hst : s ≠ t) (h : a ≠ 0 ∨ a' ≠ 0 ∨ β ≠ 0 ∨ β' ≠ 0) :
    let c := mixerCoefficients a β s t
    let c' := mixerCoefficients a' β' s t
    d-(r+b-1) ≤ (Matrix.fromBlocks 0
      (∑ k : Fin (r+b), c k • shiftedDiagonal (K:=ZMod 2) d k.val)
      (∑ k : Fin (r+b), c' k • shiftedDiagonal (K:=ZMod 2) d k.val).transpose 0).rank := by
  apply bidirectional_diagonal_rank
  rcases h with ha | ha' | hβ | hβ'
  · exact Or.inl (mixerCoefficients_nonzero a β s t hst (Or.inl ha))
  · exact Or.inr (mixerCoefficients_nonzero a' β' s t hst (Or.inl ha'))
  · exact Or.inl (mixerCoefficients_nonzero a β s t hst (Or.inr hβ))
  · exact Or.inr (mixerCoefficients_nonzero a' β' s t hst (Or.inr hβ'))

end
end Lax793645Proofs.Simplifications
