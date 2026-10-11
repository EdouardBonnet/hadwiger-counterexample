import Lax342547.HadamardRank
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Lax342547.RankFactors
import Lax342547.RankedProjection

namespace Lax342547Proofs.HadamardRank
open Lax342547.HadamardRank

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace
open scoped BigOperators Matrix

/--
---
conclusion: Lax342547.HadamardRank.hadamard_rank
---
-/
theorem hadamard_rank {I J : Type} [Fintype I] [Fintype J]
    (A B : Matrix I J Binary) : (A ⊙ B).rank ≤ A.rank*B.rank := by
  classical
  obtain ⟨U,V,hA,_,_⟩ := Lax342547.RankFactors.independent_rank_factors A
  obtain ⟨X,Y,hB,_,_⟩ := Lax342547.RankFactors.independent_rank_factors B
  let P : Matrix I (Fin A.rank × Fin B.rank) Binary := fun i uv => U i uv.1*X i uv.2
  let Q : Matrix J (Fin A.rank × Fin B.rank) Binary := fun j uv => V j uv.1*Y j uv.2
  have he : A ⊙ B = P*Q.transpose := by
    ext i j
    change A i j*B i j = _
    rw [← congrFun (congrFun hA i) j,← congrFun (congrFun hB i) j]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,P,Q]
    rw [Fintype.sum_prod_type,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left P Q.transpose).trans (by simpa using Matrix.rank_le_card_width P)

/--
---
conclusion: Lax342547.HadamardRank.all_one_rank
---
-/
theorem all_one_rank {I J : Type} [Fintype I] [Fintype J] :
    (Matrix.of (fun _ : I => fun _ : J => (1 : Binary))).rank ≤ 1 := by
  let P : Matrix I (Fin 1) Binary := fun _ _ => 1
  let Q : Matrix (Fin 1) J Binary := fun _ _ => 1
  have he : (Matrix.of (fun _ : I => fun _ : J => (1 : Binary))) = P*Q := by
    ext i j
    simp [Matrix.mul_apply,P,Q]
  rw [he]
  exact (Matrix.rank_mul_le_left P Q).trans (by simpa using Matrix.rank_le_card_width P)

/--
---
conclusion: Lax342547.HadamardRank.one_add_rank
---
-/
theorem one_add_rank {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J Binary) :
    ((Matrix.of (fun _ : I => fun _ : J => (1 : Binary)))+A).rank ≤ 1+A.rank := by
  let O : Matrix I J Binary := fun _ _ => 1
  have hh := Lax342547.RankedProjection.linear_add_rank O.mulVecLin A.mulVecLin
  rw [← Matrix.mulVecLin_add] at hh
  exact hh.trans (Nat.add_le_add_right Lax342547.HadamardRank.all_one_rank A.rank)

/--
---
conclusion: Lax342547.HadamardRank.incompatible_tuple_bound
---
-/
theorem incompatible_tuple_bound {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (F : Matrix Ω Ω Binary) (x : ι → Ω) (hdiag : ∀ a, F a a = 0)
    (hinc : ∀ i j, i ≠ j → ¬ (F (x i) (x j) = 0 ∧ F (x j) (x i) = 0)) :
    Fintype.card ι ≤ (1+F.rank)^2 := by
  let A := F.submatrix x x
  let O : Matrix ι ι Binary := fun _ _ => 1
  have he : (O+A) ⊙ (O+A).transpose = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.hadamard_apply,A,O,hdiag]
    · have hx := hinc i j hij
      have hh : (1+F (x i) (x j))*(1+F (x j) (x i)) = 0 := by
        generalize F (x i) (x j) = a at hx ⊢
        generalize F (x j) (x i) = b at hx ⊢
        fin_cases a <;> fin_cases b <;> simp_all [show (1+1 : Binary) = 0 from rfl]
      simpa [Matrix.hadamard_apply,A,O,Matrix.one_apply,hij] using hh
  have hr := Lax342547.HadamardRank.hadamard_rank (O+A) (O+A).transpose
  rw [he,Matrix.rank_one,Matrix.rank_transpose] at hr
  have ha : (O+A).rank ≤ 1+F.rank :=
    (Lax342547.HadamardRank.one_add_rank A).trans (Nat.add_le_add_left (Matrix.rank_submatrix_le F x x) 1)
  exact hr.trans (by simpa only [pow_two] using Nat.mul_self_le_mul_self ha)

/--
---
conclusion: Lax342547.HadamardRank.compatible_pair_in_tuple
---
-/
theorem compatible_pair_in_tuple {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (F : Matrix Ω Ω Binary) (x : ι → Ω) (hdiag : ∀ a, F a a = 0)
    (hsize : (1+F.rank)^2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ F (x i) (x j) = 0 ∧ F (x j) (x i) = 0 := by
  by_contra hn
  have hinc : ∀ i j, i ≠ j → ¬ (F (x i) (x j) = 0 ∧ F (x j) (x i) = 0) := by
    intro i j hij hh
    exact hn ⟨i,j,hij,hh⟩
  have hc := Lax342547.HadamardRank.incompatible_tuple_bound F x hdiag hinc
  omega

end Lax342547Proofs.HadamardRank
