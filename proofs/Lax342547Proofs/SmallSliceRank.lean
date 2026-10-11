import Lax342547.SmallSliceRank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Lax342547.RankedProjection

namespace Lax342547Proofs.SmallSliceRank
open Lax342547.SmallSliceRank
open Lax342547.MomentSpace
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.SmallSliceRank.independent_column_selection
---
-/
theorem independent_column_selection {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (t : ℕ) (ht : t ≤ A.rank) :
    ∃ c : Fin t → J,Function.Injective c ∧ (A.submatrix id c).rank = t := by
  classical
  have h := Submodule.exists_fun_fin_finrank_span_eq Binary (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols] at h
  obtain ⟨f,hf,_,hli⟩ := h
  choose c hc using hf
  have hl : LinearIndependent Binary (fun i => A.col (c i)) := by simpa only [hc] using hli
  let d : Fin t → J := fun i => c (Fin.castLE ht i)
  have hd : LinearIndependent Binary (fun i => A.col (d i)) :=
    hl.comp (Fin.castLE ht) (Fin.castLE_injective ht)
  refine ⟨d,?_,?_⟩
  · intro i j he
    apply hd.injective
    exact congrArg A.col he
  · rw [Matrix.rank_eq_finrank_span_cols]
    have he : (A.submatrix id d).col = (fun i => A.col (d i)) := rfl
    rw [he,finrank_span_eq_card hd,Fintype.card_fin]

/--
---
conclusion: Lax342547.SmallSliceRank.rank_witness
---
-/
theorem rank_witness {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (t : ℕ) (ht : t ≤ A.rank) :
    ∃ r : Fin t → I,∃ c : Fin t → J,
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).rank = t := by
  obtain ⟨c,hc,hr⟩ := Lax342547.SmallSliceRank.independent_column_selection A t ht
  obtain ⟨r,hi,hh⟩ := Lax342547.SmallSliceRank.independent_column_selection (A.submatrix id c).transpose t (by rw [Matrix.rank_transpose,hr])
  refine ⟨r,c,hi,hc,?_⟩
  have he : (A.submatrix r c).transpose = (A.submatrix id c).transpose.submatrix id r := rfl
  rw [← Matrix.rank_transpose,he,hh]

/--
---
conclusion: Lax342547.SmallSliceRank.rank_le_of_small_slices
---
-/
theorem rank_le_of_small_slices {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (r : ℕ)
    (h : ∀ i : Fin (r+1) → I,∀ j : Fin (r+1) → J,
      Function.Injective i → Function.Injective j → (A.submatrix i j).rank ≤ r) : A.rank ≤ r := by
  by_contra hh
  obtain ⟨i,j,hi,hj,hr⟩ := Lax342547.SmallSliceRank.rank_witness A (r+1) (by omega)
  have := h i j hi hj
  omega



/--
---
conclusion: Lax342547.SmallSliceRank.cross_affine_product
---
-/
theorem cross_affine_product {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (c d : Binary) (a u : I → Binary) (b v : J → Binary) :
    crossCoefficients (fun x y => affineValue c a b x y*affineValue d u v x y) =
      Matrix.vecMulVec a v+Matrix.vecMulVec u b := by
  ext i j
  simp only [crossCoefficients,affineValue,dotProduct_single,dotProduct_zero,
    Matrix.add_apply,Matrix.vecMulVec_apply]
  ring_nf
  simp only [show (2 : Binary) = 0 from rfl,show (4 : Binary) = 0 from rfl,mul_zero,zero_add,add_zero]

 theorem matrix_sum_rank {P I J : Type} [Fintype P] [Fintype I] [Fintype J]
    (M : P → Matrix I J Binary) : (∑ p,M p).rank ≤ ∑ p,(M p).rank := by
  have hh := Lax342547.RankedProjection.linear_sum_rank (fun p => (M p).mulVecLin)
  have he : (∑ p,M p).mulVecLin = ∑ p,(M p).mulVecLin := by
    ext x i
    simp only [Matrix.mulVecLin_apply,LinearMap.sum_apply,Matrix.sum_apply,Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.sum_apply]
    rw [Finset.sum_comm]
  rw [← he] at hh
  exact hh

 theorem cross_sum {P I J : Type} [Fintype P] [DecidableEq I] [DecidableEq J]
    (F : P → (I → Binary) → (J → Binary) → Binary) :
    crossCoefficients (fun x y => ∑ p,F p x y) = ∑ p,crossCoefficients (F p) := by
  ext i j
  simp only [Matrix.sum_apply,crossCoefficients,← Finset.sum_add_distrib]

/--
---
conclusion: Lax342547.SmallSliceRank.cross_products_rank
---
-/
theorem cross_products_rank {P I J : Type} [Fintype P] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (c d : P → Binary) (a u : P → I → Binary)
    (b v : P → J → Binary) :
    (crossCoefficients (fun x y => ∑ p,affineValue (c p) (a p) (b p) x y*
      affineValue (d p) (u p) (v p) x y)).rank ≤ 2*Fintype.card P := by
  rw [cross_sum]
  apply (matrix_sum_rank _).trans
  calc
    (∑ p,(crossCoefficients (fun x y => affineValue (c p) (a p) (b p) x y*
      affineValue (d p) (u p) (v p) x y)).rank) ≤ ∑ p,2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [Lax342547.SmallSliceRank.cross_affine_product]
      have hh := Lax342547.RankedProjection.linear_add_rank (Matrix.vecMulVec (a p) (v p)).mulVecLin
        (Matrix.vecMulVec (u p) (b p)).mulVecLin
      rw [← Matrix.mulVecLin_add] at hh
      have ha := Matrix.rank_vecMulVec_le (a p) (v p)
      have hb := Matrix.rank_vecMulVec_le (u p) (b p)
      change (Matrix.vecMulVec (a p) (v p)+Matrix.vecMulVec (u p) (b p)).rank ≤
        (Matrix.vecMulVec (a p) (v p)).rank+(Matrix.vecMulVec (u p) (b p)).rank at hh
      exact hh.trans (by omega)
    _ = _ := by simp [Nat.mul_comm]


 theorem lift_zero {T I : Type} [Fintype T] [DecidableEq I] (r : T → I) :
    liftCoordinates r (0 : T → Binary) = 0 := by simp [liftCoordinates]

 theorem lift_basis {T I : Type} [Fintype T] [DecidableEq T] [DecidableEq I]
    (r : T → I) (t : T) : liftCoordinates r (Pi.single t 1) = Pi.single (r t) 1 := by
  unfold liftCoordinates
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu
    simp [hu]
  · simp

 theorem cross_slice {T U I J : Type} [Fintype T] [Fintype U]
    [DecidableEq T] [DecidableEq U] [DecidableEq I] [DecidableEq J]
    (F : (I → Binary) → (J → Binary) → Binary) (r : T → I) (c : U → J) :
    crossCoefficients (fun x y => F (liftCoordinates r x) (liftCoordinates c y)) =
      (crossCoefficients F).submatrix r c := by
  ext i j
  simp only [crossCoefficients,lift_basis,lift_zero,Matrix.submatrix_apply]

/--
---
conclusion: Lax342547.SmallSliceRank.cross_rank_of_products
---
-/
theorem cross_rank_of_products {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : ℕ) (F : (I → Binary) → (J → Binary) → Binary)
    (h : HasProducts s F) : (crossCoefficients F).rank ≤ 2*s := by
  obtain ⟨c,d,a,u,b,v,he⟩ := h
  have hf : F = (fun x y => ∑ p,affineValue (c p) (a p) (b p) x y*affineValue (d p) (u p) (v p) x y) :=
    funext (fun x => funext (he x))
  rw [hf]
  simpa only [Fintype.card_fin] using Lax342547.SmallSliceRank.cross_products_rank c d a u b v

/--
---
conclusion: Lax342547.SmallSliceRank.rank_from_local_products
---
-/
theorem rank_from_local_products {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : ℕ) (F : (I → Binary) → (J → Binary) → Binary)
    (h : ∀ r : Fin (2*s+1) → I,∀ c : Fin (2*s+1) → J,
      Function.Injective r → Function.Injective c →
      HasProducts s (fun x y => F (liftCoordinates r x) (liftCoordinates c y))) :
    (crossCoefficients F).rank ≤ 2*s := by
  apply Lax342547.SmallSliceRank.rank_le_of_small_slices
  intro r c hr hc
  rw [← cross_slice]
  exact Lax342547.SmallSliceRank.cross_rank_of_products s _ (h r c hr hc)

 theorem cross_dotProduct {I : Type} [Fintype I] [DecidableEq I] :
    crossCoefficients (fun x y : I → Binary => dotProduct x y) = 1 := by
  ext i j
  simp [crossCoefficients,dotProduct_single,Matrix.one_apply,Pi.single_apply,eq_comm]

/--
---
conclusion: Lax342547.SmallSliceRank.parity_rank_contradiction
---
-/
theorem parity_rank_contradiction {T : Type} [Fintype T] (s m : ℕ)
    (F : T → (Fin m → Binary) → (Fin m → Binary) → Binary)
    (hparity : ∀ x y,(∑ l,F l x y) = dotProduct x y)
    (hloc : ∀ l : T,∀ r : Fin (2*s+1) → Fin m,∀ c : Fin (2*s+1) → Fin m,
      Function.Injective r → Function.Injective c →
      HasProducts s (fun x y => F l (liftCoordinates r x) (liftCoordinates c y)))
    (hm : 2*s*Fintype.card T < m) : False := by
  have he : (∑ l,crossCoefficients (F l)) = (1 : Matrix (Fin m) (Fin m) Binary) := by
    rw [← cross_sum]
    have hf : (fun x y => ∑ l,F l x y) = (fun x y => dotProduct x y) := funext (fun x => funext (hparity x))
    rw [hf,cross_dotProduct]
  have hh := matrix_sum_rank (fun l => crossCoefficients (F l))
  rw [he,Matrix.rank_one,Fintype.card_fin] at hh
  have hb : (∑ l,(crossCoefficients (F l)).rank) ≤ 2*s*Fintype.card T := by
    calc
      _ ≤ ∑ _ : T,2*s := Finset.sum_le_sum (fun l _ => Lax342547.SmallSliceRank.rank_from_local_products s (F l) (hloc l))
      _ = _ := by simp [Nat.mul_comm]
  omega

end Lax342547Proofs.SmallSliceRank
