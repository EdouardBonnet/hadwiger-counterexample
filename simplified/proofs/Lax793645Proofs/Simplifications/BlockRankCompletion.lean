import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CrossPatternCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem inverse_from_injective {t : ℕ} (A : Mat (Fin t) (Fin t))
    (hi : Injective A.mulVec) : ∃ E : Mat (Fin t) (Fin t),A*E=1 ∧ E*A=1 := by
  let e := LinearEquiv.ofBijective A.mulVecLin
    ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩
  let E := LinearMap.toMatrix' e.symm.toLinearMap
  refine ⟨E,?_,?_⟩
  · apply coe_mv_inj
    change (A*E).mulVecLin=Matrix.mulVecLin 1
    dsimp only [E]
    rw [mulVecLin_mul,toMat_map,mulVecLin_one]
    exact LinearMap.ext (fun x=>e.apply_symm_apply x)
  · apply coe_mv_inj
    change (E*A).mulVecLin=Matrix.mulVecLin 1
    dsimp only [E]
    rw [mulVecLin_mul,toMat_map,mulVecLin_one]
    exact LinearMap.ext (fun x=>e.symm_apply_apply x)

/-- A maximum disjoint-block minor determines a low-rank completion of
all rows and columns on its border. -/
theorem rank_border_completion {I : Type} [Fintype I] [DecidableEq I]
    (M : Mat I I) {t : ℕ} (f g : Fin t→I)
    (hi : Injective (M.submatrix f g).mulVec) :
    ∃ R : Mat I I,R.rank≤t ∧ (∀ i j,M (f i) j=R (f i) j) ∧
      (∀ i j,M i (g j)=R i (g j)) := by
  obtain ⟨E,hL,hR⟩ := inverse_from_injective (M.submatrix f g) hi
  let R := M.submatrix _root_.id g * E * M.submatrix f _root_.id
  have hl : R.submatrix f _root_.id=M.submatrix f _root_.id := by
    change ((M.submatrix _root_.id g * E) * M.submatrix f _root_.id).submatrix f _root_.id=_
    rw [submatrix_mul _ _ f _root_.id _root_.id Function.bijective_id]
    rw [submatrix_mul _ _ f _root_.id _root_.id Function.bijective_id]
    simp only [submatrix_submatrix,Function.comp_id,Function.id_comp,submatrix_id_id]
    rw [hL,Matrix.one_mul]
  have hr : R.submatrix _root_.id g=M.submatrix _root_.id g := by
    change ((M.submatrix _root_.id g * E) * M.submatrix f _root_.id).submatrix _root_.id g=_
    rw [submatrix_mul _ _ _root_.id _root_.id g Function.bijective_id]
    simp only [submatrix_submatrix,Function.comp_id,Function.id_comp,submatrix_id_id]
    rw [Matrix.mul_assoc,hR,Matrix.mul_one]
  refine ⟨R,?_,fun i j=>congr_fun (congr_fun hl i) j |>.symm,
    fun i j=>congr_fun (congr_fun hr i) j |>.symm⟩
  exact (Matrix.rank_mul_le_left ..).trans
    ((Matrix.rank_mul_le_right ..).trans (by simpa using E.rank_le_card_width))

/-- A binary block matrix is a block-diagonal matrix plus a matrix of
rank at most (1+4b)t, where b is the block size and t is the maximum rank
of a rectangle between disjoint groups of blocks. The number of blocks
does not occur in this bound. -/
theorem block_rank_completion {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Avenue I J) :
    ∃ D R : Avenue I J,M=D+R ∧
      (∀ x y,x.1≠y.1→D x y=0) ∧
      R.rank≤(1+4*Fintype.card J)*peak M := by
  obtain ⟨f,g,hd,hfg⟩ := real_peak M
  obtain ⟨R0,hR0,hrow,hcol⟩ := rank_border_completion M f g hfg
  let T : Finset I := (univ.image (fun i=>(f i).1))∪(univ.image (fun i=>(g i).1))
  let U : Avenue I J := fun x y=>if x.1∈T then (M+R0) x y else 0
  let V : Avenue I J := fun x y=>if x.1∉T ∧ y.1∈T then (M+R0) x y else 0
  let R := R0+U+V
  let D := M+R
  have hT : T.card≤2*peak M := by
    calc T.card≤(univ.image (fun i=>(f i).1)).card+(univ.image (fun i=>(g i).1)).card := card_union_le ..
      _≤2*peak M := by
        have hf := card_image_le (f:=fun i=>(f i).1) (s:=univ)
        have hg := card_image_le (f:=fun i=>(g i).1) (s:=univ)
        simp only [card_univ,Fintype.card_fin] at hf hg
        omega
  have hU : U.rank≤T.card*Fintype.card J := by
    apply le_trans (U.rank_le_card_of_support_subset (T.product (univ : Finset J)) ?_)
      (by simp)
    intro x hx
    change x∈T.product (univ : Finset J)
    apply Finset.mem_product.mpr
    refine ⟨?_,mem_univ _⟩
    by_contra hn
    apply hx
    funext y
    simp [U,hn]
  have hV : V.rank≤T.card*Fintype.card J := by
    rw [←Matrix.rank_transpose V]
    apply le_trans (Vᵀ.rank_le_card_of_support_subset (T.product (univ : Finset J)) ?_)
      (by simp)
    intro x hx
    change x∈T.product (univ : Finset J)
    apply Finset.mem_product.mpr
    refine ⟨?_,mem_univ _⟩
    by_contra hn
    apply hx
    funext y
    simp [V,Matrix.transpose_apply,hn]
  refine ⟨D,R,?_,?_,?_⟩
  · change M=(M+R)+R
    rw [add_assoc,ZModModule.add_self,add_zero]
  · intro x y hxy
    by_cases hx : x.1∈T
    · simp only [D,R,U,V,hx,not_true_eq_false,false_and,if_false,if_true,Matrix.add_apply]
      ring_nf
      simp [show (2:F)=0 from by decide]
    by_cases hy : y.1∈T
    · simp only [D,R,U,V,hx,hy,not_false_eq_true,true_and,if_false,if_true,Matrix.add_apply]
      ring_nf
      simp [show (2:F)=0 from by decide]
    have hdisp : disperses (Sum.elim f (fun _ : Unit=>x))
        (Sum.elim g (fun _ : Unit=>y)) := by
      rintro (i|i) (j|j) he
      · exact hd i j he
      · apply hy
        simp only [T,mem_union,mem_image,mem_univ,true_and]
        exact Or.inl ⟨i,he⟩
      · apply hx
        simp only [T,mem_union,mem_image,mem_univ,true_and]
        exact Or.inr ⟨j,he.symm⟩
      · exact hxy he
    have he := border_same M R0 f g x y hfg hrow hcol (sized_peak M hdisp)
      ((R0.rank_submatrix_le _ _).trans hR0)
    simp only [D,R,U,V,hx,hy,not_false_eq_true,and_false,if_false,Matrix.add_apply,
      add_zero,he]
    exact ZModModule.add_self _
  · have hh := mrk_add_le (R0+U) V
    have hh' := mrk_add_le R0 U
    dsimp only [R]
    have hb : T.card*Fintype.card J≤2*peak M*Fintype.card J :=
      Nat.mul_le_mul_right _ hT
    nlinarith

private theorem matrix_rank_sum {I J A : Type} [Fintype I] [Fintype J]
    (s : Finset A) (M : A→Mat I J) :
    (∑ a∈s,M a).rank≤∑ a∈s,(M a).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (mrk_add_le _ _).trans (Nat.add_le_add_left ih _)

def maskBlockPattern {I J : Type} (P : J→J→Prop) [DecidableRel P]
    (M : Avenue I J) : Avenue I J :=
  fun x y=>if P x.2 y.2 then M x y else 0

/-- Restricting a matrix to a fixed pattern on within-block coordinates
costs at most the block size in rank. This permits keeping only the
original component and plus/minus pairs in a low-rank completion. -/
theorem mask_block_rank {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (P : J→J→Prop) [DecidableRel P]
    (M : Avenue I J) :
    (maskBlockPattern P M).rank≤Fintype.card J*M.rank := by
  let row (j : J) : Avenue I J := Matrix.diagonal (fun x=>if x.2=j then 1 else 0)
  let col (j : J) : Avenue I J := Matrix.diagonal (fun x=>if P j x.2 then 1 else 0)
  have he : maskBlockPattern P M=∑ j:J,row j*M*col j := by
    ext x y
    simp only [Matrix.sum_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,row,col]
    rw [Finset.sum_eq_single x.2]
    · simp [maskBlockPattern]
    · intro j _ hj
      simp [hj.symm]
    · simp
  rw [he]
  calc
    _≤∑ j:J,(row j*M*col j).rank := matrix_rank_sum univ _
    _≤∑ _ : J,M.rank := Finset.sum_le_sum (fun j _=>
      (Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..))
    _=Fintype.card J*M.rank := by simp

/-- The block-diagonal/low-rank decomposition may retain any fixed
allowed within-block coordinate pattern, at a constant rank cost. -/
theorem patterned_block_rank_completion {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (P : J→J→Prop) [DecidableRel P]
    (M : Avenue I J) (hM : ∀ x y,¬P x.2 y.2→M x y=0) :
    ∃ D R : Avenue I J,M=D+R ∧
      (∀ x y,x.1≠y.1→D x y=0) ∧
      (∀ x y,¬P x.2 y.2→D x y=0 ∧ R x y=0) ∧
      R.rank≤Fintype.card J*(1+4*Fintype.card J)*peak M := by
  obtain ⟨D,R,hDR,hD,hR⟩ := block_rank_completion M
  refine ⟨maskBlockPattern P D,maskBlockPattern P R,?_,?_,?_,?_⟩
  · ext x y
    by_cases hp : P x.2 y.2
    · simpa [maskBlockPattern,hp] using congr_fun (congr_fun hDR x) y
    · simp [maskBlockPattern,hp,hM x y hp]
  · intro x y hxy
    simp [maskBlockPattern,hD x y hxy]
  · intro x y hxy
    simp [maskBlockPattern,hxy]
  · exact (mask_block_rank P R).trans (by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hR)

end
end Lax793645Proofs.Simplifications
