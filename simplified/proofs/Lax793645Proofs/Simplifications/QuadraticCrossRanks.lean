import Lax793645Proofs.Simplifications.QuadraticCodeDimension
import Lax793645Proofs.Simplifications.QuadraticPairGramLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

def quadraticFrameCross (P Q : Rack I N) : Mat I I:=P.1ᵀ*Q.2+P.2ᵀ*Q.1

def quadraticFrameCrossMap (P : Rack I N) : Rack I N→ₗ[F]Mat I I where
  toFun:=quadraticFrameCross P
  map_add' Q R:=by simp only [quadraticFrameCross,Prod.fst_add,Prod.snd_add,Matrix.mul_add]; abel
  map_smul' c Q:=by simp [quadraticFrameCross,Matrix.mul_smul,smul_add]

theorem quadratic_cross_surjective (P : Rack I N)
    (hP : Injective (stackMatrixEquiv N P).mulVec) : Surjective (quadraticFrameCrossMap P) := by
  let A:=(Matrix.fromRows P.2 P.1)
  have hi : Injective A.mulVec := by
    intro x y h
    apply hP
    change (Matrix.fromRows P.2 P.1)*ᵥx=(Matrix.fromRows P.2 P.1)*ᵥy at h
    change (Matrix.fromRows P.1 P.2)*ᵥx=(Matrix.fromRows P.1 P.2)*ᵥy
    simp only [Matrix.fromRows_mulVec] at h ⊢
    apply funext
    intro i
    cases i with
    | inl i=>exact congrFun h (.inr i)
    | inr i=>exact congrFun h (.inl i)
  obtain ⟨B,hB⟩:=mat_left_inv hi
  intro M
  refine ⟨(stackMatrixEquiv N).symm (Bᵀ*M),?_⟩
  have ht : Aᵀ*Bᵀ=1 := by rw [←Matrix.transpose_mul,hB,Matrix.transpose_one]
  change quadraticFrameCross P ((stackMatrixEquiv N).symm (Bᵀ*M))=M
  have he (Q : Rack I N) : quadraticFrameCross P Q=Aᵀ*stackMatrixEquiv N Q := by
    change quadraticFrameCross P Q=(Matrix.fromRows P.2 P.1)ᵀ*Matrix.fromRows Q.1 Q.2
    rw [Matrix.transpose_fromRows,Matrix.fromCols_mul_fromRows]
    exact add_comm _ _
  rw [he,Equiv.apply_symm_apply,←Matrix.mul_assoc,ht,Matrix.one_mul]

theorem quadratic_cross_uniform (P : Rack I N)
    (hP : Injective (stackMatrixEquiv N P).mulVec) (W : Mat I I) :
    mapW unif (fun Q=>quadraticFrameCross P Q+W)=unif := by
  let E : Mat I I≃Mat I I:=⟨(·+W),(·+W),add_polar W,add_polar W⟩
  change mapW unif (E∘quadraticFrameCrossMap P)=_
  rw [←mapW_nested,map_unif_surjective _ (quadratic_cross_surjective P hP),unif_equiv]

theorem quadratic_pair_density_cap (G : Mat I I) (hN : 2*num I+2≤N) :
    ∀ Q : Rack I N,unifOn (quadraticPairGood G) Q≤
      bp ((dim (QuadraticGramCode I):ℝ)+2)*unif Q := by
  have hl:=quadratic_pair_good_lower (N:=N) G hN
  rw [unif_apply,card_space,←bp_neg,←pair_unif] at hl
  have he : bp (-(dim (QuadraticGramCode I):ℝ))/4=
      bp (-(dim (QuadraticGramCode I):ℝ)-2) := by rw [bp_sub]; norm_num [bp]
  rw [he] at hl
  intro Q
  rw [←on_unif]
  have h:=on_mon unif_law.nz (bp_pos _) hl Q
  rw [←bp_neg] at h
  convert h using 1 <;> congr 2 <;> ring

theorem quadratic_cross_rank_bound (P : Rack I N)
    (hP : Injective (stackMatrixEquiv N P).mulVec)
    (G W : Mat I I) (hN : 2*num I+2≤N) (r : ℕ) :
    pr (unifOn (quadraticPairGood G)) (fun Q=>(quadraticFrameCross P Q+W).rank≤r)≤
      bp ((dim (QuadraticGramCode I):ℝ)+2+2*num I*r-num I*num I) := by
  have hh:=pr_cap (quadratic_pair_density_cap G hN)
    (fun Q=>(quadraticFrameCross P Q+W).rank≤r)
  have he : pr unif (fun Q : Rack I N=>(quadraticFrameCross P Q+W).rank≤r)=
      pr unif (fun M : Mat I I=>M.rank≤r) := by
    rw [←quadratic_cross_uniform P hP W,mapW_pr]
  rw [he] at hh
  refine hh.trans ((mul_le_mul_of_nonneg_left (pr_matrix_rank (I:=I) (J:=I) r)
    (bp_pos _).le).trans_eq ?_)
  rw [←bp_add]
  congr 1
  ring

theorem quadratic_cross_pair_rank_bound (G H W : Mat I I)
    (hN : 2*num I+2≤N) (r : ℕ) :
    pr (pairW (unifOn (quadraticPairGood G)) (unifOn (quadraticPairGood H)))
      (fun Q : Rack I N×Rack I N=>(quadraticFrameCross Q.1 Q.2+W).rank≤r)≤
      bp ((dim (QuadraticGramCode I):ℝ)+2+2*num I*r-num I*num I) := by
  have hG : IsLaw (unifOn (quadraticPairGood G) : Wgt (Rack I N)) := by
    rw [←on_unif]
    exact on_law unif_law.nz (by simpa only [pair_unif] using quadratic_pair_good_pos G hN)
  rw [pr,pairW_avg]
  rw [←hG.avg_const (bp ((dim (QuadraticGramCode I):ℝ)+2+2*num I*r-num I*num I))]
  apply Finset.sum_le_sum
  intro P _
  by_cases hz : unifOn (quadraticPairGood G) P=0
  · simp only [hz,zero_mul,le_refl]
  have hp : quadraticPairGood G P := by
    by_contra h
    exact hz (unifOn_carried _ _ h)
  exact mul_le_mul_of_nonneg_left (quadratic_cross_rank_bound P hp.1 H W hN r) (hG.nz P)

/-- Quadratic-frame conditioning still leaves an exponentially small
binary rank failure. Only one endpoint law is paid for, after fixing the
other endpoint's injective image. -/
theorem quadratic_cross_rank_calendar :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ,2*(n:ℝ)+2≤N→
      ∀ G H W : Mat (Fin n) (Fin n),
      pr (pairW (unifOn (quadraticPairGood G)) (unifOn (quadraticPairGood H)))
        (fun Q : Rack (Fin n) N×Rack (Fin n) N=>
          5*(quadraticFrameCross Q.1 Q.2+W).rank<n)≤bp (-(n:ℝ)*n/20) := by
  filter_upwards [eventually_ge_atTop 100] with n hn N hN G H W
  let r:=n/5
  have hr : 5*(r:ℝ)≤n := by exact_mod_cast (show 5*r≤n by unfold r; omega)
  have hn' : (100:ℝ)≤n := by exact_mod_cast hn
  have hd:=quadratic_code_dimension_real (I:=Fin n)
  simp only [num,Fintype.card_fin] at hd
  have hh:=quadratic_cross_pair_rank_bound (N:=N) G H W (by simpa only [num,Fintype.card_fin] using hN) r
  refine (pr_mono (subLaw_pair (unifOn_sub _) (unifOn_sub _)).nz
    (fun Q h=>(by unfold r; omega : (quadraticFrameCross Q.1 Q.2+W).rank≤r))).trans
      (hh.trans (bp_le ?_))
  simp only [num,Fintype.card_fin]
  nlinarith [mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg n : 0≤(n:ℝ)),
    mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg n : 0≤(n:ℝ))]

end
end Lax793645Proofs.Simplifications
