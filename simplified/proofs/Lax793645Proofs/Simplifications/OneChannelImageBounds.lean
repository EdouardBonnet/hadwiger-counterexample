import Lax793645Proofs.Simplifications.OnePhaseLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem product_projection_law {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
    (w : I→Wgt A) (hw : ∀ i,IsLaw (w i)) (i : I) :
    mapW (prodW w) (fun x=>x i)=w i := by
  classical
  funext a
  have he (x : I→A) : x i=a ↔ ∀ j,j=i→x j=a := by
    constructor
    · intro h j hj; simpa [hj] using h
    · intro h; exact h i rfl
  change pr (prodW w) (fun x=>x i=a)=_
  simp_rw [he]
  rw [prodW_pr w (fun j x=>j=i→x=a),Finset.prod_eq_single i]
  · simp [pr_point']
  · intro j _ hj
    simp only [hj,false_implies,pr_true,(hw j).total]
  · simp

def oneChannelRowsEquiv (p : Shape) (N : ℕ) :
    OneChannels p N≃ₗ[F]Mat (HyperbolicIdx p.h) (Fin (2*N)) :=
  ((oneChannelPairEquiv p N).trans splitChannelMatrix.symm).trans
    (Matrix.transposeLinearEquiv _ _ F F)

def oneChannelRows {p : Shape} {n N : ℕ} (P : OneFrame p n N) :
    Mat (HyperbolicIdx p.h) (Fin (2*N)) :=oneChannelRowsEquiv p N (oneChannels P)

theorem one_channel_rows_uniform (p : Shape) (N : ℕ) :
    mapW unif (oneChannelRowsEquiv p N)=unif :=
  unif_equiv (oneChannelRowsEquiv p N).toEquiv

variable {p : Shape} {n N : ℕ}

theorem one_channel_rows_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (T : Mat (HyperbolicIdx p.h) (Fin (2*N))) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm') oneChannelRows T≤oneChannelPrice p*unif T := by
  have hh:=mapW_cap (one_channels_cap m hroom hN) (oneChannelRowsEquiv p N) T
  rw [mapW_nested,one_channel_rows_uniform] at hh
  exact hh

theorem one_unit_frame_marginal (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (i : Bool) (e : Comp p.g) :
    mapW (oneUnitRaw m N) (fun x=>x i e)=
      quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' := by
  have h1:=product_projection_law (fun _ : Bool=>oneRaw m N)
    (fun _=>one_raw_law m hroom) i
  have h2:=product_projection_law
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law (quadratic_channel_frames_exist
      (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
      (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (one_frame_room hroom))) e
  have h:=mapW_nested (oneUnitRaw m N) (fun x=>x i) (fun o=>o e)
  have h1' : mapW (oneUnitRaw m N) (fun x=>x i)=oneRaw m N := by
    convert h1 using 1 <;> congr!
  rw [h1'] at h
  have h2' : mapW (oneRaw m N) (fun o=>o e)=
      quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' := by
    convert h2 using 1 <;> congr!
  convert h.symm.trans h2' using 1 <;> congr!

theorem one_unit_channel_rows_cap {w : Wgt (OneUnit p n N)} {H : ℝ}
    (hH : 0≤H) (m : Mixer p n) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (e : Comp p.g) (T : Mat (HyperbolicIdx p.h) (Fin (2*N))) :
    mapW w (fun x=>oneChannelRows (x i e)) T≤H*oneChannelPrice p*unif T := by
  have hc:=product_projection_law
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law (quadratic_channel_frames_exist
      (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
      (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (one_frame_room hroom))) e
  have hf:=mapW_cap hcap (fun o=>oneChannelRows (o e)) T
  rw [mapW_nested] at hf
  have he : mapW (oneRaw m N) (fun o=>oneChannelRows (o e)) T=
      mapW (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm') oneChannelRows T := by
    have hh:=mapW_nested (oneRaw m N) (fun o=>o e) oneChannelRows
    have hc' : mapW (oneRaw m N) (fun o=>o e)=
        quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
          (selfM p n m.mixM).toQuadraticForm' := by
      convert hc using 1 <;> congr!
    rw [hc'] at hh
    convert congrFun hh.symm T using 1 <;> congr!
  rw [he] at hf
  exact hf.trans ((mul_le_mul_of_nonneg_left (one_channel_rows_cap m hroom hN T) hH).trans_eq
    (mul_assoc _ _ _).symm)

/-- All channel evaluations on an independent ambient k-frame have the
uniform matrix point bound, up to the fixed raw-channel price. -/
theorem one_channel_test_cap {A : Type} [Fintype A] {w : Wgt A}
    (read : A→Mat (HyperbolicIdx p.h) (Fin (2*N))) {H : ℝ}
    (hcap : ∀ T,mapW w read T≤H*unif T)
    {k : ℕ} (P : Mat (Fin (2*N)) (Fin k)) (hP : Function.Injective P.mulVec)
    (T : Mat (HyperbolicIdx p.h) (Fin k)) :
    pr w (fun x=>read x*P=T)≤H*bp (-(2*(p.h:ℝ))*k) := by
  have hh:=pr_cap hcap (fun M=>M*P=T)
  rw [mapW_pr,pr_mult_mat hP] at hh
  simpa [num,HyperbolicIdx,two_mul] using hh

/-- The pin subspace may depend on the sampled unit. Rank counting
still bounds the event that all k channel evaluations lie in it. -/
theorem one_channel_rank_cap {A : Type} [Fintype A] {w : Wgt A}
    (hw : SubLaw w) (read : A→Mat (HyperbolicIdx p.h) (Fin (2*N))) {H : ℝ}
    (hcap : ∀ T,mapW w read T≤H*unif T)
    {k : ℕ} (P : Mat (Fin (2*N)) (Fin k)) (hP : Function.Injective P.mulVec)
    (K : ℕ) :
    pr w (fun x=>(read x*P).rank≤K)≤
      H*bp ((2*(p.h:ℝ)+k)*K-2*(p.h:ℝ)*k) := by
  classical
  let S:={T : Mat (HyperbolicIdx p.h) (Fin k)//T.rank≤K}
  have he (x) (hx : (read x*P).rank≤K) : ∃ T : S,read x*P=T.val:=⟨⟨_,hx⟩,rfl⟩
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz _)).trans ?_
  refine (Finset.sum_le_sum fun T _=>one_channel_test_cap read hcap P hP T.val).trans ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hn : (Fintype.card S:ℝ)≤bp ((2*(p.h:ℝ)+k)*K) := by
    rw [←nbr_eq_card]
    simpa [num,HyperbolicIdx,two_mul] using
      (nbr_matrix_rank (I:=HyperbolicIdx p.h) (J:=Fin k) K)
  have hH : 0≤H := by
    have hh:= (pr_nonneg hw.nz).trans (hcap 0)
    exact nonneg_of_mul_nonneg_left hh (by simp only [unif_apply]; positivity)
  calc
    _ ≤ bp ((2*(p.h:ℝ)+k)*K)*(H*bp (-(2*(p.h:ℝ))*k)) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg hH (bp_pos _).le)
    _ = _ := by rw [mul_left_comm,←bp_add]; congr 2 <;> ring

end
end Lax793645Proofs.Simplifications
