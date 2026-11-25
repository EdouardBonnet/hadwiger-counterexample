import Lax793645Proofs.Simplifications.OneEndpointPins

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneUnitRaw (m : Mixer p n) (N : ℕ) : Wgt (OneUnit p n N) :=
  prodW (fun _ : Bool=>oneRaw m N)

theorem one_unit_raw_law (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+1≤N) : IsLaw (oneUnitRaw m N) :=
  prodW_law (fun _=>one_raw_law m hN)

theorem one_full_dimension : dim (OneFull p n)=Fintype.card (Row p n)+2*p.h := by
  simp [dim,OneFull,QuadraticFull,Ray,Module.finrank_prod,Module.finrank_pi_fintype]
  omega

/-- At nonzero rank the fixed quadratic-Gram normalization is absorbed
by the rank itself. Rank-zero pins cost exactly no probability. -/
theorem one_frame_pin_fee (m : Mixer p n) (P : Space (OneFull p n))
    (T : OneFrame p n N) {δ : ℝ}
    (hN : 2*dim (OneFull p n)+3≤N)
    (hδ : (dim (OneFull p n):ℝ)+2≤δ*(2*N)) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm') (fun g=>∀ v∈P,g v=T v)≤
      fee (2*N) δ (dim P) := by
  have hdim : dim P≤dim (OneFull p n):=Submodule.finrank_le _
  have hroom : Fintype.card (Row p n)+2*p.h+1≤N:=by
    rw [one_full_dimension] at hN
    omega
  by_cases hz : dim P=0
  · simp only [hz,fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    have hl:=quadratic_channel_raw_law (hyperbolicMatrix N).toQuadraticForm'
      (hyperbolic_matrix_nondegenerate N) (selfM p n m.mixM).toQuadraticForm'
      (C:=Vec (Fin p.h)) (one_frame_room hroom)
    exact (pr_le_tot hl.nz).trans_eq hl.total
  · have hNP : 2*dim P+3≤N:=
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdim) 3).trans hN
    apply (one_frame_pin_cap m P T hroom hNP).trans
    apply bp_le
    have hp : (1:ℝ)≤dim P:=by exact_mod_cast (show 1≤dim P by omega)
    have hd : (dim P:ℝ)≤dim (OneFull p n):=by exact_mod_cast hdim
    have hmul:=mul_le_mul_of_nonneg_right hδ (show (0:ℝ)≤dim P by positivity)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hd (show (0:ℝ)≤dim P by positivity)]

/-- Actual raw-image cap for the six-block closed pins used in peeling.
The exponent uses the full ambient dimension 2N. -/
theorem one_closed_pin_cap (m : Mixer p n)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp) {δ : ℝ} (hd : δ≤1)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hδ : (dim (OneFull p n):ℝ)+2≤δ*(2*N)) :
    pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
      fee (2*N) δ (imagePlanRank a.sp) := by
  classical
  let S (i : Bool) (e : Comp p.g):=(a.sp e).map (oneEndpointProjection i)
  let event (i : Bool) (e : Comp p.g) (g : OneFrame p n N):=
    ∀ v∈S i e,g v=oneEndpointTarget (a.target e) i v
  have hnn : ∀ x,0≤oneUnitRaw m N x:=prodW_nonneg (fun _=>one_raw_nonneg m)
  have hprod : pr (oneUnitRaw m N) (fun x=>∀ i e,event i e (x i e))=
      ∏ i,∏ e,pr (quadraticChannelRaw (C:=Vec (Fin p.h))
        (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm') (event i e) := by
    rw [oneUnitRaw,prodW_pr (fun _ : Bool=>oneRaw m N) (fun i x=>∀ e,event i e (x e))]
    apply Finset.prod_congr rfl
    intro i _
    exact prodW_pr _ (event i)
  have hbound : pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
      ∏ i,∏ e,fee (2*N) δ (dim (S i e)) := by
    have hm : pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
        pr (oneUnitRaw m N) (fun x=>∀ i e,event i e (x i e)):=
      pr_mono hnn (fun x hx i e v hv=>one_closed_pin_endpoint a ha x hx i e hv)
    apply hm.trans
    rw [hprod]
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg (fun e _=>pr_nonneg (unifOn_sub _).nz)
    · intro i _
      exact Finset.prod_le_prod (fun e _=>pr_nonneg (unifOn_sub _).nz)
        (fun e _=>one_frame_pin_fee m (S i e) _ hN hδ)
  have hprodfee : (∏ i,∏ e,fee (2*N) δ (dim (S i e)))=
      fee (2*N) δ (∑ i,∑ e,dim (S i e)) := by
    unfold fee
    simp only [←bp_sum,←Finset.sum_mul,←Finset.mul_sum,←Nat.cast_sum]
  rw [hprodfee] at hbound
  apply hbound.trans
  apply bp_le
  have hr : imagePlanRank a.sp≤∑ i,∑ e,dim (S i e) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun e _=>one_endpoint_pin_dimension (a.sp e))
  have hr' : (imagePlanRank a.sp:ℝ)≤∑ i,∑ e,(dim (S i e):ℝ):=by exact_mod_cast hr
  push_cast
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left hr' (by linarith)) (by positivity)

end
end Lax793645Proofs.Simplifications
