import Lax793645Proofs.Simplifications.HyperbolicRowCaps
import Lax793645Proofs.Simplifications.OnePrimalImageBounds
import Lax793645Proofs.Simplifications.PreparedLinearRank

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneFreeColumns (p : Shape) (n : ℕ) (s : Label p.b) :
    Vec (Fin n)→ₗ[F]OneFull p n:=
  quadraticPrimalIn.comp (blockRay p n s Block.Z).mulVecLin

theorem one_free_columns_injective (s : Label p.b) : Injective (oneFreeColumns p n s) := by
  intro a b h
  exact blockRay_inj p n s Block.Z (congrArg Prod.fst h)

def oneMixedRow (J : Vec (Fin n)→ₗ[F]OneFull p n) (o : OneOrient p n N) :
    (Comp p.g→Vec (HyperbolicIdx N))→ₗ[F]Module.Dual F (Vec (Fin n)):=
  ∑ e,(quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' ((o e).comp J)).comp
    (LinearMap.proj e)

theorem one_independent_row (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (J : Vec (Fin n)→ₗ[F]OneFull p n) (hJ : Injective J)
    (v : Comp p.g→Vec (HyperbolicIdx N)) (hv : v≠0)
    (θ : Module.Dual F (Vec (Fin n))) :
    pr (oneRaw m N) (fun o=>oneMixedRow J o v=θ)≤8*bp (-(n:ℝ)) := by
  letI : Fintype (Module.Dual F (Vec (Fin n))):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  obtain ⟨e,he⟩ : ∃ e,v e≠0:=Function.ne_iff.mp hv
  have hc:=quadratic_channel_frames_exist (hyperbolicMatrix N).toQuadraticForm'
    (hyperbolic_matrix_nondegenerate N) (selfM p n m.mixM).toQuadraticForm'
    (C:=Vec (Fin p.h)) (one_frame_room hroom)
  have hh:=independent_sum_point_cap
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law hc)
    (fun i P=>quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J) (v i))
    e (8*bp (-(n:ℝ)))
    (fun y=>by
      change pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm'
        (quadraticChannelClass (C:=Vec (Fin p.h)) (selfM p n m.mixM).toQuadraticForm')))
        (fun P=>quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J) (v e)=y)≤_
      simpa only [dim_vec,Fintype.card_fin] using hyperbolic_frame_row_cap
        (quadraticChannelClass (C:=Vec (Fin p.h)) (selfM p n m.mixM).toQuadraticForm')
        J hJ y (v e) he hN) θ
  simpa only [oneRaw,oneMixedRow,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply] using hh

theorem one_independent_rank (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (J : Vec (Fin n)→ₗ[F]OneFull p n) (hJ : Injective J)
    (H : Space (Comp p.g→Vec (HyperbolicIdx N))) :
    pr (oneRaw m N) (fun o=>¬Injective ((oneMixedRow J o).comp H.subtype))≤
      8*bp ((dim H:ℝ)-n) := by
  let P (v : H) (o : OneOrient p n N):=v≠0 ∧ oneMixedRow J o v.val=0
  have hsub (o : OneOrient p n N)
      (h : ¬Injective ((oneMixedRow J o).comp H.subtype)) : ∃ v,P v o := by
    by_contra! hh
    apply h
    intro a b hab
    have he : ((oneMixedRow J o).comp H.subtype) (a-b)=0:=by rw [map_sub,hab,sub_self]
    apply sub_eq_zero.mp
    by_contra hn
    exact hh (a-b) ⟨hn,he⟩
  have hp (v : H) : pr (oneRaw m N) (P v)≤8*bp (-(n:ℝ)) := by
    by_cases hv : v=0
    · simp only [P,hv,ne_eq,not_true_eq_false,false_and,pr_false]
      exact mul_nonneg (by norm_num) (bp_pos _).le
    have hv' : v.val≠0:=fun h=>hv (Subtype.ext h)
    simpa only [P,hv,ne_eq,not_false_eq_true,true_and] using
      one_independent_row m hroom hN J hJ v.val hv' 0
  refine ((pr_mono (one_raw_nonneg m) hsub).trans (pr_exists_le (one_raw_nonneg m) P)).trans ?_
  refine (Finset.sum_le_sum fun v _=>hp v).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,bp_sub,bp_neg]
  ring

/-- Full rank is charged to the prepared endpoint marginal. It is not
asserted under the much larger separately normalized leaf cap. -/
theorem one_prepared_linear_rank (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (H : Space (Comp p.g→Vec (HyperbolicIdx N))) (ρ : Wgt (OneOrient p n N))
    (hρ : ∀ o,ρ o≤bp ((n:ℝ)/32)*oneRaw m N o) :
    pr ρ (fun o=>∃ s : Label p.b,
      ¬Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype))≤
      8*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32) := by
  refine (pr_cap hρ _).trans ?_
  have hh:=(pr_exists_le (one_raw_nonneg m)
    (fun s o=>¬Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype))).trans
    (Finset.sum_le_sum (fun s _=>one_independent_rank m hroom hN _ (one_free_columns_injective s) H))
  refine (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,dim_vec,Fintype.card_fin]
  calc
    _=8*(bp ((n:ℝ)/32)*bp (p.b:ℝ)*bp ((dim H:ℝ)-n)):=by ring
    _=8*bp ((n:ℝ)/32+p.b+((dim H:ℝ)-n)):=by rw [bp_add,bp_add]
    _=_:=by congr 1; congr 1; ring

theorem one_prepared_growing_rank_calendar (p : Shape) :
    ∀ᶠ n : ℕ in Filter.atTop,∀ N : ℕ,∀ m : Mixer p n,
      Fintype.card (Row p n)+2*p.h+1≤N →4≤N →
      ∀ H : Space (Comp p.g→Vec (HyperbolicIdx N)),dim H≤n/4 →
      ∀ ρ : Wgt (OneOrient p n N),(∀ o,ρ o≤bp ((n:ℝ)/32)*oneRaw m N o) →
      pr ρ (fun o=>∃ s : Label p.b,
        ¬Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype))≤bp (-(n:ℝ)/2) := by
  filter_upwards [Filter.eventually_ge_atTop (64*(p.b+4))] with n hn N m hroom hN H hH ρ hρ
  refine (one_prepared_linear_rank m hroom hN H ρ hρ).trans ?_
  have hdim : 4*dim H≤n:=by omega
  have hdim' : 4*(dim H:ℝ)≤n:=by exact_mod_cast hdim
  have hn' : 64*((p.b:ℝ)+4)≤n:=by exact_mod_cast hn
  rw [show (8:ℝ)=bp 3 by norm_num [bp],←bp_add]
  exact bp_le (by linarith only [hdim',hn'])

end
end Lax793645Proofs.Simplifications
