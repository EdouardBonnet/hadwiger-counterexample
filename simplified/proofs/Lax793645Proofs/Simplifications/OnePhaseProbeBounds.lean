import Lax793645Proofs.Simplifications.OnePhaseHeat

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def onePrimalMatrix (P : OneFrame p n N) : Mat (Fin (2*N)) (Row p n):=
  LinearMap.toMatrix' ((oneAmbientCoordinates N).toLinearMap.comp (onePrimal P))

def oneBasisFrom {q : Comp p.g→ℕ} (x : OneUnit p n N) (i : Bool)
    (Z : ImageTuple (Comp p.g) q (2*N)) : Prop:=
  ∀ e,Function.Injective (Z e).mulVec ∧colSp (Z e)≤colSp (onePrimalMatrix (x i e))

theorem one_primal_dual_image {J : Type} [Fintype J] [DecidableEq J]
    (x : OneUnit p n N) (i : Bool) (e : Comp p.g) (U : Mat (Row p n) J) :
    oneDualImages x e*onePrimalCoefficient i U=
      LinearMap.toMatrix' (oneDuality N).toLinearMap*(onePrimalMatrix (x i e)*U) := by
  apply coe_mv_inj
  apply LinearMap.ext
  intro v
  simp only [Matrix.mulVecLin_apply,←mulVec_mulVec,one_primal_coefficient_apply,
    one_dual_endpoint_images,onePrimalMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply,
    LinearEquiv.coe_coe,oneDuality,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rfl

abbrev OnePrimalAmong (p : Shape) (n : ℕ) (q : Comp p.g→ℕ) :=∀ e,Mat (Row p n) (Fin (q e))
abbrev OneChannelAmong (p : Shape) (t : Comp p.g→ℕ) :=Bool→∀ e,Mat (HyperbolicIdx p.h) (Fin (t e))

theorem one_probe_format_size (q t : Comp p.g→ℕ) :
    num (OnePrimalAmong p n q×OneChannelAmong p t)=
      bp (num (Row p n)*(∑ e,q e)+4*p.h*(∑ e,t e)) := by
  classical
  unfold num
  rw [card_space,dim,finrank_prod]
  have hq : dim (OnePrimalAmong p n q)=Fintype.card (Row p n)*∑ e,q e := by
    unfold dim OnePrimalAmong
    rw [finrank_pi_fintype,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _=>(dim_mat ..).trans (by simp))
  have ht : dim (OneChannelAmong p t)=4*p.h*∑ e,t e := by
    unfold dim OneChannelAmong
    rw [finrank_pi_fintype,Fintype.sum_bool]
    simp only [finrank_pi_fintype,dim_mat,HyperbolicIdx,Fintype.card_sum,Fintype.card_fin]
    rw [←Finset.mul_sum]
    ring
  change bp (↑(dim (OnePrimalAmong p n q)+dim (OneChannelAmong p t)))=_
  rw [hq,ht]
  push_cast
  congr 1

def oneHeatRate (p : Shape) (n N : ℕ) (ζ : ℝ) (q t : ℕ) :=
  bp (num (Row p n)*q+4*p.h*t)*fee (2*N) ζ (q+t)

set_option maxHeartbeats 800000 in
/-- Joint primal-companion and polar-action estimate. Both observations
are charged to one raw image event on disjoint nominal subspaces. -/
theorem one_heat_rate {q t : Comp p.g→ℕ} (i : Bool) (S : Party) (hi : S i=1)
    (A B : ImageTuple (Comp p.g) t (2*N)) (Z : ImageTuple (Comp p.g) q (2*N))
    (m : Mixer p n) {ζ : ℝ}
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp)) :
    pr (oneUnitRaw m N) (fun x=>oneBasisFrom x i Z ∧oneTupleGlimpse x i A ∧
      oneThermal x S A=B)≤oneHeatRate p n N ζ (∑ e,q e) (∑ e,t e) := by
  classical
  let Fmt:=OnePrimalAmong p n q×OneChannelAmong p t
  let PP (v : Fmt) (e : Comp p.g):=onePrimalCoefficient i (v.1 e)
  let CC (v : Fmt) (e : Comp p.g):=oneChannelCoefficient (n:=n) (fun j=>v.2 j e)
  let ZZ : ImageTuple (Comp p.g) q (2*N):=
    fun e=>LinearMap.toMatrix' (oneDuality N).toLinearMap*Z e
  have hh:=image_probe_family_cap oneDualImages PP CC ZZ B
    (prodW_nonneg (fun _=>one_raw_nonneg m)) hcap
    (fun x=>oneBasisFrom x i Z ∧oneTupleGlimpse x i A ∧oneThermal x S A=B) ?_
  · rw [one_probe_format_size] at hh
    exact hh
  rintro x ⟨hZ,hA,hB⟩
  choose U hU using fun e=>pull_cols (onePrimalMatrix (x i e)) (Z e) (hZ e).2
  refine ⟨(U,oneSparks x S A),fun e=>?_,fun e=>?_⟩
  · refine ⟨one_primal_coefficient_inj i (U e) ?_,one_hot_channel_coefficient x S A i hi hA e,
      one_coefficient_disjoint i (U e) _⟩
    intro a b he
    apply (hZ e).1
    rw [←hU e,←mulVec_mulVec,←mulVec_mulVec,he]
  · change oneDualImages x e*onePrimalCoefficient i (U e)=ZZ e ∧
      oneDualImages x e*oneChannelCoefficient (n:=n) (fun j=>oneSparks x S A j e)=B e
    refine ⟨?_,(one_fused_thermal x S A e).trans (congrFun hB e)⟩
    rw [one_primal_dual_image,hU]

/-- The concrete one-frame law supplies the initial image cap required
by the joint phase estimate. -/
theorem one_heat_rate_raw {q t : Comp p.g→ℕ} (i : Bool) (S : Party) (hi : S i=1)
    (A B : ImageTuple (Comp p.g) t (2*N)) (Z : ImageTuple (Comp p.g) q (2*N))
    (m : Mixer p n) {ζ : ℝ} (hz : 0≤ζ) (hz' : ζ≤6)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hζ : (dim (OneFull p n):ℝ)+2≤(ζ/6)*(2*N)) :
    pr (oneUnitRaw m N) (fun x=>oneBasisFrom x i Z ∧oneTupleGlimpse x i A ∧
      oneThermal x S A=B)≤oneHeatRate p n N ζ (∑ e,q e) (∑ e,t e) :=
  one_heat_rate i S hi A B Z m (fun a=>one_dual_image_pin_cap m a hz hz' hN hζ)

end
end Lax793645Proofs.Simplifications
