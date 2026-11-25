import Lax793645Proofs.Simplifications.OnePreparationBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : PreparationParameters}

theorem one_nascent_frames (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (hw : OneNascent q m w) (x : OneUnit p n N) (hx : w x≠0) : oneFrameSide m x := by
  have hraw : oneUnitRaw m N x≠0 := by
    intro hzero
    have hc:=hw.total x
    rw [hzero,mul_zero] at hc
    exact hx (le_antisymm hc (hw.law.nz x))
  intro i
  change (∏ j : Bool,oneRaw m N (x j))≠0 at hraw
  have hi : oneRaw m N (x i)≠0 :=
    (Finset.prod_ne_zero_iff.mp hraw) i (Finset.mem_univ i)
  by_contra hh
  exact hi (one_raw_carried m N (x i) hh)

set_option maxHeartbeats 600000 in
/-- Closed-pin peeling retains at least half the mass. No intersection
rank cutoff is imposed: the marked profiles use the pin rank bound. -/
theorem one_entered_calendar (q : PreparationParameters) (p : Shape)
    (_hD : 0<q.D) (hq : OnePreparationAllows q)
    (hK : (q.D:ℝ)+q.ζ≤((q.ζ/6)-(q.ζ/6)/4)*q.e) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n) (w : Wgt (OneUnit p n (M*n))),OneNascent q m w →
      carried w (fun x=>(oneRawHoles m).unit (x true,x false)) →
      ∃ s : OneLeafMixture p n (M*n),OneEntered q m w s := by
  filter_upwards [one_leaf_calendar p hq.pos hq.small q.D q.e hK,
    eventually_ge_atTop 1] with M hM hMpos
  have hz:= (trend_sizes (atTop:Filter ℕ) le_rfl hMpos).2
  have hδ : ∀ᶠ n : ℕ in atTop,bp (-q.ζ*(2*(M*n:ℕ)))≤1/2 := by
    have h2 : Tendsto (fun n : ℕ=>bp (-(2*q.ζ)*(M*n:ℕ))) atTop (𝓝 0):=
      (bp_tendsto_zero (by linarith only [hq.pos])).comp hz
    filter_upwards [h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n h2
    convert h2.le using 1 <;> congr 1 <;> ring
  filter_upwards [hM,hδ] with n hn hδ m w hw hunit
  let P (x : OneUnit p n (M*n)):=w x≠0 ∧ (oneRawHoles m).unit (x true,x false) ∧ oneFrameSide m x
  have hP : carried w P := by
    intro x hx
    by_contra hnz
    apply hx
    exact ⟨hnz,by by_contra hh; exact hnz (hunit x hh),one_nascent_frames m w hw x hnz⟩
  obtain ⟨s,hs,hwithin,hmass⟩:=hn m w hw.total hw.law.nz P
  rw [(carried_iff_pr hw.law.nz).mp hP,hw.law.total] at hmass
  refine ⟨s,⟨?_,image_strength_slide hs ?_ le_rfl le_rfl
    (prodW_nonneg (fun _=>one_raw_nonneg m)),?_⟩⟩
  · linarith only [hmass,hδ]
  · unfold leafOld
    linarith
  intro i hi x hx
  exact hwithin i hi x hx

end
end Lax793645Proofs.Simplifications
