import Lax793645Proofs.Simplifications.OneExactCohorts
import Lax793645Proofs.Simplifications.OneFiniteDose

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter PreparationParameters Function
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {M : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {U : Ultrafilter ℕ}

/-- Exact predictions are put in quadratic normal form before
classification and the phase restrictions are applied. -/
theorem one_algebraic_prediction_dose (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n))
    (h : ∀ᶠ n in U,∃ g : Bool→OneAugur p (M*n),
      (∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (g i) R) ∧
      (0.000001:ℝ)≤pr ((s n).sap (w n))
        (fun x=>∃ z L α,oneSeems q (m n) (s n) x g z L α 0)) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),
      OneDosed q (U:Filter ℕ) m w s b P ∧
      (∀ᶠ n in U, OneAlgebraicRows (fun j=>b.g j n) (exactPredictorRows p q) ∧
        oneFiniteClass (fun j=>b.g j n) b.α=b.c) ∧
      (i=true→b.α true=b.α false) ∧
      ∀ᶠ n in U,∀ x,P n x→((i=true)↔oneMarkedDelta x (b.m n x)=0) := by
  classical
  suffices hc : ∀ᶠ n in U,∃ (z : OneBanners) (i : OneSage p n (M*n)),
      OneAlgebraicRows i.g (exactPredictorRows p q) ∧
      (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
      crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z 0) by
    obtain ⟨b,P,i,hd,hlin,hα,hδ⟩:=one_exact_cohorts_to_dose hl hq (exactPredictorRows p q) hc
    exact ⟨b,P,i,hd,hlin,hα,hδ⟩
  have htail : ∀ᶠ n : ℕ in atTop,2*bp (-(n:ℝ)/2)≤crowdSeed := by
    have ht : Tendsto (fun n : ℕ=>2*bp (-(n:ℝ)/2)) atTop (𝓝 0) := by
      convert (bp_nat_vanish (by norm_num : 0<(1/2:ℝ))).const_mul 2 using 1 <;> ring
    exact (ht.eventually (gt_mem_nhds (by unfold crowdSeed; linarith only [pollen_pos]))).mono
      (fun _ hn=>hn.le)
  have hside : ∀ᶠ n : ℕ in atTop,2*q.L≤bp ((n:ℝ)/32) := by
    filter_upwards [bp_poly_dom_nat (a:=1/32) (by norm_num) (2*q.L) 0] with n hn
    simpa only [pow_zero,mul_one,one_div_mul_eq_div] using hn.le
  filter_upwards [h,hw,hx,hq.unary_room.filter_mono hl,hq.wrap.filter_mono hl,
    htail.filter_mono hl,hside.filter_mono hl,
    (eventually_ge_atTop (2*p.r)).filter_mono hl,
    (eventually_ge_atTop (64*(p.b+4))).filter_mono hl]
    with n hp hw hx hroom hwrap htail hside hn hsize
  have hv : oneBySide ((s n).sap (w n)) (m n) (2*q.L) :=
    one_upper_side hw.border (one_sap_twice hw.law hx.weight) (by norm_num) le_rfl
  obtain ⟨z,i,hlin,hcap,hα,hmass⟩:=one_algebraic_cohort (m n) (w n) (s n) hx hw.law
    hq.hg hq.hG hq.hJ hq.hR hn hq.exactRoom
    (by omega) hwrap.2.1 hq.hB hsize htail
    (fun j o=>(hv j o).trans (mul_le_mul_of_nonneg_right hside (one_raw_nonneg (m n) o)))
    hp
  exact ⟨z,i,hlin,hcap,hα,hmass⟩

end
end Lax793645Proofs.Simplifications
