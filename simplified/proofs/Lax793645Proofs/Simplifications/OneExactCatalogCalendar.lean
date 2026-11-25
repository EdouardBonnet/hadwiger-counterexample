import Lax793645Proofs.Simplifications.OneExactSpanCatalog
import Lax793645Proofs.Simplifications.OneAnalyticAsymptotics

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis StatusAnalysis.DualAnalysis Filter
open scoped Topology
noncomputable section
variable {p : Shape} {M s0 : ℕ} {q : PreparationParameters} {l : Filter ℕ}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}

/-- Full cell reference bounds and the prepared rank event hold for
every palette with a fixed row bound. The exceptional probability is
measured before choosing either leaf. -/
theorem OneVeil.exact_catalog_calendar (h : OneVeil p M q s0 l m s w) (R : ℕ) :
    ∀ᶠ n in l,∀ c : ℕ,∀ Y : OneSilhouette p (M*n) c,
      OneFullLinearSilhouette Y R→
      ∃ H : Space (OneJointKey p (M*n)),
        pr ((s n).sap (w n)) (fun o=>¬OnePaletteGood H o)≤1/16 ∧
        (∀ o o',OnePaletteGood H o→OnePaletteGood H o'→
          OneFullTableGap Y (m n) (onePreparationPins q) o o') ∧
        (∀ o : OneUnit p n (M*n),OnePaletteGood H o→∀ d : Rates,∀ v : Charts p n d,
          (∀ i z,totalRank (v i z)≤onePreparationPins q)→
          ∀ i E,E.card≤q.B→∀ z α f,
          ExactStatusPrediction (oneWisp p Y) (oneWake p Y (m n) o v) i E (yokeSet z α) f→
            OneTesterFree Y f ∧
            onePostulates (o i) (oneFromPulse Y f) (oneYoke (m n) o i (v i z) α) ∅ 0) ∧
        (∀ o : OneUnit p n (M*n),OnePaletteGood H o→OneGenericStatusContinues Y (m n) q.B o) ∧
        TesterSeparated (oneWisp p Y) (OneTesterFree Y) := by
  have hM : (0:ℝ)<M := by exact_mod_cast (by have hh:=h.parameters.planted.hM; omega : 0<M)
  have hdecay : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (𝓝 0) := by
    convert bp_nat_vanish (show 0<(M:ℝ)/2 by positivity) using 1 <;> push_cast <;> ring
  have hN : ∀ᶠ n : ℕ in atTop,∀ t : Tag p.g,
      bp (-((M*n:ℕ):ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) t))/2 := by
    apply eventually_all.mpr
    intro t
    exact (hdecay.eventually (gt_mem_nhds (half_pos (bp_pos _)))).mono (fun _ hn=>hn.le)
  have hsmall : ∀ᶠ n : ℕ in atTop,∀ t : Tag p.g,
      2*bp (num (oneUnaryRail (p:=p) t))*bp (-((M*n:ℕ):ℝ)/2)≤bp (-(R:ℝ))/2 := by
    apply eventually_all.mpr
    intro t
    have hd := hdecay.const_mul (2*bp (num (oneUnaryRail (p:=p) t)))
    simp only [mul_zero] at hd
    exact (hd.eventually (gt_mem_nhds (half_pos (bp_pos _)))).mono (fun _ hn=>hn.le)
  have hbad : ∀ᶠ n : ℕ in atTop,
      16*bp ((3*(p.g*R):ℕ)+p.b-31*(n:ℝ)/32)≤(1/16:ℝ) := by
    have hd : Tendsto (fun n : ℕ=>16*bp ((3*(p.g*R):ℕ)+p.b-31*(n:ℝ)/32)) atTop (𝓝 0) := by
      convert (bp_nat_vanish (by norm_num : 0<(31/32:ℝ))).const_mul
        (16*bp ((3*(p.g*R):ℕ)+p.b)) using 1
      · funext n
        rw [bp_sub]
        rw [show -(31/32:ℝ)*(n:ℝ)=-(31*(n:ℝ)/32) by ring,bp_neg]
        ring
      · ring
    exact (hd.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/16))).mono (fun _ hn=>hn.le)
  filter_upwards [h.query_caps,hN.filter_mono h.time,hsmall.filter_mono h.time,
    hbad.filter_mono h.time,h.parameters.planted.unary_room.filter_mono h.time,
    h.parameters.planted.wrap.filter_mono h.time,
    (eventually_ge_atTop (2*p.r)).filter_mono h.time]
    with n hc hN hsmall hbad hroom hwrap hn c Y hY
  obtain ⟨H,hH,hgap,hnorm,hcontinue⟩:=one_exact_span_catalog_control Y hY hN hsmall (m n)
    (onePreparationPins q) q.B h.parameters.planted.hg h.parameters.planted.hG
    h.parameters.planted.hJ h.parameters.planted.hR hn h.parameters.exactLateRoom
    h.parameters.planted.hB
  refine ⟨H,?_,hgap,hnorm,hcontinue,one_exact_tester_separated Y hY
    (by have hh:=h.parameters.planted.hG; omega) hN hsmall⟩
  refine (one_palette_good_mass (m n) (by omega) hwrap.2.1 H _ hc.1 ?_).trans ?_
  · intro i o
    simpa only [one_div_mul_eq_div] using hc.2.1 i o
  refine (mul_le_mul_of_nonneg_left (bp_le ?_) (by norm_num : (0:ℝ)≤16)).trans hbad
  have hh : (dim H:ℝ)≤(3*(p.g*R):ℕ) := by exact_mod_cast hH
  linarith only [hh]

end
end Lax793645Proofs.Simplifications
