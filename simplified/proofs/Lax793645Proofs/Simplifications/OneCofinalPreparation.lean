import Lax793645Proofs.Simplifications.OneLinearPreparation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter PreparationParameters PredictionClass Function Finset
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem restrict_frequent {A : Type} (l : Filter A) (P : A→Prop)
    (h : ∃ᶠ n in l,P n) :
    ∃ l' : Filter A,l'≤l ∧ l'.NeBot ∧ ∀ᶠ n in l',P n := by
  refine ⟨l⊓principal {n|P n},inf_le_left,frequently_iff_neBot.mp h,?_⟩
  exact (eventually_principal.mpr (show ∀ n∈{n|P n},P n from fun _ h=>h)).filter_mono inf_le_right

theorem finite_cofinal_choice {A I : Type} [Finite I] (l : Filter A) [l.NeBot]
    (P : A→I→Prop) (h : ∀ᶠ n in l,∃ i,P n i) :
    ∃ (i : I) (l' : Filter A),l'≤l ∧ l'.NeBot ∧ ∀ᶠ n in l',P n i := by
  obtain ⟨i,hi⟩:=Filter.frequently_exists.mp h.frequently
  obtain ⟨l',hl',hn,hP⟩:=restrict_frequent l (fun n=>P n i) hi
  exact ⟨i,l',hl',hn,hP⟩

variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {P : OneCampaign p M}

/-- Exact bounded-coordinate predictions are classified by literal
equalities. Finite selections fix the banner and one of five classes; no
sequence of disagreement thresholds or additional trimming is used. -/
theorem one_exact_cohorts_refine (hl : l≤atTop) [l.NeBot]
    (hq : OnePlanted q p M) (R : ℕ)
    (h : ∀ᶠ n in l,∃ (z : OneBanners) (i : OneSage p n (M*n)),
      OneAlgebraicRows i.g R ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
        crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z 0)) :
    ∃ l' : Filter ℕ,l'≤l ∧ l'.NeBot ∧
      ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),
      OneDosed q l' m w s b P ∧
      (∀ᶠ n in l', OneAlgebraicRows (fun j=>b.g j n) R ∧ oneFiniteClass (fun j=>b.g j n) b.α=b.c) ∧
      (i=true→b.α true=b.α false) ∧
      ∀ᶠ n in l',∀ x,P n x→((i=true)↔oneMarkedDelta x (b.m n x)=0) := by
  classical
  letI : Fintype PredictionClass:=
    ⟨{dusk,dawn false,dawn true,twinned,noon},by
      intro c
      cases c with
      | dawn i=>cases i <;> simp
      | _=>simp⟩
  let T (n : ℕ) (z : OneBanners) (i : OneSage p n (M*n)) :=
    OneAlgebraicRows i.g R ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
      crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z 0)
  obtain ⟨z,l1,hl1,hn1,hz⟩:=finite_cofinal_choice l
    (fun n z=>∃ i,T n z i) (show ∀ᶠ n in l,∃ z i,T n z i from h)
  let : l1.NeBot:=hn1
  obtain ⟨i,hi⟩:=taking hz
  obtain ⟨c,l2,hl2,hn2,hc⟩:=finite_cofinal_choice l1
    (fun n c=>oneFiniteClass (i n).g z.1=c)
    (Eventually.of_forall fun n=>⟨_,rfl⟩)
  let : l2.NeBot:=hn2
  have hi:=hi.filter_mono hl2
  have htime:l2≤atTop:=hl2.trans (hl1.trans hl)
  refine ⟨l2,hl2.trans hl1,hn2,?_⟩
  let b : OneSketch p M:=⟨c,z.1,z.2.1,fun n=>(i n).m,fun n=>(i n).L,
    fun j n=>(i n).g j,fun _=>0⟩
  let P : OneCampaign p M:=fun n=>oneTender (i n) q (m n) (s n) z 0
  have hlit : c.lit z.1 := by
    obtain ⟨n,hn⟩:=hc.exists
    rw [←hn]
    exact one_finite_lit _ _
  have hconsistent : z.2.2=true→z.1 true=z.1 false := by
    obtain ⟨n,hn⟩:=hi.exists
    exact hn.2.2.1
  have hledger : OneLedger b l2 := ⟨fun ε hε => Eventually.of_forall (fun _=>hε.le),hlit⟩
  refine ⟨b,P,z.2.2,⟨hledger,?_,hi.mono (fun _ hn=>hn.2.1),?_⟩,
    (hi.and hc).mono (fun _ hn=>⟨hn.1.1,hn.2⟩),hconsistent,Eventually.of_forall (fun _ _ hx=>hx.2.2)⟩
  · filter_upwards [hi] with n hn
    exact (show pollen≤crowdSeed by unfold crowdSeed; linarith only [pollen_pos]).trans hn.2.2.2
  · filter_upwards [hc,(eventually_ge_atTop (2*p.r)).filter_mono htime] with n hc hn x hx
    refine ⟨hx.1,hx.2.1,?_⟩
    intro hd j
    have hclass : oneFiniteClass (i n).g z.1=dusk:=hc.trans hd
    obtain ⟨ha,r,hr⟩:=one_finite_dusk _ _ hclass j
    have ha' : z.1 j=1:=dusk_lit z.1 (hclass ▸ one_finite_lit _ _) j
    have hpred:=hx.1.2 j
    rw [ha'] at hpred
    have hE : (((i n).L x j).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
      lt_of_le_of_lt (by exact_mod_cast (hx.1.1 j).1) hq.hB
    exact (one_literal_silent (x j) ((i n).g j) _ ((i n).L x j) r
      hE hq.hg hq.hR hn hr hpred).2

/-- Exact predictions are put in quadratic normal form before
classification and the phase restrictions are applied. -/
theorem one_algebraic_dose_refine (hl : l≤atTop) [l.NeBot] (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (h : ∀ᶠ n in l,∃ g : Bool→OneAugur p (M*n),
      (∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (g i) R) ∧
      (0.000001:ℝ)≤pr ((s n).sap (w n))
        (fun x=>∃ z L α,oneSeems q (m n) (s n) x g z L α 0)) :
    ∃ l' : Filter ℕ,l'≤l ∧ l'.NeBot ∧
      ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),
      OneDosed q l' m w s b P ∧
      (∀ᶠ n in l', OneAlgebraicRows (fun j=>b.g j n) (exactPredictorRows p q) ∧
        oneFiniteClass (fun j=>b.g j n) b.α=b.c) ∧
      (i=true→b.α true=b.α false) ∧
      ∀ᶠ n in l',∀ x,P n x→((i=true)↔oneMarkedDelta x (b.m n x)=0) := by
  classical
  suffices hc : ∀ᶠ n in l,∃ (z : OneBanners) (i : OneSage p n (M*n)),
      OneAlgebraicRows i.g (exactPredictorRows p q) ∧
      (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
      crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z 0) by
    obtain ⟨l',hl',hn',b,P,i,hd,hlin,hα,hδ⟩:=one_exact_cohorts_refine hl hq (exactPredictorRows p q) hc
    exact ⟨l',hl',hn',b,P,i,hd,hlin,hα,hδ⟩
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

theorem one_citable_filter {l' : Filter ℕ} (hl' : l'≤l)
    (h : OneCitable q l p M m w s b P) : OneCitable q l' p M m w s b P := by
  obtain ⟨c,hc,hret⟩:=h.retained
  refine ⟨fun ε hε=>(h.mass ε hε).filter_mono hl',?_,h.mark.filter_mono hl',c,hc,hret.filter_mono hl'⟩
  exact ⟨fun ε hε=>(h.forecast.small ε hε).filter_mono hl',h.forecast.light⟩

/-- Only finitely many alternatives are fixed. Each restriction keeps
an infinite set of indices; no ultrafilter is chosen. -/
theorem one_prepare_cofinal [l.NeBot] (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    ∃ l' : Filter ℕ,l'≤l ∧ l'.NeBot ∧ oneLinearSatisfied q l' m w := by
  classical
  by_cases hfreq : ∃ᶠ n in l,oneBoundedLinearPredicts q (m n) (s n) (w n) 0
  · obtain ⟨l1,hl1,hn1,hpred⟩:=restrict_frequent l
      (fun n=>oneBoundedLinearPredicts q (m n) (s n) (w n) 0) hfreq
    let : l1.NeBot:=hn1
    have hpred' : ∀ᶠ n in l1,∃ g : Bool→OneAugur p (M*n),
        oneBoundedLinearAugurs p n (M*n) g ∧
        (0.000001:ℝ)≤pr ((s n).sap (w n))
          (fun x=>∃ z L α,oneSeems q (m n) (s n) x g z L α 0) := by
      filter_upwards [hpred] with n hn
      obtain ⟨g,hg,hmass⟩:=hn
      refine ⟨g,hg,?_⟩
      simpa only [one_generic_seems_zero_iff] using hmass
    obtain ⟨l2,hl2,hn2,b,P,i,hQ,hlin,hα,hz⟩:=one_algebraic_dose_refine
      (hl1.trans hl) hq (hw.filter_mono hl1) (hx.filter_mono hl1) hpred'
    let : l2.NeBot:=hn2
    have htime:l2≤atTop:=hl2.trans (hl1.trans hl)
    have hw2:=hw.filter_mono (hl2.trans hl1)
    have hx2:=hx.filter_mono (hl2.trans hl1)
    cases i
    · obtain ⟨R,hR,hT⟩:=one_phase_split htime hq hw2 hx2 hQ
        (hz.mono fun n hn x hx he=>Bool.false_ne_true ((hn x hx).mpr he))
      rcases Filter.frequently_or_distrib.mp hT.frequently with hmix|htiny
      · obtain ⟨l3,hl3,hn3,hF⟩:=restrict_frequent l2 _ hmix
        exact ⟨l3,hl3.trans (hl2.trans hl1),hn3,
          one_finished_linear (hlin.filter_mono hl3)
            (one_out_by_mix (hl3.trans htime) hq (hw2.filter_mono hl3)
              (hx2.filter_mono hl3) (one_citable_filter hl3 hR) hF)⟩
      obtain ⟨l3,hl3,hn3,hF⟩:=restrict_frequent l2 _ htiny
      exact ⟨l3,hl3.trans (hl2.trans hl1),hn3,
        one_finished_linear (hlin.filter_mono hl3)
          (one_out_by_cover (hl3.trans htime) hq (hw2.filter_mono hl3)
            (hx2.filter_mono hl3) (one_citable_filter hl3 hR) hF)⟩
    exact ⟨l2,hl2.trans hl1,hn2,one_finished_linear hlin
      (one_phase_absent_exact htime hq hw2 hx2 hQ (hα rfl)
        (hz.mono fun n hn x hx=>(hn x hx).mp rfl))⟩
  have hn:=not_frequently.mp hfreq
  exact ⟨l,le_rfl,inferInstance,s,one_retain_initial hl hq hx,Or.inl ⟨0,le_rfl,
    hn.and (((one_retain_initial hl hq hx).unconditional hl hq hw).mono fun n hn=>hn.2)⟩⟩

end
end Lax793645Proofs.Simplifications
