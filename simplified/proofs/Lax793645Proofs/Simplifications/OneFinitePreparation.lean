import Lax793645Proofs.Simplifications.OnePreparationCertificate

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter PreparationParameters PredictionClass Function Finset
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Each member of a finite cover may have its own bound on the dimension.
Taking their maximum gives a bound valid for every member at once. -/
theorem eventually_of_finite_cases {A I : Type} [Finite I] {l : Filter A}
    (P : A → I → Prop) {Q : A → Prop} (hp : ∀ᶠ n in l, ∃ i,P n i)
    (h : ∀ i (v : Filter A),v ≤ l → v.NeBot → (∀ᶠ n in v,P n i) → ∀ᶠ n in v,Q n) :
    ∀ᶠ n in l,Q n := by
  classical
  have each (i : I) : ∀ᶠ n in l,P n i → Q n := by
    apply (eventually_inf_principal (s:={n | P n i})).mp
    let v := l ⊓ principal {n | P n i}
    change ∀ᶠ n in v,Q n
    by_cases hv : v=⊥
    · rw [hv]; exact eventually_bot
    apply h i v inf_le_left (neBot_iff.mpr hv)
    exact (eventually_principal.mpr (show ∀ n∈{n | P n i},P n i from fun _ hn=>hn)).filter_mono inf_le_right
  filter_upwards [hp,eventually_all.mpr each] with n ⟨i,hi⟩ hn
  exact hn i hi

private theorem bound_on_finite_cases {A I : Type} [Finite I] {l : Filter A}
    (P : A → I → Prop) {Q : A → ℕ → Prop} (mono : ∀ n,Monotone (Q n))
    (hp : ∀ᶠ n in l,∃ i,P n i)
    (h : ∀ i (v : Filter A),v≤l → v.NeBot → (∀ᶠ n in v,P n i) →
      ∃ k,∀ᶠ n in v,Q n k) : ∃ k,∀ᶠ n in l,Q n k := by
  classical
  letI := Fintype.ofFinite I
  have each (i : I) : ∃ k,∀ᶠ n in l,P n i → Q n k := by
    let v := l ⊓ principal {n | P n i}
    suffices ∃ k,∀ᶠ n in v,Q n k by
      obtain ⟨k,hk⟩:=this
      exact ⟨k,eventually_inf_principal.mp hk⟩
    by_cases hv : v=⊥
    · exact ⟨0,hv ▸ eventually_bot⟩
    exact h i v inf_le_left (neBot_iff.mpr hv)
      ((eventually_principal.mpr (show ∀ n∈{n | P n i},P n i from fun _ hn=>hn)).filter_mono inf_le_right)
  choose k hk using each
  refine ⟨univ.sup k,?_⟩
  filter_upwards [hp,eventually_all.mpr hk] with n ⟨i,hi⟩ hn
  exact mono n (Finset.le_sup (f:=k) (mem_univ i)) (hn i hi)

variable {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {l : Filter ℕ}

/-- The banner, class, and exact predictions are chosen separately at each
dimension and for each admissible law. -/
def OneCohortAt {n N : ℕ} (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N)
    (z : OneBanners) (c : PredictionClass) (i : OneSage p n N) : Prop :=
  OneAlgebraicRows i.g (exactPredictorRows p q) ∧
  (∀ x j,totalRank (i.m x j)≤q.e) ∧ (z.2.2=true → z.1 true=z.1 false) ∧
  crowdSeed≤pr (s.sap w) (oneTender i q m s z 0) ∧ oneFiniteClass i.g z.1=c

theorem one_cohort_calendar (hq : OnePlanted q p M) :
    ∀ᶠ n : ℕ in atTop,∀ (m : Mixer p n) (w : Wgt (OneUnit p n (M*n)))
      (s : OneLeafMixture p n (M*n)),OneNascent q m w → OneEntered q m w s →
      ¬oneBoundedLinearPredicts q m s w 0 ∨ ∃ z c i,OneCohortAt q m w s z c i := by
  classical
  have htail : ∀ᶠ n : ℕ in atTop,2*bp (-(n:ℝ)/2)≤crowdSeed := by
    have ht : Tendsto (fun n : ℕ=>2*bp (-(n:ℝ)/2)) atTop (𝓝 0) := by
      convert (bp_nat_vanish (by norm_num : 0<(1/2:ℝ))).const_mul 2 using 1 <;> ring
    exact (ht.eventually (gt_mem_nhds (by unfold crowdSeed; linarith only [pollen_pos]))).mono
      (fun _ hn=>hn.le)
  have hside : ∀ᶠ n : ℕ in atTop,2*q.L≤bp ((n:ℝ)/32) := by
    filter_upwards [bp_poly_dom_nat (a:=1/32) (by norm_num) (2*q.L) 0] with n hn
    simpa only [pow_zero,mul_one,one_div_mul_eq_div] using hn.le
  filter_upwards [hq.unary_room,hq.wrap,htail,hside,eventually_ge_atTop (2*p.r),
    eventually_ge_atTop (64*(p.b+4))] with n hroom hwrap ht hs hn hsize m w s hw hx
  by_cases H : oneBoundedLinearPredicts q m s w 0
  · right
    have hv := one_upper_side hw.border (one_sap_twice hw.law hx.weight) (by norm_num) (le_refl (2*q.L))
    obtain ⟨g,hg,hpr⟩:=H
    obtain ⟨z,i,hr,hcap,hα,hmass⟩:=one_algebraic_cohort m w s hx hw.law hq.hg hq.hG
      hq.hJ hq.hR hn hq.exactRoom (by omega) hwrap.2.1 hq.hB hsize ht
      (fun j o=>(hv j o).trans (mul_le_mul_of_nonneg_right hs (one_raw_nonneg m o)))
      ⟨g,hg,by simpa only [one_generic_seems_zero_iff] using hpr⟩
    exact ⟨z,_,i,hr,hcap,hα,hmass,rfl⟩
  exact Or.inl H

private theorem one_header_data (hl : l≤atTop) [l.NeBot] (hq : OnePlanted q p M)
    (z : OneBanners) (c : PredictionClass)
    (h : ∀ᶠ n in l,∃ i,OneCohortAt q (m n) (w n) (s n) z c i) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M), b.c=c ∧ (∀ n,b.ε n=0) ∧
      OneDosed q l m w s b P ∧ oneLinearLedger q b l ∧
      (z.2.2=true → b.α true=b.α false) ∧
      ∀ᶠ n in l,∀ x,P n x → ((z.2.2=true) ↔ oneMarkedDelta x (b.m n x)=0) := by
  classical
  obtain ⟨i,hi⟩:=taking h
  let b : OneSketch p M := ⟨c,z.1,z.2.1,fun n=>(i n).m,fun n=>(i n).L,
    fun j n=>(i n).g j,fun _=>0⟩
  let P : OneCampaign p M := fun n=>oneTender (i n) q (m n) (s n) z 0
  obtain ⟨n,hn⟩:=hi.exists
  have hledger : OneLedger b l :=
    ⟨fun ε he=>Eventually.of_forall (fun _=>he.le),by change c.lit z.1; rw [←hn.2.2.2.2]; exact one_finite_lit _ _⟩
  refine ⟨b,P,rfl,fun _=>rfl,⟨hledger,?_,hi.mono (fun _ hn=>hn.2.1),?_⟩,
    hi.mono (fun _ hn=>⟨hn.1,hn.2.2.2.2⟩),hn.2.2.1,Eventually.of_forall fun _ _ hx=>hx.2.2⟩
  · exact hi.mono fun _ hn=>(show pollen≤crowdSeed by unfold crowdSeed; linarith only [pollen_pos]).trans hn.2.2.2.1
  · filter_upwards [hi,(eventually_ge_atTop (2*p.r)).filter_mono hl] with n hn hsize x hx
    refine ⟨hx.1,hx.2.1,?_⟩
    intro hd j
    have hclass : oneFiniteClass (i n).g z.1=dusk := hn.2.2.2.2.trans hd
    obtain ⟨_,r,hr⟩:=one_finite_dusk _ _ hclass j
    have ha : z.1 j=1 := dusk_lit z.1 (hclass ▸ one_finite_lit _ _) j
    have hpred:=hx.1.2 j
    rw [ha] at hpred
    have hE : (((i n).L x j).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
      lt_of_le_of_lt (by exact_mod_cast (hx.1.1 j).1) hq.hB
    exact (one_literal_silent (x j) ((i n).g j) _ ((i n).L x j) r
      hE hq.hg hq.hR hsize hr hpred).2

private theorem one_citable_on {l' : Filter ℕ} (hl' : l'≤l)
    {b : OneSketch p M} {P : OneCampaign p M}
    (h : OneCitable q l p M m w s b P) : OneCitable q l' p M m w s b P := by
  obtain ⟨c,hc,hret⟩:=h.retained
  exact ⟨fun ε he=>(h.mass ε he).filter_mono hl',
    ⟨fun ε he=>(h.forecast.small ε he).filter_mono hl',h.forecast.light⟩,
    h.mark.filter_mono hl',c,hc,hret.filter_mono hl'⟩

/-- Take the worst quota over the finite cases. Both the input law and the
resulting branch can vary with the dimension. -/
theorem one_preparation_cases (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    ∃ k,∀ᶠ n in l,OnePreparedAt q (m n) (w n) k := by
  classical
  letI : Fintype PredictionClass :=
    ⟨{dusk,dawn false,dawn true,twinned,noon},by
      intro c
      cases c with
      | dawn i=>cases i <;> simp
      | _=>simp⟩
  let P (n : ℕ) : Option (OneBanners × PredictionClass) → Prop
    | none => ¬oneBoundedLinearPredicts q (m n) (s n) (w n) 0
    | some (z,c) => ∃ i,OneCohortAt q (m n) (w n) (s n) z c i
  apply bound_on_finite_cases P (fun n=>one_prepared_mono q (m n) (w n))
  · filter_upwards [(one_cohort_calendar hq).filter_mono hl,hw,hx] with n hn H E
    rcases hn _ _ _ H E with h|⟨z,c,i,h⟩
    · exact ⟨none,h⟩
    exact ⟨some (z,c),i,h⟩
  intro tag v hv hne htag
  letI : v.NeBot := hne
  have ht := hv.trans hl
  have H := hw.filter_mono hv
  have E := hx.filter_mono hv
  cases tag with
  | none =>
    have durable := one_retain_initial ht hq E
    exact one_quiet_certificate durable
      (htag.and ((durable.unconditional ht hq H).mono fun _ hn=>hn.2))
  | some tag =>
    obtain ⟨z,c⟩:=tag
    obtain ⟨b,P,hc,hε,dose,rows,hα,hδ⟩:=one_header_data ht hq z c htag
    by_cases hfree : c=noon
    · exact one_predicted_certificate hε rows
        (one_unrestricted_class ht hq H E (dose.citable ht hq.hM) (hc.trans hfree))
    by_cases hzero : z.2.2=true
    · exact one_predicted_certificate hε rows
        (one_phase_absent_exact ht hq H E dose (hα hzero)
          (hδ.mono fun _ hn x hx=>(hn x hx).mp hzero))
    have remaining (v' : Filter ℕ) (hv' : v'≤v) : ∃ k,∀ᶠ n in v',OnePreparedAt q (m n) (w n) k := by
      have ht := hv'.trans ht
      have H := H.filter_mono hv'
      have E := E.filter_mono hv'
      have rows := rows.filter_mono hv'
      have hδ := hδ.filter_mono hv'
      have dose : OneDosed q v' m w s b P :=
        ⟨⟨fun ε h=>(dose.forecast.small ε h).filter_mono hv',dose.forecast.light⟩,
          dose.lower.filter_mono hv',dose.capped.filter_mono hv',dose.mark.filter_mono hv'⟩
      obtain ⟨R,hR,hT⟩:=one_phase_split ht hq H E dose
        (hδ.mono fun _ hn x hx he=>hzero ((hn x hx).mpr he))
      let B (n : ℕ) : Bool→Prop
        | true => oneTonalMix (fun x=>oneMarkedDelta x (b.m n x)) (onePotion s w R n)
        | false => oneTonalTiny (fun x=>oneMarkedDelta x (b.m n x)) (onePotion s w R n) q.d
      apply bound_on_finite_cases B (fun n=>one_prepared_mono q (m n) (w n)) (hT.mono fun n h=>h.elim (fun x=>⟨true,x⟩) (fun x=>⟨false,x⟩))
      intro flag l' hl' hn' hf
      apply one_predicted_certificate hε (rows.filter_mono hl')
      cases flag
      · exact one_out_by_cover (hl'.trans ht) hq (H.filter_mono hl') (E.filter_mono hl')
          (one_citable_on hl' hR) hf
      exact one_out_by_mix (hl'.trans ht) hq (H.filter_mono hl') (E.filter_mono hl')
        (one_citable_on hl' hR) hf
    let reciprocal := b.c=twinned ∨ ∃ i,b.c=dawn i ∧ b.α i=1
    let zeroClass := reciprocal ∨ b.c=dusk ∧ b.r=0
    let smallSpan n := ∃ V : Space (Ambient p (2*(M*n))),
      dim V≤(2*(M*n))*onePreparationCover q ∧
      ∀ x,inTiles (s n).T x ∧ P n x → oneMarkedDelta x (b.m n x)∈V
    have fromSpan := dose.crossing_of_span_bound ht hq H E
      (hδ.mono fun _ hn x hx he => hzero ((hn x hx).mpr he))
    let direct n := smallSpan n ∧ (zeroClass ∨ oneHalfCrossing s w P b n ∨ oneIncompatibleSpanBound s w P b n)
    let test (n : ℕ) (i : Bool) := if i then direct n else ¬direct n
    apply bound_on_finite_cases test (fun n=>one_prepared_mono q (m n) (w n))
      (Eventually.of_forall fun n=>by
        by_cases h : direct n
        · exact ⟨true,h⟩
        exact ⟨false,h⟩)
    intro flag u hu _ hf
    have hcite:=one_citable_on hu (dose.citable ht hq.hM)
    cases flag
    · by_cases hc : reciprocal
      · obtain ⟨t,dur,bright,_⟩:=one_drop_harvest (hu.trans ht) hq (H.filter_mono hu)
          (E.filter_mono hu) hcite
        let good n := oneCompatibilityFloor (t n) (w n) (oneMatchProg b n) (1/2) ∧
          oneGleam t w b n≤0.001*oneGlow t w b n
        let passes (n : ℕ) (i : Bool) := if i then good n else ¬good n
        apply bound_on_finite_cases passes (fun n=>one_prepared_mono q (m n) (w n))
          (Eventually.of_forall fun n=>by
            by_cases h : good n
            · exact ⟨true,h⟩
            exact ⟨false,h⟩)
        intro check l' hl' _ hpass
        have hlim:=hl'.trans hu
        cases check
        · exact remaining l' hlim
        obtain ⟨a,ha,hret⟩:=dur.retained
        have dur' : OneDurable q l' m w t := ⟨fun ε h=>(dur.mass ε h).filter_mono hl',
          dur.shape.filter_mono hl',a,ha,hret.filter_mono hl'⟩
        have bright' : OneBright q l' m t b := ⟨⟨fun ε h=>(bright.forecasts.small ε h).filter_mono hl',
          bright.forecasts.light⟩,bright.engraved.filter_mono hl'⟩
        exact one_direct_zero_certificate (hlim.trans ht) hq (H.filter_mono hlim) dur' bright'
          (rows.filter_mono hlim) hε hc (by norm_num : 0<(1/2:ℝ)) hpass
      exact remaining u hu
    apply one_predicted_certificate hε (rows.filter_mono hu)
    have hspan : oneSpannedPopulation q u s P b := hf.mono fun _ h => h.1
    by_cases hclass : zeroClass
    · rcases hclass with hc|⟨hd,hr⟩
      · exact one_zero_parity_outcome (hu.trans ht) hq (H.filter_mono hu) (E.filter_mono hu)
          hcite (one_coded_of_span hspan) hc
      exact one_four_zero_outcome (hu.trans ht) hq (H.filter_mono hu) (E.filter_mono hu)
        hcite hspan hd hr
    have hasOne : (∃ i,b.c=dawn i ∧ b.α i=0) ∨ b.c=dusk ∧ b.r=1 := by
      cases h : b.c with
      | noon => exact (hfree (hc.symm.trans h)).elim
      | twinned => exact (hclass (Or.inl (Or.inl h))).elim
      | dusk => exact Or.inr ⟨rfl,(bit_cases b.r).resolve_left fun hr => hclass (Or.inr ⟨h,hr⟩)⟩
      | dawn i => exact Or.inl ⟨i,rfl,(bit_cases (b.α i)).resolve_right fun ha =>
          hclass (Or.inl (Or.inr ⟨i,h,ha⟩))⟩
    exact one_prescribed_one_outcome (hu.trans ht) hq (H.filter_mono hu) (E.filter_mono hu)
      hcite hspan hasOne ((hf.and (fromSpan.filter_mono hu)).mono fun _ h =>
        (h.1.2.resolve_left hclass).elim id h.2)

/-- One positive quota and one starting dimension work for every admissible
law. At each size take a law failing the largest integer quota index up to n,
if such a law exists. Any bound for this choice works for all the laws. -/
theorem one_finite_preparation (hq : OnePlanted q p M) :
    ∃ k,∀ᶠ n : ℕ in atTop,∀ (m : Mixer p n) (w : Wgt (OneUnit p n (M*n)))
      (s : OneLeafMixture p n (M*n)),OneNascent q m w → OneEntered q m w s →
      OnePreparedAt q m w k := by
  classical
  let bad (n k : ℕ) := ∃ (m : Mixer p n) (w : Wgt (OneUnit p n (M*n)))
    (s : OneLeafMixture p n (M*n)),OneNascent q m w ∧ OneEntered q m w s ∧ ¬OnePreparedAt q m w k
  let j n := Nat.findGreatest (bad n) n
  let v : Filter ℕ := atTop ⊓ principal {n | bad n (j n)}
  have hb : ∀ᶠ n in v,bad n (j n) :=
    (eventually_principal.mpr (show ∀ n∈{n | bad n (j n)},bad n (j n) from fun _ h=>h)).filter_mono inf_le_right
  let (n : ℕ) : Nonempty (Mixer p n) := ⟨⟨0,0,0⟩⟩
  obtain ⟨m,hm⟩:=taking hb
  obtain ⟨w,hw⟩:=taking hm
  obtain ⟨s,hs⟩:=taking hw
  obtain ⟨k,hk⟩:=one_preparation_cases (l:=v) inf_le_left hq
    (hs.mono fun _ h=>h.1) (hs.mono fun _ h=>h.2.1)
  have hunif : ∀ᶠ n in v,¬bad n k := by
    filter_upwards [hk,hs,(eventually_ge_atTop k).filter_mono (show v≤atTop from inf_le_left)]
      with n hn hs hsize hbad
    exact hs.2.2 (one_prepared_mono q (m n) (w n) (Nat.le_findGreatest hsize hbad) hn)
  have htotal := eventually_inf_principal.mp hunif
  refine ⟨k,?_⟩
  filter_upwards [htotal,eventually_ge_atTop k] with n hn hsize m w s hw hs
  by_contra h
  have hbad : bad n k := ⟨m,w,s,hw,hs,h⟩
  exact hn (Nat.findGreatest_spec hsize hbad) hbad

end
end Lax793645Proofs.Simplifications
