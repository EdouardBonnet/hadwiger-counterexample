import Lax793645Proofs.Simplifications.OneFiniteReferenceGap
import Lax793645Proofs.Simplifications.OnePredictionClassification

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {U : Ultrafilter ℕ}

theorem one_literal_silent (o : OneOrient p n N) (g : OneAugur p N)
    (v : Pdual p n) (E : Finset (Label p.b)) (r : F)
    (hE : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hg : Odd p.g) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (hlit : oneLiteral g r) (h : onePostulates o g v E 0) :
    r=0 ∧ silent v := by
  apply exact_vat v E r hE hg hn hr
  intro l a ha
  have hh:=h a ha l Flavor.full
  have he : oneMismatch g v l a Flavor.full o=
      (fun x=>v (useAtom p l a Flavor.full x)≠r*dialed p l Flavor.full x) := by
    funext x
    unfold oneMismatch
    rw [hlit]
  rw [he] at hh
  exact hh.trans_lt (by norm_num)

/-- Exact bounded-coordinate predictions are classified by literal
equalities. The only finite selection chooses one of five classes; no
sequence of disagreement thresholds or additional trimming is used. -/
theorem one_exact_cohorts_to_dose (hl : (U:Filter ℕ)≤atTop)
    (hq : OnePlanted q p M) (R : ℕ)
    (h : ∀ᶠ n in U,∃ (z : OneBanners) (i : OneSage p n (M*n)),
      OneAlgebraicRows i.g R ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
        crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z 0)) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),
      OneDosed q (U:Filter ℕ) m w s b P ∧
      (∀ᶠ n in U, OneAlgebraicRows (fun j=>b.g j n) R ∧ oneFiniteClass (fun j=>b.g j n) b.α=b.c) ∧
      (i=true→b.α true=b.α false) ∧
      ∀ᶠ n in U,∀ x,P n x→((i=true)↔oneMarkedDelta x (b.m n x)=0) := by
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
  obtain ⟨z,hz⟩:=Ultrafilter.eventually_exists_iff.mp (show ∀ᶠ n in U,∃ z i,T n z i from h)
  obtain ⟨i,hi⟩:=taking hz
  obtain ⟨c,hc⟩:=Ultrafilter.eventually_exists_iff.mp
    (show ∀ᶠ n in U,∃ c,oneFiniteClass (i n).g z.1=c from
      Eventually.of_forall fun n=>⟨_,rfl⟩)
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
  have hledger : OneLedger b (U:Filter ℕ) := ⟨fun ε hε => Eventually.of_forall (fun _=>hε.le),hlit⟩
  refine ⟨b,P,z.2.2,⟨hledger,?_,hi.mono (fun _ hn=>hn.2.1),?_⟩,
    (hi.and hc).mono (fun _ hn=>⟨hn.1.1,hn.2⟩),hconsistent,Eventually.of_forall (fun _ _ hx=>hx.2.2)⟩
  · filter_upwards [hi] with n hn
    exact (show pollen≤crowdSeed by unfold crowdSeed; linarith only [pollen_pos]).trans hn.2.2.2
  · filter_upwards [hc,(eventually_ge_atTop (2*p.r)).filter_mono hl] with n hc hn x hx
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

end
end Lax793645Proofs.Simplifications
