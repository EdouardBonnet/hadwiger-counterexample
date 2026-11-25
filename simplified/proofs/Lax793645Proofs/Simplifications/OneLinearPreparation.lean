import Lax793645Proofs.Simplifications.OneExactPreparedOutcomes
import Lax793645Proofs.Simplifications.OneExactPreparation
import Lax793645Proofs.Simplifications.OneGenericInputs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ} {q : PreparationParameters} {l : Filter ℕ}
  {m : cycleM p} {w : OneTale p M} {s : OneRhythms p M} {U : Ultrafilter ℕ}
  {b : OneSketch p M}

def oneBoundedLinearAugurs (p : Shape) (n N : ℕ) (g : Bool→OneAugur p N):=
  ∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (g i) R

def oneBoundedLinearPredicts (q : PreparationParameters) (m : Mixer p n)
    (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N)) (ε : ℝ):=
  ∃ g : Bool→OneAugur p N,oneBoundedLinearAugurs p n N g ∧
    (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,oneGenericSeems q m s x g z L α ε)

def oneLinearLedger (q : PreparationParameters) (b : OneSketch p M) (l : Filter ℕ) :=
  ∀ᶠ n in l, OneAlgebraicRows (fun i=>b.g i n) (exactPredictorRows p q) ∧
    oneFiniteClass (fun i=>b.g i n) b.α=b.c

def oneLinearSilenceOutcome (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M):=
  ∃ ε : ℝ,0≤ε ∧ ∀ᶠ n in l,
    ¬oneBoundedLinearPredicts q (m n) (s n) (w n) ε ∧
      0.99<pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (oneSecureAt (s n))

def oneLinearPredOutcome (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M):=
  ∃ b : OneSketch p M,oneLinearLedger q b l ∧ OneBright q l m s b ∧
    (oneGlowOutcome l w s b ∨ oneGlimmer q l w s b)

def oneLinearSatisfied (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M):=
  ∃ s : OneRhythms p M,OneDurable q l m w s ∧
    (oneLinearSilenceOutcome q l m w s ∨ oneLinearPredOutcome q l m w s)

def oneLinearOutlook (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M):=
  ∀ᶠ n in l,oneBoundedLinearPredicts q (m n) (s n) (w n) 0

theorem one_linear_eclipse (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n)) :
    oneLinearSilenceOutcome q (U:Filter ℕ) m w s ∨
      oneLinearOutlook q (U:Filter ℕ) m w s := by
  classical
  by_cases he : ∀ᶠ n in U,oneBoundedLinearPredicts q (m n) (s n) (w n) 0
  · exact Or.inr he
  exact Or.inl ⟨0,le_rfl,
    (Ultrafilter.eventually_not.mpr he).and
      (((one_retain_initial hl hq hx).unconditional hl hq hw).mono fun n hn=>hn.2)⟩

theorem one_linear_outlook_to_dose (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n))
    (h : oneLinearOutlook q (U:Filter ℕ) m w s) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),
      OneDosed q (U:Filter ℕ) m w s b P ∧ oneLinearLedger q b (U:Filter ℕ) ∧
        (i=true→b.α true=b.α false) ∧
        ∀ᶠ n in U,∀ x,P n x → ((i=true)↔oneMarkedDelta x (b.m n x)=0) :=
by
  apply one_algebraic_prediction_dose hl hq hw hx
  filter_upwards [h] with n hn
  obtain ⟨g,hg,hmass⟩:=hn
  refine ⟨g,hg,?_⟩
  simpa only [one_generic_seems_zero_iff] using hmass

theorem one_finished_linear (hlin : oneLinearLedger q b l) (h : oneFinished q l m w b) :
    oneLinearSatisfied q l m w := by
  obtain ⟨s,hs,hb,hout⟩:=h
  exact ⟨s,hs,Or.inr ⟨b,hlin,hb,hout⟩⟩

set_option maxHeartbeats 1000000 in
/-- Preparation for the actual one-frame construction. The same bounded
linear predictors survive classification, exactification, phase restriction,
cover pinning, and the zero-discrepancy contradiction. -/
theorem one_prepare_linear (U : Ultrafilter ℕ) (hl : (U:Filter ℕ)≤atTop)
    (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n)) :
    oneLinearSatisfied q (U:Filter ℕ) m w := by
  classical
  rcases one_linear_eclipse hl hq hw hx with hn|hn
  · exact ⟨s,one_retain_initial hl hq hx,Or.inl hn⟩
  obtain ⟨b,P,i,hQ,hlin,hα,hz⟩:=one_linear_outlook_to_dose hl hq hw hx hn
  cases i
  · obtain ⟨R,hR,hT⟩:=one_phase_split hl hq hw hx hQ
      (hz.mono fun n hn x hx he=>Bool.false_ne_true ((hn x hx).mpr he))
    rcases Ultrafilter.eventually_or.mp hT with hF|hF
    · exact one_finished_linear hlin (one_out_by_mix hl hq hw hx hR hF)
    exact one_finished_linear hlin (one_out_by_cover hl hq hw hx hR hF)
  exact one_finished_linear hlin (one_phase_absent_exact hl hq hw hx hQ (hα rfl)
    (hz.mono fun n hn x hx=>(hn x hx).mp rfl))

end
end Lax793645Proofs.Simplifications
