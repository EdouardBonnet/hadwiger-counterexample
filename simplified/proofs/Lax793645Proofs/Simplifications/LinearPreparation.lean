import Lax793645Proofs.Simplifications.LinearPredictionConditions
import Lax793645Proofs.Simplifications.LinearPreparedConsistency
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionDichotomy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ} {q : PreparationParameters} {l : Filter ℕ}
  {m : cycleM p} {w : tale p M} {s : rhythms p M} {U : Ultrafilter ℕ}
  {b : Sketch p M}

/-- Combining the two endpoints and all tags uses at most `2*g*R`
frequencies. This budget leaves the joint frequency dimension at most n/4. -/
def boundedLinearAugurs (p : Shape) (n N : ℕ) (g : Bool→Augur p N) :=
  ∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,LinearAugur (g i) R

def boundedLinearPredicts (q : PreparationParameters) (p : Shape) (N : ℕ) {n : ℕ}
    (m : Mixer p n) (s : LeafMixture p n N) (w : Wgt (UnitType p n N)) (ε : ℝ) :=
  ∃ R : ℕ,8*p.g*R≤n ∧ linearPredicts q p N m s w R ε

theorem bounded_linear_predicts_witness (m : Mixer p n) (s : LeafMixture p n N)
    (w : Wgt (UnitType p n N)) (ε : ℝ) :
    boundedLinearPredicts q p N m s w ε ↔
      ∃ g : Bool→Augur p N,boundedLinearAugurs p n N g ∧
        (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,q.seems p m s x g z L α ε) := by
  constructor
  · rintro ⟨R,hR,g,hlin,hg⟩
    exact ⟨g,⟨R,hR,hlin⟩,hg⟩
  · rintro ⟨g,⟨R,hR,hlin⟩,hg⟩
    exact ⟨R,hR,g,hlin,hg⟩

def linearLedger (b : Sketch p M) (l : Filter ℕ) :=
  ∀ᶠ n in l,boundedLinearAugurs p n (M*n) (fun i=>b.g i n)

def linearSilenceOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape)
    (M : ℕ) (m : cycleM p) (w : tale p M) (s : rhythms p M) :=
  ∃ ε : ℝ,0<ε ∧ ∀ᶠ n in l,
    ¬boundedLinearPredicts q p (M*n) (m n) (s n) (w n) ε ∧
      0.99<pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (secureAt p (s n).rooting)

def linearPredOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape)
    (M : ℕ) (m : cycleM p) (w : tale p M) (s : rhythms p M) :=
  ∃ b : Sketch p M,linearLedger b l ∧ q.bright l p M m s b ∧
    (glowOutcome l p M w s b ∨ q.glimmer l p M w s b)

def linearSatisfied (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) :=
  ∃ s : rhythms p M,q.durable l p M m w s ∧
    (linearSilenceOutcome q l p M m w s ∨ linearPredOutcome q l p M m w s)

def linearOutlook (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) :=
  ∃ ε : ℕ→ℝ,slight l ε ∧ ∀ᶠ n in l,
    boundedLinearPredicts q p (M*n) (m n) (s n) (w n) (ε n)

theorem linear_eclipse (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    linearSilenceOutcome q (U:Filter ℕ) p M m w s ∨
      linearOutlook q (U:Filter ℕ) p M m w s := by
  classical
  let P (n : ℕ) ε:=boundedLinearPredicts q p (M*n) (m n) (s n) (w n) ε
  let c (i : ℕ):=((i:ℝ)+1)⁻¹
  by_cases he : ∀ k : ℕ,∀ᶠ n in U,P n (c k)
  · obtain ⟨k,h1,h2⟩:=diagonal_gains (U:Filter ℕ) hl (fun i j=>P i (c j)) he
    exact Or.inr ⟨fun i=>c (k i),slight_inv_stage h1,h2⟩
  push Not at he
  obtain ⟨k,hk⟩:=he
  exact Or.inl ⟨c k,by unfold c; positivity,
    hk.and (((retainInitial hl hq hx).unconditional hl hq hw).mono fun i hi=>hi.2)⟩

/-- The coordinate invariant follows the same chosen functions through
classification and exactification, independently of the trimming event. -/
theorem linear_outlook_to_dose (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (h : linearOutlook q (U:Filter ℕ) p M m w s) :
    ∃ (b : Sketch p M) (P : Campaign p M) (i : Bool),
      q.dosed (U:Filter ℕ) p M m w s b P ∧ linearLedger b (U:Filter ℕ) ∧
        ∀ᶠ n in U,∀ x,P n x → ((i=true) ↔ delta (b.m n) x=0) := by
  obtain ⟨ε,hε,h⟩:=h
  apply outlook_to_dose_preserving hl hq hw hx
    (fun n g=>boundedLinearAugurs p n (M*n) g)
  exact ⟨ε,hε,h.mono (fun n hn=>(bounded_linear_predicts_witness _ _ _ _).mp hn)⟩

theorem finished_linear (hlin : linearLedger b l) (h : finished q l p M m w b) :
    linearSatisfied q l p M m w := by
  obtain ⟨s,hs,hb,hout⟩:=h
  exact ⟨s,hs,Or.inr ⟨b,hlin,hb,hout⟩⟩

set_option maxHeartbeats 1600000 in
/-- Preparation restricted to certified predictors. The same certificate
survives both the phase and cover branches and the zero-discrepancy branch. -/
theorem prepare_linear (U : Ultrafilter ℕ) (hl : (U:Filter ℕ)≤atTop)
    (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    linearSatisfied q (U:Filter ℕ) p M m w := by
  classical
  rcases linear_eclipse hl hq hw hx with hn|hn
  · exact ⟨s,retainInitial hl hq hx,Or.inl hn⟩
  obtain ⟨b,P,i,hQ,hlin,hz⟩:=linear_outlook_to_dose hl hq hw hx hn
  cases i
  · obtain ⟨R,hR,hT⟩:=phaseSplit hl hq hw hx hQ
      (hz.mono fun n hn i hi x h hh ht=>Bool.false_ne_true ((hn x hh).mpr ht))
    rcases Ultrafilter.eventually_or.mp hT with hF|hF
    · exact finished_linear hlin (outByMix_fixed hl hq hw hx hR hF)
    exact finished_linear hlin (outByCover_fixed hl hq hw hx hR hF)
  exact finished_linear hlin (phaseAbsent_linear_fixed hl hq hw hx hQ hlin
    (hz.mono fun n hn i hi x h hh=>(hn x hh).mp rfl))

end
end Lax793645Proofs.Simplifications
