import Lax793645.ConstructionData

/-!
---
title: Positive mass of soluble scalar systems
type: lemma
---
In the branch without a common prediction, safe pairs outside the exceptional sets
have soluble scalar targets. Hence the estimates suppressing all eligible options and
the absence of common predictions cannot hold together.
-/

namespace Lax793645.SolublePairs

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
open StatusAnalysis
open PreparationParameters PredictionClass Club Guild DualAnalysis
open Lax793645.ConstructionData.Frames.OneExactOptions
variable {p : Shape} {n N M r s0 K coords : ℕ} {w:OneLeafMixture p n N} {b:PreparationParameters}

axiom no_out (w:OneLeafMixture p n N) (b:PreparationParameters)
    (m:Mixer p n) (Y:OneSilhouette p N r) (U:Wgt (OneUnit p n N))
    (v:OneStation p n N (onePreparationPins b) w) (ε η a δ τ:ℝ)
    (h:OneLead U w m b.leafNew (2* b.ζ) (onePreparationPins b)) (ht:v.bank) (he:OneAnalyticParameters p M b s0) (hn:2* p.r≤ n)
    (hp:Jubilee p (onePreparationPins b) ε η) (hε:0<ε)
    (hB:oneSupportBudget p (onePreparationPins b) η a)
    (hv:OneGenericBeams m Y w U v a ε δ (1/16))
    (hYlinear:OneLinearSilhouette Y coords) (hcoords:8* p.g* coords≤ n)
    (hτ : 0≤τ)
    (H : Space (OneJointKey p N))
    (hgood : pr (w.sap U) (fun o=>¬OnePaletteGood H o)≤1/16)
    (hgap : ∀ o o',OnePaletteGood H o→ OnePaletteGood H o'→
      OneFullTableGap Y m (onePreparationPins b) o o')
    (hnorm : ∀ o : OneUnit p n N,OnePaletteGood H o→∀ d : Rates,∀ v : Charts p n d,
      (∀ i z,totalRank (v i z)≤ onePreparationPins b)→
      ∀ i E,E.card≤ b.B→∀ z α f,
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E (yokeSet z α) f→
        OneTesterFree Y f ∧
        onePostulates (o i) (oneFromPulse Y f) (oneYoke m o i (v i z) α) ∅ 0)
    (hcontinue : ∀ o : OneUnit p n N,OnePaletteGood H o→ OneGenericStatusContinues Y m b.B o)
    (hη : η≤ bp (-(4*(oneStatusCoordinateBound p ((onePreparationPins b)^2)
      (onePreparationPins b):ℝ)+1)))
    (hsep : TesterSeparated (oneWisp p Y) (OneTesterFree Y))
    (hh:¬oneBoundedLinearPredicts b m w U τ)
    (hu:0.99 < pr (pairW (w.sap U) (w.sap U)) (oneSecureAt w)) :
    False

end

end Lax793645.SolublePairs
