import Lax793645.ConstructionData

/-!
---
title: How often a dual obstruction can occur
type: lemma
---
In the absence of a common prediction on the required mass, any one catalogue predicts
on at most $0.001$ of the units. Applying this in both directions bounds the mass of
good pairs with a dual relation by $0.002$.
-/

namespace Lax793645.RareObstructions

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

axiom witnessed_cost (w : OneLeafMixture p n N)
    (v : OneStation p n N (onePreparationPins b) w) (L : OneLoupe w (onePreparationPins b))
    (h : OneShipped w (onePreparationPins b) v L) (m : Mixer p n)
    (Y : OneSilhouette p N r) (H : Space (OneJointKey p N))
    (a : ℝ) (U : Wgt (OneUnit p n N)) (cat : Nodes→ Pulsar p r)
    (hp : OneLead U w m b.leafNew (2* b.ζ) (onePreparationPins b)) (ha : 0≤ a)
    (hnorm : ∀ x : OneAspect w,OnePaletteGood H x.2→∀ i E,E.card≤ b.B→∀ u α f,
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m x.2 (oneRouteC L v x))
        i E (yokeSet u α) f→
        onePostulates (x.2 i) (oneFromPulse Y f)
          (oneYoke m x.2 i (oneRouteC L v x i u) α) ∅ 0)
    (hYlinear : OneLinearSilhouette Y coords) (hcoords : 8* p.g* coords≤ n)
    (hy : ¬oneBoundedLinearPredicts b m w U a) :
    pr (oneTroupe w U) (witnessed w v L m Y H b.B cat)≤0.001

end

end Lax793645.RareObstructions
