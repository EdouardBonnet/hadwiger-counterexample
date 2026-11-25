import Lax793645.ConstructionData

/-!
---
title: Seven possible pairs of common predictors
type: lemma
---
Fix the second unit. An exact nonzero dual relation forces the first unit to use a
pair of predictors from a catalogue of at most 7. Its members are the zero function
and the two canonical predictors of the fixed unit in their allowed positions.
-/

namespace Lax793645.SevenPredictions

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}

axiom exact_seven_alternative {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    {β δ : ℝ} (hg : 3≤ p.g) (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ) (hβ : 0<β)
    (B : ℕ) (hB : B< Fintype.card (Label p.b))
    (Free : Pulsar p r→ Prop) (hzero : Free 0) (hsep : TesterSeparated u Free)
    (hnormS : ∀ i E,E.card≤ B→∀ w α f,
      ExactStatusPrediction u s i E (yokeSet w α) f→ Free f)
    (hnormT : ∀ i E,E.card≤ B→∀ w α f,
      ExactStatusPrediction u t i E (yokeSet w α) f→ Free f)
    (catS catT : Nodes→ Pulsar p r)
    (hcatS : ExactCatalog u s B catS) (hcatT : ExactCatalog u t B catT)
    (hfreeS : ∀ i,Free (catS i)) (hfreeT : ∀ i,Free (catT i))
    (E G : Stalls p) (hE : ∀ i,(E i).card≤ B) (hF : ∀ i,(G i).card≤ B)
    (z : DualCoefficients d e) (hz : z.left≠0 ∨ z.right≠0)
    (hpred : ∀ i : Grid,∃ f : Pulsar p r,
      ExactStatusPrediction u s i.1 (E i.1) (leftChime z i) f ∧
      ExactStatusPrediction u t i.2 (G i.2) (rightChime z i) f) :
    ExactAnnounced u s catT B ∨ ExactAnnounced u t catS B

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}

axiom seven_prediction_pairs_card (f : Nodes→ Pulsar p r) :
    (sevenPredictionPairs f).card≤7

end

end Lax793645.SevenPredictions
