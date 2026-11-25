import Lax793645.ConstructionData

/-!
---
title: Solving the scalar system with exact predictors
type: lemma
---
For compatible frames with a safe table, the attained pairs of predictor values
suffice to solve the scalar system. All attained pairs are kept on both diagonal
slices.
-/

namespace Lax793645.PredictedScalarSystem

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass
open Finset Matrix Function
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N r:ℕ} {A B:Rates}

axiom one_attained_scalar_soluble (g : Bool→ OneAugur p N) (α : Party)
    (c : PredictionClass) (hc : oneFiniteClass g α=c) {R : ℕ} (hrows : OneAlgebraicRows g R)
    (X : ∀ i,Cell (A i)) (Z : ∀ i,Cell (B i)) (η : ℝ)
    (hmass : ∀ l q x, η≤ oneWisp p (onePredictorPartition c g) l q
      (onePredictorPartition c g l q x))
    (m : OneUnit p n N→ Bool→ Profile p n)
    (x y : OneUnit p n N) (T : OneCross p n) (s : Charts p n A) (t : Charts p n B)
    (hx : oneCoordSpec m x s X) (hy : oneCoordSpec m y t Z) (hg : 3≤ p.g)
    (he : glint p (m x)=glint p (m y))
    (hcompat : c.compatible α (glint p (m x)) (oneCardTone m x T,
      oneCardTone m y (fun e=>(T e)ᵀ))) :
    scorecard (fun i => predictedSpan (α i.1) (α i.2) (X i.1) (Z i.2)
      (retainedPatterns (oneWisp p (onePredictorPartition c g)) (predictorPulse c) η i))
      (oneHailing s t T)

end

end Lax793645.PredictedScalarSystem
