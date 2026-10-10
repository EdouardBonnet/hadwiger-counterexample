import Lax342547.ActualCellCollision
import Lax342547Proofs.RawCellEntropy
import Lax342547Proofs.CellRepresentatives
import Lax342547Proofs.GradientRealization

import Lax342547Proofs.RawRetainedCells
import Lax342547Proofs.ConditionalPairs

namespace Lax342547Proofs.ActualCellCollision
open Lax342547.ActualCellCollision

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.ReferencePins Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.RawBaselines Lax342547.JoinedRecords Lax342547.RealCellLaws Lax342547.FrozenCellDirections
open Lax342547.TableContractions Lax342547.KeySpans Lax342547.PrimalGramTests Lax342547.HoleRelation
open scoped ENNReal

/--
---
conclusion: Lax342547.ActualCellCollision.realized_conditional_four_holes
---
-/
theorem realized_conditional_four_holes {k n b degree r J K : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (hk0 : 0 < k) (W : Lists k n b degree r hr) (pA pB : PMF (Unit (H := H) (N := N) (E := M)))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hP : P.rank ≤ K) (hQ : Q.rank ≤ K)
    (A B : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2*K+28))
    (hB : Lax342547.PinLabelExclusions.Covers Q B (2*K+28))
    (C D : Unit (H := H) (N := N) (E := M) → Prop)
    (refA refB : Unit (H := H) (N := N) (E := M)) (hAr : C refA) (hBr : D refB)
    (hC : ∀ o, C o → o ∈ P.event observation ∧ leftTuple W o = leftTuple W refA ∧
      leftRecord W Q refB o = leftRecord W Q refB refA)
    (hD : ∀ o, D o → o ∈ Q.event observation ∧ rightTuple W o = rightTuple W refB ∧
      rightRecord W P refA o = rightRecord W P refA refB)
    (hkey : leftTuple W refA = rightTuple W refB)
    (testers : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (holes : HoleData (Component (Tag k) → Lax342547.RawFrames.Frame (Coordinate k n b degree) H N M)
      (Profile k n b degree) (Component (Tag k) → Matrix N N Binary))
    (hrole : holes.a = testers.role) (hgradient : holes.T = gradient testers L R)
    (hU : ∀ o, holes.U o = (Lax342547.RawFrames.profileMap o).comp (Profile k n b degree).subtype)
    (hu : ∀ o, holes.u o = Lax342547.RawFrames.profileContraction o)
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (hrecipe : ScalarRecipe W testers L R refA refB T A B)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients testers L R
      (endpointAtoms W i) (oppositeP W refB i))
    (hgradients' : ∀ z, Lax342547.ConcreteRecipes.RecipeGradients testers L R
      (endpointAtoms (flip W) z) (oppositeP (flip W) refA z))
    (hadmissible : Lax342547.SmallTables.Admissible T observation observation refA refB)
    (hdegree : 6*(2*K+28)+4 ≤ degree)
    (hmargin : 28*J*Fintype.card (Component (Tag k)) +
      Lax342547.CompressedResidual.quotientBound k b degree K (14*K+140) + 2*K+4*(3*K+28) < 970*r)
    (hchannels : 1000*r ≤ Fintype.card H)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1/1000)
    (hk : 2*ζ*Fintype.card (Lax342547.QuerySlots.Slot W) ≤ (1/500 : ℝ))
    (hmassA : (2 : ℝ)^(-((Fintype.card (Lax342547.QuerySlots.Slot W) : ℝ)+1/100)*Fintype.card N) ≤
      (pA.toOuterMeasure {o | C o}).toReal)
    (hmassB : (2 : ℝ)^(-((Fintype.card (Lax342547.QuerySlots.Slot W) : ℝ)+1/100)*Fintype.card N) ≤
      (pB.toOuterMeasure {o | D o}).toReal)
    (hcapA : ∀ T : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N,
      1 ≤ P.relativeRank T → pA.toOuterMeasure (T.event observation) ≤
        ((2 : ℝ≥0∞)^(-(1-2*ζ)*Fintype.card N))^(P.relativeRank T))
    (hcapB : ∀ T : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N,
      1 ≤ Q.relativeRank T → pB.toOuterMeasure (T.event observation) ≤
        ((2 : ℝ≥0∞)^(-(1-2*ζ)*Fintype.card N))^(Q.relativeRank T))
    (hsmall : (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) ≤
      1/(2 : ℝ)^(16 * Fintype.card (Component (Tag k)) * Fintype.card H * Fintype.card (Coordinate k n b degree)+1)) : by
      classical
      exact 1/(2 : ℝ)^(16 * Fintype.card (Component (Tag k)) * Fintype.card H * Fintype.card (Coordinate k n b degree)+1) ≤
        Lax342547.CellAveraging.pairEventMass
          (Lax342547.RetainedImages.conditionalLaw (weights pA) C)
          (Lax342547.RetainedImages.conditionalLaw (weights pB) D)
          (fun x y => ∀ i z, Hole holes (x i) (y z)) := by
  classical
  rw [← Lax342547Proofs.ConditionalPairs.subtype_pair_event]
  exact Lax342547Proofs.RawRetainedCells.realized_retained_four_holes hk0 W pA pB P Q
    hP hQ A B hA hB C D refA refB hAr hBr hC hD hkey testers L R holes
    hrole hgradient hU hu T hT hrecipe hgradients hgradients' hadmissible hdegree hmargin hchannels
    ζ hζ hζsmall hk hmassA hmassB hcapA hcapB hsmall

end Lax342547Proofs.ActualCellCollision
