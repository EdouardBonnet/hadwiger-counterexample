import Lax342547.LeafBlockCaps
import Lax342547.PinLabelExclusions
import Lax342547.FrozenCellDirections
import Lax342547.PinReindexing

/-!
---
title: Both actual cross orientations have retained-cell image entropy
type: lemma
---
Actual query-key independence and the exact leaf caps give all-rank matrix-image bounds on the original retained cells. Reindexing the second nominal orientation preserves ranks and uses the same key-slot exponent.
-/

namespace Lax342547.RawCellEntropy

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.ReferencePins Lax342547.JoinedRecords Lax342547.ExactPins Lax342547.KeySpans
open Lax342547.RawQueryImages Lax342547.RealCellLaws Lax342547.ComponentCharacters
open Lax342547.PrimalGramTests
open scoped ENNReal

axiom left_cell_block_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr) (p : PMF (Unit (H := H) (N := N) (E := M)))
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (q : Lax342547.ReferenceKeys.Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (C : Unit (H := H) (N := N) (E := M) → Prop) (hCkey : ∀ o, C o → leftTuple W o = q)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1/1000)
    (hk : 2*ζ*Fintype.card (Lax342547.QuerySlots.Slot W) ≤ (1/500 : ℝ))
    (hCmass : (2 : ℝ)^(-((Fintype.card (Lax342547.QuerySlots.Slot W) : ℝ)+1/100)*Fintype.card N) ≤
      (p.toOuterMeasure {o | C o}).toReal)
    (hcap : ∀ Q : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event observation) ≤ ((2 : ℝ≥0∞)^(-(1-2*ζ)*Fintype.card N))^(P.relativeRank Q))
    (ranks : Lax342547.CutProfiles.Component (Tag k) × Bool → ℕ)
    (F : ∀ a, Matrix (Fin 2 × (Coordinate k n b degree ⊕ H)) (Fin (ranks a)) Binary)
    (hF : ∀ a, Function.Injective ((joined P (fun a => keyMap (H := H) W a.1) a).mkQ.comp (F a).mulVecLin))
    (y : ((Σ a, Fin (ranks a)) × N) → Binary) : by
      classical
      exact Lax342547.PushforwardWalsh.push (subtypeWeights (weights p) C)
        (fun o => blockImage F (leftMatrices o.val)) y ≤
          (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, ranks a)*Fintype.card N))

axiom right_cell_block_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr) (p : PMF (Unit (H := H) (N := N) (E := M)))
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.right i z t).label ∉ A z)
    (q : Lax342547.ReferenceKeys.Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (C : Unit (H := H) (N := N) (E := M) → Prop) (hCkey : ∀ o, C o → rightTuple W o = q)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1/1000)
    (hk : 2*ζ*Fintype.card (Lax342547.QuerySlots.Slot W) ≤ (1/500 : ℝ))
    (hCmass : (2 : ℝ)^(-((Fintype.card (Lax342547.QuerySlots.Slot W) : ℝ)+1/100)*Fintype.card N) ≤
      (p.toOuterMeasure {o | C o}).toReal)
    (hcap : ∀ Q : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event observation) ≤ ((2 : ℝ≥0∞)^(-(1-2*ζ)*Fintype.card N))^(P.relativeRank Q))
    (ranks : Lax342547.CutProfiles.Component (Tag k) × Bool → ℕ)
    (F : ∀ a, Matrix (Fin 2 × (Coordinate k n b degree ⊕ H)) (Fin (ranks a)) Binary)
    (hF : ∀ a, Function.Injective ((joined (Lax342547.PinReindexing.pull Lax342547.PinReindexing.opposite P)
      (fun a => keyMap (H := H) (Lax342547.PairedRecipes.flip W) a.1) a).mkQ.comp (F a).mulVecLin))
    (y : ((Σ a, Fin (ranks a)) × N) → Binary) : by
      classical
      exact Lax342547.PushforwardWalsh.push (subtypeWeights (weights p) C)
        (fun o => blockImage F (rightMatrices o.val)) y ≤
          (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, ranks a)*Fintype.card N))

end Lax342547.RawCellEntropy
