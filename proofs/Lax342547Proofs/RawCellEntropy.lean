import Lax342547.RawCellEntropy
import Lax342547Proofs.LeafBlockCaps
import Lax342547Proofs.PinLabelExclusions
import Lax342547Proofs.FrozenCellDirections
import Lax342547Proofs.PinReindexing

namespace Lax342547Proofs.RawCellEntropy
open Lax342547.RawCellEntropy

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.ReferencePins Lax342547.JoinedRecords Lax342547.ExactPins Lax342547.KeySpans
open Lax342547.RawQueryImages Lax342547.RealCellLaws Lax342547.ComponentCharacters
open Lax342547.PrimalGramTests
open scoped ENNReal

/--
---
conclusion: Lax342547.RawCellEntropy.left_cell_block_cap
---
-/
theorem left_cell_block_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
          (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, ranks a)*Fintype.card N)) := by
  classical
  have h := Lax342547Proofs.LeafBlockCaps.original_leaf_all_rank_block_cap p leftMatrices P
    (fun a => keyMap (H := H) W a.1) ranks F
    (Lax342547Proofs.QueryIndependence.actual_key_independence W P A hA hfresh) hF
    (tupleMaps W q) C
    (fun o ho => (Lax342547Proofs.RawQueryImages.left_tuple_event W q o).mp (hCkey o ho))
    ζ hζ hζsmall (by rw [Lax342547Proofs.RawQueryImages.key_dimension]; exact hk)
    (by simpa only [Lax342547Proofs.RawQueryImages.key_dimension] using hCmass)
    hcap y
  simpa only [mul_assoc] using h

/--
---
conclusion: Lax342547.RawCellEntropy.right_cell_block_cap
---
-/
theorem right_cell_block_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
          (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, ranks a)*Fintype.card N)) := by
  classical
  have hkeys (a : Lax342547.CutProfiles.Component (Tag k) × Bool) :
      Function.Injective (((Lax342547.PinReindexing.pull Lax342547.PinReindexing.opposite P).space a).mkQ.comp
        (keyMap (H := H) (Lax342547.PairedRecipes.flip W) a.1)) :=
    Lax342547Proofs.QueryIndependence.actual_key_independence (Lax342547.PairedRecipes.flip W) P A hA
      (fun i z t => hfresh z i t) (a.1,!a.2)
  have hknown (o : Unit (H := H) (N := N) (E := M)) (ho : C o)
      (a : Lax342547.CutProfiles.Component (Tag k) × Bool) :
      (rightMatrices o a).mulVecLin.comp (keyMap (H := H) (Lax342547.PairedRecipes.flip W) a.1) =
        tupleMaps (Lax342547.PairedRecipes.flip W) (Lax342547.RightQueryImages.reindexTuple W q) (a.1,!a.2) := by
    have ht : leftTuple (Lax342547.PairedRecipes.flip W) o = Lax342547.RightQueryImages.reindexTuple W q := by
      rw [Lax342547Proofs.RightQueryImages.left_flip_right_tuple, hCkey o ho]
    exact (Lax342547Proofs.RawQueryImages.left_tuple_event (Lax342547.PairedRecipes.flip W)
      (Lax342547.RightQueryImages.reindexTuple W q) o).mp ht (a.1,!a.2)
  have h := Lax342547Proofs.LeafBlockCaps.original_leaf_all_rank_block_cap p rightMatrices
    (Lax342547.PinReindexing.pull Lax342547.PinReindexing.opposite P)
    (fun a => keyMap (H := H) (Lax342547.PairedRecipes.flip W) a.1) ranks F hkeys hF
    (fun a => tupleMaps (Lax342547.PairedRecipes.flip W) (Lax342547.RightQueryImages.reindexTuple W q) (a.1,!a.2))
    C hknown ζ hζ hζsmall
    (by rw [Lax342547Proofs.RawQueryImages.key_dimension, Lax342547Proofs.RightQueryImages.flipped_slot_count]; exact hk)
    (by simpa only [Lax342547Proofs.RawQueryImages.key_dimension,
      Lax342547Proofs.RightQueryImages.flipped_slot_count] using hCmass)
    (Lax342547Proofs.PinReindexing.leaf_cap_reindex Lax342547.PinReindexing.opposite p observation P
      ((2 : ℝ≥0∞)^(-(1-2*ζ)*Fintype.card N)) hcap) y
  simpa only [mul_assoc] using h

end Lax342547Proofs.RawCellEntropy
