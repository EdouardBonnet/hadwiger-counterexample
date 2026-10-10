import Lax342547.RawRetainedCells
import Lax342547Proofs.RawCellEntropy
import Lax342547Proofs.CellRepresentatives
import Lax342547Proofs.GradientRealization

namespace Lax342547Proofs.RawRetainedCells
open Lax342547.RawRetainedCells

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.ReferencePins Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.RawBaselines Lax342547.JoinedRecords Lax342547.RealCellLaws Lax342547.FrozenCellDirections
open Lax342547.TableContractions Lax342547.KeySpans Lax342547.PrimalGramTests Lax342547.HoleRelation
open scoped ENNReal

/--
---
conclusion: Lax342547.RawRetainedCells.retained_four_holes
---
-/
theorem retained_four_holes {k n b degree r J : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr) (pA pB : PMF (Unit (H := H) (N := N) (E := M)))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A) (hB : Excludes Q B)
    (hfresh : FreshAgainst W A B)
    (C D : Unit (H := H) (N := N) (E := M) → Prop)
    (refA refB : Unit (H := H) (N := N) (E := M)) (hAr : C refA) (hBr : D refB)
    (hC : ∀ o, C o → o ∈ P.event observation ∧ leftTuple W o = leftTuple W refA ∧
      leftRecord W Q refB o = leftRecord W Q refB refA)
    (hD : ∀ o, D o → o ∈ Q.event observation ∧ rightTuple W o = rightTuple W refB ∧
      rightRecord W P refA o = rightRecord W P refA refB)
    (hkey : leftTuple W refA = rightTuple W refB)
    (G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hf : Frozen G W P Q refA refB)
    (testers : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (holes : HoleData (Component (Tag k) → Lax342547.RawFrames.Frame (Coordinate k n b degree) H N M)
      (Profile k n b degree) (Component (Tag k) → Matrix N N Binary))
    (hrole : holes.a = testers.role) (hgradient : holes.T = gradient testers L R)
    (hU : ∀ o, holes.U o = (Lax342547.RawFrames.profileMap o).comp (Profile k n b degree).subtype)
    (hu : ∀ o, holes.u o = Lax342547.RawFrames.profileContraction o)
    (hroles : ∀ i z, testers.role (leftWitness W i z) + testers.role (rightWitness W i z) = 1)
    (hleft : ∀ i z x, fullContraction G (Profile k n b degree) i z x =
      (testers.role + gradient testers L R (leftWitness W i z)) x)
    (hright : ∀ i z x, fullContraction G.flip (Profile k n b degree) z i x =
      (testers.role + gradient testers L R (rightWitness W i z)) x)
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
        Lax342547.PairRecovery.pairMass (subtypeWeights (weights pA) C) (subtypeWeights (weights pB) D)
          (fun x y => ∀ i z, Hole holes (x.val i) (y.val z)) := by
  classical
  have hmA : 0 < Lax342547.RetainedImages.cellMass (weights pA) C := by
    rw [Lax342547Proofs.RealCellLaws.event_mass]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hmassA
  have hmB : 0 < Lax342547.RetainedImages.cellMass (weights pB) D := by
    rw [Lax342547Proofs.RealCellLaws.event_mass]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hmassB
  apply Lax342547Proofs.PrimalGramTests.primal_cell_four_holes
    (subtypeWeights (weights pA) C) (subtypeWeights (weights pB) D)
    (fun x => x.val) (fun y => y.val)
    (fun a => joined P (fun a => keyMap (H := H) W a.1) a)
    (fun a => joined (Lax342547.PinReindexing.pull Lax342547.PinReindexing.opposite Q)
      (fun a => keyMap (H := H) (flip W) a.1) a) G
    (Lax342547Proofs.RealCellLaws.subtype_weights_nonneg (weights pA) C (Lax342547Proofs.RealCellLaws.weights_nonneg pA) hmA)
    (Lax342547Proofs.RealCellLaws.subtype_weights_nonneg (weights pB) D (Lax342547Proofs.RealCellLaws.weights_nonneg pB) hmB)
    (Lax342547Proofs.RealCellLaws.subtype_weights_total (weights pA) C hmA)
    (Lax342547Proofs.RealCellLaws.subtype_weights_total (weights pB) D hmB)
    _ _ _ _ W testers L R holes hrole hgradient hU hu _ hroles hleft hright hsmall
  · intro x y a v hv w
    exact Lax342547Proofs.FrozenCellDirections.record_target_oriented W P Q x.val y.val refA refB
      (hC x.val x.property).1 (hC refA hAr).1 (hD y.val y.property).1 (hD refB hBr).1
      (hC x.val x.property).2.1 (hD y.val y.property).2.1
      (hC x.val x.property).2.2 (hD y.val y.property).2.2 G hf a v w (Or.inl hv)
  · intro x y a v w hw
    exact Lax342547Proofs.FrozenCellDirections.record_target_oriented W P Q x.val y.val refA refB
      (hC x.val x.property).1 (hC refA hAr).1 (hD y.val y.property).1 (hD refB hBr).1
      (hC x.val x.property).2.1 (hD y.val y.property).2.1
      (hC x.val x.property).2.2 (hD y.val y.property).2.2 G hf a v w (Or.inr hw)
  · intro ranks F hF y
    exact Lax342547Proofs.RawCellEntropy.left_cell_block_cap W pA P A hA hfresh.1
      (leftTuple W refA) C (fun o ho => (hC o ho).2.1) ζ hζ hζsmall hk hmassA hcapA ranks F hF y
  · intro ranks F hF y
    exact Lax342547Proofs.RawCellEntropy.right_cell_block_cap W pB Q B hB hfresh.2
      (rightTuple W refB) D (fun o ho => (hD o ho).2.1) ζ hζ hζsmall hk hmassB hcapB ranks F hF y
  · intro x y
    apply Lax342547Proofs.QueryReference.tuple_equality_matched_keys
    exact (hC x.val x.property).2.1.trans (hkey.trans (hD y.val y.property).2.1.symm)

/--
---
conclusion: Lax342547.RawRetainedCells.realized_retained_four_holes
---
-/
theorem realized_retained_four_holes {k n b degree r J K : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
        Lax342547.PairRecovery.pairMass (subtypeWeights (weights pA) C) (subtypeWeights (weights pB) D)
          (fun x y => ∀ i z, Hole holes (x.val i) (y.val z)) := by
  classical
  have hkeys : MatchedKeys W refA refB :=
    Lax342547Proofs.QueryReference.tuple_equality_matched_keys W refA refB hkey
  obtain ⟨G,hf,hleft,hright⟩ := Lax342547Proofs.GradientRealization.gradient_realization
    hk0 W testers L R refA refB P Q hP hQ A B hA hrecipe.fresh.1 hB T hT hrecipe hkeys
    hgradients hgradients' hadmissible hdegree hmargin hchannels
  exact retained_four_holes W pA pB P Q A B
    (Lax342547Proofs.PinLabelExclusions.keys_exclusion P A hA)
    (Lax342547Proofs.PinLabelExclusions.keys_exclusion Q B hB)
    hrecipe.fresh C D refA refB hAr hBr hC hD hkey G hf testers L R holes
    hrole hgradient hU hu hrecipe.roles hleft hright ζ hζ hζsmall hk hmassA hmassB hcapA hcapB hsmall

end Lax342547Proofs.RawRetainedCells
