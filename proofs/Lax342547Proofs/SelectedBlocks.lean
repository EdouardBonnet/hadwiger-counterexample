import Lax342547.SelectedBlocks
import Lax342547.BarredSpaces
import Lax342547.PairedAnnihilators
import Lax342547.PairedWitnesses
import Lax342547.PureObstructions
import Lax342547.QuotientExtractors
import Lax342547.TensorAnnihilators
import Lax342547.TensorBlocks

namespace Lax342547Proofs.SelectedBlocks

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.WitnessAtoms
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PinLabelExclusions
open Lax342547.BarredSpaces Lax342547.PairedAnnihilators Lax342547.BaseMoments
open Lax342547.SelectedBlocks Lax342547.SparsePins

set_option backward.isDefEq.respectTransparency false

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

theorem key_lift (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) (t : Σ z, Fin (W.length i z)) :
    labelTensor (selectorEval (degree := degree)) (W.left i t.1 t.2).label (keyBase W i e t) =
      individualDirection W i e t := by
  classical
  by_cases he : (W.left i t.1 t.2).tag ∈ e.val
  · ext c
    simp [labelTensor, keyBase, individualDirection, he,
      Lax342547.WitnessAtoms.PointAtom.vector, point]
  · simp [keyBase, individualDirection, he]

theorem keys_as_labels (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) :
    Submodule.span Binary (Set.range (fun t : Σ z, Fin (W.length i z) =>
      labelTensor (selectorEval (degree := degree)) (W.left i t.1 t.2).label (keyBase W i e t))) =
        individualKeys W i e := by
  simp only [key_lift, individualKeys]

/--
---
conclusion: Lax342547.SelectedBlocks.individual_extractor
---
Adjoin the endpoint's at most fourteen key labels to the component's
support. Actual list freshness identifies the only key at the selected
label; it spans the selected affine ray exactly on its incident star.
-/
theorem individual_extractor {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (u : Σ z, Fin (W.length i z))
    (hs : (W.left i u.1 u.2).label ∈ L) (hfresh : (W.left i u.1 u.2).label ∉ A i) :
    ∃ q : (Vector k n b degree ⧸ (projected P i a ⊔ individualKeys W i a.1)) →ₗ[Binary]
        ((Option (Base k n) → Binary) ⧸ individualRay W i a.1 u),
      ∀ t ∈ L, ∀ v, q (Submodule.Quotient.mk
        (labelTensor (selectorEval (degree := degree)) t v)) =
          if t = (W.left i u.1 u.2).label then (individualRay W i a.1 u).mkQ v else 0 := by
  classical
  let labels : (Σ z, Fin (W.length i z)) → Fin b → Binary := fun t => (W.left i t.1 t.2).label
  let J := Finset.univ.image labels
  have hJ : J.card ≤ 14 :=
    (Finset.card_image_le).trans (by simpa using (Lax342547.PairedWitnesses.list_budgets W).1 i)
  have hUnion : (L ∪ J).card ≤ R + 14 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hL hJ)
  have hlabels (t : Σ z, Fin (W.length i z)) : labels t ∈ L ∪ J :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
  have hmatch (t : Σ z, Fin (W.length i z)) (ht : labels t = (W.left i u.1 u.2).label) :
      keyBase W i a.1 t ∈ individualRay W i a.1 u := by
    have heq : t = u := W.left_fresh i ht
    subst t
    by_cases he : (W.left i u.1 u.2).tag ∈ a.1.val
    · simp only [keyBase, individualRay, he, if_pos]
      exact Submodule.subset_span (Set.mem_singleton _)
    · simp [keyBase, individualRay, he]
  have hex := Lax342547.QuotientExtractors.key_extractor P A hA i a (L ∪ J) hUnion
    (W.left i u.1 u.2).label (Finset.mem_union_left _ hs) hfresh labels (keyBase W i a.1)
    hlabels (individualRay W i a.1 u) hmatch
  have hkeys := keys_as_labels W i a.1
  change Submodule.span Binary (Set.range (fun t =>
    labelTensor (selectorEval (degree := degree)) (labels t) (keyBase W i a.1 t))) =
      individualKeys W i a.1 at hkeys
  rw [hkeys] at hex
  obtain ⟨q, hq⟩ := hex
  exact ⟨q, fun t ht v => hq t (Finset.mem_union_left _ ht) v⟩

/--
---
conclusion: Lax342547.SelectedBlocks.selected_component
---
Project the nominal pure annihilator to this endpoint. Extract the
selected label in both factors. Its base moment is killed by its affine
ray quotients, or by no rays off its star, giving a scalar point or zero.
-/
theorem selected_component {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (U V : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k))
    (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, true)) (barred W P V (e, false)))
    (i : Fin 2) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : M i = ∑ t ∈ L, Lax342547.TensorBlocks.block selectorEval t (Z t))
    (u : Σ z, Fin (W.length i z)) (hs : (W.left i u.1 u.2).label ∈ L)
    (hfresh : (W.left i u.1 u.2).label ∉ A i)
    (hZ : IsBaseMoment (Z (W.left i u.1 u.2).label)) :
    Z (W.left i u.1 u.2).label =
      if (W.left i u.1 u.2).tag ∈ e.val then
        Z (W.left i u.1 u.2).label none none • baseMoment (W.left i u.1 u.2).base else 0 := by
  classical
  obtain ⟨q, hq⟩ := Lax342547.SelectedBlocks.individual_extractor W P A hA i (e, true) L hL u hs hfresh
  obtain ⟨v, hv⟩ := Lax342547.SelectedBlocks.individual_extractor W P A hA i (e, false) L hL u hs hfresh
  have hi := Lax342547.PairedAnnihilators.endpoint_projection M _ _ h i
    (projected P i (e, true) ⊔ individualKeys W i e)
    (projected P i (e, false) ⊔ individualKeys W i e)
    (Lax342547.BarredSpaces.barred_projection W P U (e, true) i)
    (Lax342547.BarredSpaces.barred_projection W P V (e, false) i)
  rw [hM] at hi
  have hb := Lax342547.TensorBlocks.quotient_isolation selectorEval L (W.left i u.1 u.2).label hs Z
    _ _ (individualRay W i e u) (individualRay W i e u) q v hq hv hi
  by_cases he : (W.left i u.1 u.2).tag ∈ e.val
  · rw [if_pos he]
    apply Lax342547.TensorAnnihilators.selected_block _ _ hZ
    simpa only [individualRay, he, if_pos] using hb
  · rw [if_neg he]
    have hz : Lax342547.TensorAnnihilators.PureAnnihilates
        (Z (W.left i u.1 u.2).label) ⊥ ⊥ := by
      simpa only [individualRay, he, if_false] using hb
    have hzero := Lax342547.TensorAnnihilators.pure_sandwich _ _ _ hz
      (1 : Matrix (Option (Base k n)) (Option (Base k n)) Binary)
      (1 : Matrix (Option (Base k n)) (Option (Base k n)) Binary) bot_le bot_le
    simpa using hzero

/--
---
conclusion: Lax342547.SelectedBlocks.selected_obstruction
---
Apply the component theorem to the actual pair of cut profiles and the
entrywise reconstruction supplied by their low-rank label decomposition.
-/
theorem selected_obstruction {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Lax342547.PureObstructions.Annihilates W P U V x)
    (i : Fin 2) (e : Component (Tag k)) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : ∀ a c, (x i).val e a c =
      ∑ t ∈ L, selectorEval t a.1 * selectorEval t c.1 * Z t a.2 c.2)
    (u : Σ z, Fin (W.length i z)) (hs : (W.left i u.1 u.2).label ∈ L)
    (hfresh : (W.left i u.1 u.2).label ∉ A i)
    (hZ : IsBaseMoment (Z (W.left i u.1 u.2).label)) :
    Z (W.left i u.1 u.2).label =
      if (W.left i u.1 u.2).tag ∈ e.val then
        Z (W.left i u.1 u.2).label none none • baseMoment (W.left i u.1 u.2).base else 0 := by
  apply Lax342547.SelectedBlocks.selected_component W P A hA (U e) (V e) e
    (Lax342547.PureObstructions.endpointComponent e x)
    (Lax342547.PureObstructions.component_annihilation W P U V x h e) i L hL Z _ u hs hfresh hZ
  ext a c
  simpa [Lax342547.PureObstructions.endpointComponent, Lax342547.TensorBlocks.block,
    LinearMap.sum_apply, Matrix.sum_apply] using hM a c

end Lax342547Proofs.SelectedBlocks
