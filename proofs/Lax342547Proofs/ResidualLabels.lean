import Lax342547.ResidualLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lax342547.Atoms
import Lax342547.SelectedRemoval
import Lax342547.SelectedScalars

namespace Lax342547Proofs.ResidualLabels

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PinLabelExclusions Lax342547.BaseMoments
open Lax342547.LabelRelations Lax342547.TensorBlocks Lax342547.SelectedRemoval
open Lax342547.ResidualLabels

set_option backward.isDefEq.respectTransparency false

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

theorem block_point {Label Coord Base : Type} (p : Label → Coord → Binary)
    (s : Label) (z : Base → Binary) : block p s (baseMoment z) = pointMoment p s z := by
  ext a d
  simp only [block, baseMoment, pointMoment, point, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem sum_supported_image {Label Base I : Type} [Fintype I] [DecidableEq Label]
    (label : I → Label) (hinj : Function.Injective label) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) (p : Label → (SelectorCoordinates b degree) → Binary) :
    (∑ u, block p (label u) (supported L Z (label u))) =
      ∑ s ∈ L ∩ Finset.univ.image label, block p s (Z s) := by
  classical
  rw [← Finset.sum_image (f := fun s => block p s (supported L Z s))
    (s := Finset.univ) (g := label) hinj.injOn]
  have he : (Finset.univ.image label).filter (fun s => s ∈ L) = L ∩ Finset.univ.image label := by
    ext s
    simp [and_comm]
  rw [← he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ L <;> simp [supported, hs]

/--
---
conclusion: Lax342547.ResidualLabels.residual_reconstruction
---
The list labels are injective, so their sum is the sum over the selected
label set. The common scalar identifies each selected block with the
corresponding atom. The finite intersection/difference identity deletes
exactly those blocks from every component.
-/
theorem residual_reconstruction (W : Lists k n b degree r hr)
    (x : Fin 2 → Profile k n b degree)
    (L : Fin 2 → Component (Tag k) → Finset (Fin b → Binary))
    (Z : Fin 2 → Component (Tag k) → (Fin b → Binary) →
      Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary)
    (hM : ∀ i e, (x i).val e = ∑ s ∈ L i e, block selectorEval s (Z i e s))
    (hc : ∀ i u e, supported (L i e) (Z i e) (W.left i u.1 u.2).label =
      if (W.left i u.1 u.2).tag ∈ e.val then c i u • baseMoment (W.left i u.1 u.2).base else 0) :
    ∀ i e, ((x - selectedPart W c) i).val e =
      ∑ s ∈ L i e \ chosenLabels W i, block selectorEval s (Z i e s) := by
  classical
  intro i e
  have hpart : ((selectedPart W c) i).val e =
      ∑ u : Σ z, Fin (W.length i z), block selectorEval (W.left i u.1 u.2).label
        (supported (L i e) (Z i e) (W.left i u.1 u.2).label) := by
    simp only [selectedPart, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro u _
    rw [hc i u e]
    by_cases he : (W.left i u.1 u.2).tag ∈ e.val
    · simp only [if_pos he, map_smul, block_point,
        Lax342547.WitnessAtoms.PointAtom.profile, Lax342547.Atoms.atom_component]
    · simp [he, Lax342547.WitnessAtoms.PointAtom.profile, Lax342547.Atoms.atom_component]
  have himage := sum_supported_image (fun u : Σ z, Fin (W.length i z) => (W.left i u.1 u.2).label)
    (W.left_fresh i) (L i e) (Z i e) (selectorEval (degree := degree))
  have hpart' : ((selectedPart W c) i).val e =
      ∑ s ∈ L i e ∩ chosenLabels W i, block selectorEval s (Z i e s) := hpart.trans himage
  change (x i).val e - ((selectedPart W c) i).val e = _
  rw [hM i e, hpart', ← Finset.sum_inter_add_sum_sdiff (L i e) (chosenLabels W i)
    (fun s => block (selectorEval (degree := degree)) s (Z i e s))]
  abel

/--
---
conclusion: Lax342547.ResidualLabels.unselected_obstruction
---
Choose the scalar decompositions at both endpoints and subtract their
actual selected atoms. Pure annihilation is preserved, and deleting the
selected labels preserves the label and sum-of-ranks budgets and all
Boolean moment identities of the surviving base blocks.
-/
theorem unselected_obstruction {K : ℕ} [Fintype H] (hk : 0 < k)
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Covers P A (2 * K + 28)) (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Lax342547.PureObstructions.Annihilates W P U V x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∃ c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary,
    ∃ L : Fin 2 → Component (Tag k) → Finset (Fin b → Binary),
    ∃ Z : Fin 2 → Component (Tag k) → (Fin b → Binary) →
        Matrix (Option (Base k n)) (Option (Base k n)) Binary,
      Lax342547.PureObstructions.Annihilates W P U V (x - selectedPart W c) ∧
      ∀ i e, (L i e).card ≤ 2 * K + 28 ∧
        (∀ s ∈ L i e, s ∉ chosenLabels W i ∧ IsBaseMoment (Z i e s)) ∧
        (∑ s ∈ L i e, (Z i e s).rank) ≤ 2 * K + 28 ∧
        ((x - selectedPart W c) i).val e = ∑ s ∈ L i e, block selectorEval s (Z i e s) := by
  classical
  choose L Z c hdec hc using
    (fun i => Lax342547.SelectedScalars.selected_decomposition hk W P hK A hA hfresh U V x h hdegree i)
  have hmat (i : Fin 2) (e : Component (Tag k)) :
      (x i).val e = ∑ s ∈ L i e, block selectorEval s (Z i e s) := by
    ext a d
    simpa [Matrix.sum_apply, Lax342547.TensorBlocks.block] using (hdec i e).2.2.2 a d
  have hres := Lax342547.ResidualLabels.residual_reconstruction W x L Z c hmat hc
  refine ⟨c, fun i e => L i e \ chosenLabels W i, Z,
    Lax342547.SelectedRemoval.subtract_annihilates W P U V x h c, ?_⟩
  intro i e
  refine ⟨(Finset.card_le_card Finset.sdiff_subset).trans (hdec i e).1, ?_, ?_, hres i e⟩
  · intro s hs
    obtain ⟨hsL, hsNot⟩ := Finset.mem_sdiff.mp hs
    exact ⟨hsNot, (hdec i e).2.1 s hsL⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun _ _ _ => Nat.zero_le _)).trans (hdec i e).2.2.1

end Lax342547Proofs.ResidualLabels
