import Lax342547.SelectedScalars
import Lax342547Proofs.SelectedBlocks
import Lax342547Proofs.LabelRelations

namespace Lax342547Proofs.SelectedScalars

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PinLabelExclusions Lax342547.BaseMoments
open Lax342547.LabelRelations Lax342547.TensorBlocks

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.SelectedScalars.profile_triangle
---
The actual representative gives the three-edge cut relation. Reconstruct
its three components and separate their union of at most 3R labels.
-/
theorem profile_triangle {k n b degree R : ℕ} (x : Profile k n b degree)
    (L : Component (Tag k) → Finset (Fin b → Binary))
    (Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hL : ∀ e, (L e).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (hM : ∀ e, x.val e = ∑ s ∈ L e, block selectorEval s (Z e s))
    (a b c : Tag k) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∀ s, supported (L (edge a b hab)) (Z (edge a b hab)) s +
      supported (L (edge b c hbc)) (Z (edge b c hbc)) s +
      supported (L (edge a c hac)) (Z (edge a c hac)) s = 0 := by
  classical
  let E : Fin 3 → Component (Tag k) := ![edge a b hab, edge b c hbc, edge a c hac]
  obtain ⟨w, hw⟩ := x.property
  change cutMap w.val = x.val at hw
  have ht : x.val (edge a b hab) + x.val (edge b c hbc) + x.val (edge a c hac) = 0 := by
    rw [← hw]
    exact LabelRelations.cut_triangle w.val a b c hab hbc hac
  have hsum : (∑ j : Fin 3, ∑ s ∈ L (E j), block (selectorEval (degree := degree)) s (Z (E j) s)) = 0 := by
    simp_rw [← hM]
    simpa [Fin.sum_univ_three, E, add_assoc] using ht
  have hsep := LabelRelations.triangle_blocks (L ∘ E) (Z ∘ E)
    (fun j => hL (E j)) hdegree hsum
  intro s
  simpa [Fin.sum_univ_three, E, Function.comp_def, add_assoc] using hsep s

theorem edge_swap {Tag : Type} [DecidableEq Tag] (a b : Tag) (hab : a ≠ b) :
    edge a b hab = edge b a hab.symm := by
  apply Subtype.ext
  exact Finset.pair_comm a b

/--
---
conclusion: Lax342547.SelectedScalars.star_scalar
---
Fix one edge from the selected tag. A triangle through any other edge
has zero on its off-star edge, so its two star coefficients agree.
-/
theorem star_scalar {Tag : Type} [DecidableEq Tag] [Nontrivial Tag]
    (l : Tag) (c : Component Tag → Binary)
    (htriangle : ∀ a b d (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d),
      c (edge a b hab) + c (edge b d hbd) + c (edge a d had) = 0)
    (hout : ∀ e, l ∉ e.val → c e = 0) :
    ∃ v : Binary, ∀ e, c e = if l ∈ e.val then v else 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_ne l
  have hla := ha.symm
  have heq (b : Tag) (hlb : l ≠ b) : c (edge l b hlb) = c (edge l a hla) := by
    by_cases hba : b = a
    · subst b; rfl
    · have ht := htriangle l b a hlb hba hla
      have houtba : l ∉ (edge b a hba).val := by simp [edge, hlb, hla]
      rw [hout _ houtba, add_zero] at ht
      calc
        c (edge l b hlb) = (c (edge l b hlb) + c (edge l a hla)) + c (edge l a hla) := by
          rw [add_assoc, LabelRelations.binary_double, add_zero]
        _ = c (edge l a hla) := by rw [ht, zero_add]
  refine ⟨c (edge l a hla), ?_⟩
  intro e
  by_cases hl : l ∈ e.val
  · rw [if_pos hl]
    obtain ⟨b, d, hbd, hed⟩ := Finset.card_eq_two.mp e.property
    have he : e = edge b d hbd := Subtype.ext hed
    have hld : l = b ∨ l = d := by simpa [hed] using hl
    rcases hld with rfl | rfl
    · rw [he]
      exact heq d hbd
    · rw [he, edge_swap]
      exact heq b hbd.symm
  · rw [if_neg hl]
    exact hout e hl

/--
---
conclusion: Lax342547.SelectedScalars.selected_scalar
---
Read the affine constant entry of each selected block. Its triangle
relations and off-star vanishing give a common scalar, which recovers
the entire selected base moment on every component.
-/
theorem selected_scalar {k n b degree R : ℕ} (hk : 0 < k) (x : Profile k n b degree)
    (L : Component (Tag k) → Finset (Fin b → Binary))
    (Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hL : ∀ e, (L e).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (hM : ∀ e, x.val e = ∑ s ∈ L e, block selectorEval s (Z e s))
    (s : Fin b → Binary) (l : Tag k) (z : Base k n → Binary)
    (hshape : ∀ e, supported (L e) (Z e) s = if l ∈ e.val then
      (supported (L e) (Z e) s) none none • baseMoment z else 0) :
    ∃ v : Binary, ∀ e, supported (L e) (Z e) s = if l ∈ e.val then v • baseMoment z else 0 := by
  classical
  have : Nontrivial (Tag k) := ZMod.nontrivial_iff.mpr (by omega)
  let c (e : Component (Tag k)) := (supported (L e) (Z e) s) none none
  have htriangle (a b d : Tag k) (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
      c (edge a b hab) + c (edge b d hbd) + c (edge a d had) = 0 := by
    have ht := profile_triangle x L Z hL hdegree hM a b d hab hbd had s
    exact congrArg (fun M => M none none) ht
  have hout (e : Component (Tag k)) (he : l ∉ e.val) : c e = 0 := by
    have hz := hshape e
    rw [if_neg he] at hz
    exact congrArg (fun M => M none none) hz
  obtain ⟨v, hv⟩ := star_scalar l c htriangle hout
  refine ⟨v, ?_⟩
  intro e
  rw [hshape e]
  by_cases he : l ∈ e.val
  · rw [if_pos he, if_pos he]
    have hc : c e = v := by simpa [he] using hv e
    rw [← hc]
  · rw [if_neg he, if_neg he]

/--
---
conclusion: Lax342547.SelectedScalars.obstruction_scalar
---
Use the checked selected-block theorem in every component of the actual
pure obstruction, pad absent labels by zero, and apply scalar consistency.
-/
theorem obstruction_scalar {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Lax342547.PureObstructions.Annihilates W P U V x)
    (i : Fin 2) (L : Component (Tag k) → Finset (Fin b → Binary))
    (Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hL : ∀ e, (L e).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (hM : ∀ e, (x i).val e = ∑ s ∈ L e, block selectorEval s (Z e s))
    (hZ : ∀ e s, s ∈ L e → IsBaseMoment (Z e s))
    (u : Σ z, Fin (W.length i z)) (hfresh : (W.left i u.1 u.2).label ∉ A i) :
    ∃ v : Binary, ∀ e, supported (L e) (Z e) (W.left i u.1 u.2).label =
      if (W.left i u.1 u.2).tag ∈ e.val then v • baseMoment (W.left i u.1 u.2).base else 0 := by
  classical
  apply selected_scalar hk (x i) L Z hL hdegree hM (W.left i u.1 u.2).label
    (W.left i u.1 u.2).tag (W.left i u.1 u.2).base
  intro e
  by_cases hs : (W.left i u.1 u.2).label ∈ L e
  · simp only [supported, hs, if_pos]
    apply SelectedBlocks.selected_obstruction W P A hA U V x h i e (L e) (hL e) (Z e) _ u hs hfresh
      (hZ e _ hs)
    intro a c
    have hm := congrArg (fun M => M a c) (hM e)
    simpa [Matrix.sum_apply, Lax342547.TensorBlocks.block] using hm
  · simp [supported, hs]

/--
---
conclusion: Lax342547.SelectedScalars.selected_decomposition
---
Choose the checked component label decompositions of the actual pure
obstruction. Their degree margin permits triangle interpolation. Every
fresh selected witness then has its own scalar, shared across its star.
-/
theorem selected_decomposition {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] (hk : 0 < k) (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Lax342547.PureObstructions.Annihilates W P U V x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (i : Fin 2) :
    ∃ L : Component (Tag k) → Finset (Fin b → Binary),
    ∃ Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary,
    ∃ c : (Σ z, Fin (W.length i z)) → Binary,
      (∀ e, (L e).card ≤ 2 * K + 28 ∧ (∀ s ∈ L e, IsBaseMoment (Z e s)) ∧
        (∑ s ∈ L e, (Z e s).rank) ≤ 2 * K + 28 ∧
        ∀ a d, (x i).val e a d = ∑ s ∈ L e,
          selectorEval s a.1 * selectorEval s d.1 * Z e s a.2 d.2) ∧
      ∀ u e, supported (L e) (Z e) (W.left i u.1 u.2).label =
        if (W.left i u.1 u.2).tag ∈ e.val then c u • baseMoment (W.left i u.1 u.2).base else 0 := by
  classical
  choose L Z hL hZ hRanks hM using
    (fun e => PureObstructions.component_labels W P hK U V x h hdegree i e)
  have hmat (e : Component (Tag k)) :
      (x i).val e = ∑ s ∈ L e, block selectorEval s (Z e s) := by
    ext a d
    simpa [Matrix.sum_apply, Lax342547.TensorBlocks.block] using hM e a d
  have htri : 3 * (2 * K + 28) ≤ degree + 1 := by omega
  have hscalar (u : Σ z, Fin (W.length i z)) :=
    obstruction_scalar hk W P A hA U V x h i L Z hL htri hmat
      (fun e s hs => hZ e s hs) u (hfresh i u.1 u.2)
  choose c hc using hscalar
  exact ⟨L, Z, c, fun e => ⟨hL e, hZ e, hRanks e, hM e⟩, hc⟩

end Lax342547Proofs.SelectedScalars
