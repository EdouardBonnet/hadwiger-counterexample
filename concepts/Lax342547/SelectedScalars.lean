import Lax342547.SelectedBlocks
import Lax342547.LabelRelations

/-!
---
title: Selected label coefficients agree across the cut profile
type: lemma
---
The three-edge cut relation separates by label. A coefficient supported
on one tag star consequently has one scalar on the entire star. Applying
the selected-block theorem to actual pure obstructions yields a single
scalar multiple of each selected point atom.
-/

namespace Lax342547.SelectedScalars

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PinLabelExclusions Lax342547.BaseMoments
open Lax342547.LabelRelations Lax342547.TensorBlocks

axiom profile_triangle {k n b degree R : ℕ} (x : Profile k n b degree)
    (L : Component (Tag k) → Finset (Fin b → Binary))
    (Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hL : ∀ e, (L e).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (hM : ∀ e, x.val e = ∑ s ∈ L e, block selectorEval s (Z e s))
    (a b c : Tag k) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∀ s, supported (L (edge a b hab)) (Z (edge a b hab)) s +
      supported (L (edge b c hbc)) (Z (edge b c hbc)) s +
      supported (L (edge a c hac)) (Z (edge a c hac)) s = 0

axiom star_scalar {Tag : Type} [DecidableEq Tag] [Nontrivial Tag]
    (l : Tag) (c : Component Tag → Binary)
    (htriangle : ∀ a b d (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d),
      c (edge a b hab) + c (edge b d hbd) + c (edge a d had) = 0)
    (hout : ∀ e, l ∉ e.val → c e = 0) :
    ∃ v : Binary, ∀ e, c e = if l ∈ e.val then v else 0

axiom selected_scalar {k n b degree R : ℕ} (hk : 0 < k) (x : Profile k n b degree)
    (L : Component (Tag k) → Finset (Fin b → Binary))
    (Z : Component (Tag k) → (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hL : ∀ e, (L e).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (hM : ∀ e, x.val e = ∑ s ∈ L e, block selectorEval s (Z e s))
    (s : Fin b → Binary) (l : Tag k) (z : Base k n → Binary)
    (hshape : ∀ e, supported (L e) (Z e) s = if l ∈ e.val then
      (supported (L e) (Z e) s) none none • baseMoment z else 0) :
    ∃ v : Binary, ∀ e, supported (L e) (Z e) s = if l ∈ e.val then v • baseMoment z else 0

axiom obstruction_scalar {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
      if (W.left i u.1 u.2).tag ∈ e.val then v • baseMoment (W.left i u.1 u.2).base else 0

axiom selected_decomposition {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
        if (W.left i u.1 u.2).tag ∈ e.val then c u • baseMoment (W.left i u.1 u.2).base else 0

end Lax342547.SelectedScalars
