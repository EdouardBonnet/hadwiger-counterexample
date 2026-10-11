import Lax342547.TensorBlocks
import Lax342547.QuotientExtractors
import Lax342547.PureObstructions

/-!
---
title: Selected tensor blocks of actual pure obstructions
type: lemma
---
Freshness of the actual lists leaves one possible individual key ray at
a selected label. Extracting its block through the pin-plus-key quotients
forces a scalar point moment on its tag star and zero off that star.
Agreement of those scalars across components is a subsequent obligation.
-/

namespace Lax342547.SelectedBlocks

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.WitnessAtoms
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PinLabelExclusions
open Lax342547.BarredSpaces Lax342547.PairedAnnihilators Lax342547.BaseMoments

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

noncomputable def keyBase (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) (t : Σ z, Fin (W.length i z)) : Option (Base k n) → Binary := by
  classical
  exact if (W.left i t.1 t.2).tag ∈ e.val then baseEval (W.left i t.1 t.2).base else 0

noncomputable def individualRay (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) (t : Σ z, Fin (W.length i z)) :
    Submodule Binary (Option (Base k n) → Binary) := by
  classical
  exact if (W.left i t.1 t.2).tag ∈ e.val then
    Submodule.span Binary {baseEval (W.left i t.1 t.2).base} else ⊥

axiom individual_extractor {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (u : Σ z, Fin (W.length i z))
    (hs : (W.left i u.1 u.2).label ∈ L) (hfresh : (W.left i u.1 u.2).label ∉ A i) :
    ∃ q : (Vector k n b degree ⧸ (projected P i a ⊔ individualKeys W i a.1)) →ₗ[Binary]
        ((Option (Base k n) → Binary) ⧸ individualRay W i a.1 u),
      ∀ t ∈ L, ∀ v, q (Submodule.Quotient.mk
        (Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t v)) =
          if t = (W.left i u.1 u.2).label then (individualRay W i a.1 u).mkQ v else 0

axiom selected_component {R : ℕ} (W : Lists k n b degree r hr)
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
        Z (W.left i u.1 u.2).label none none • baseMoment (W.left i u.1 u.2).base else 0

axiom selected_obstruction {R : ℕ} (W : Lists k n b degree r hr)
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
        Z (W.left i u.1 u.2).label none none • baseMoment (W.left i u.1 u.2).base else 0

end Lax342547.SelectedBlocks
