import Lax342547.SelectedRemoval

/-!
---
title: Removing selected atoms leaves only unselected component labels
type: definition and theorem
---
Freshness identifies the finite sum of selected atoms with exactly the
selected label blocks. Subtracting that sum deletes those blocks. The
remaining supports are subsets of the original bounded supports and
retain the original Boolean moment and sum-of-block-ranks budgets.
-/

namespace Lax342547.ResidualLabels

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PinLabelExclusions Lax342547.BaseMoments
open Lax342547.LabelRelations Lax342547.TensorBlocks Lax342547.SelectedRemoval

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

noncomputable def chosenLabels (W : Lists k n b degree r hr) (i : Fin 2) : Finset (Fin b → Binary) :=
  Finset.univ.image (fun u : Σ z, Fin (W.length i z) => (W.left i u.1 u.2).label)

axiom residual_reconstruction (W : Lists k n b degree r hr)
    (x : Fin 2 → Profile k n b degree)
    (L : Fin 2 → Component (Tag k) → Finset (Fin b → Binary))
    (Z : Fin 2 → Component (Tag k) → (Fin b → Binary) →
      Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary)
    (hM : ∀ i e, (x i).val e = ∑ s ∈ L i e, block selectorEval s (Z i e s))
    (hc : ∀ i u e, supported (L i e) (Z i e) (W.left i u.1 u.2).label =
      if (W.left i u.1 u.2).tag ∈ e.val then c i u • baseMoment (W.left i u.1 u.2).base else 0) :
    ∀ i e, ((x - selectedPart W c) i).val e =
      ∑ s ∈ L i e \ chosenLabels W i, block selectorEval s (Z i e s)

axiom unselected_obstruction {K : ℕ} [Fintype H] (hk : 0 < k)
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
        ((x - selectedPart W c) i).val e = ∑ s ∈ L i e, block selectorEval s (Z i e s)

end Lax342547.ResidualLabels
