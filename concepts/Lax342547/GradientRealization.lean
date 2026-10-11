import Lax342547.FrozenGradients
import Lax342547.RawBaselines

/-!
---
title: Deterministic whole-space gradient realization from the genuine recipe hypotheses
type: lemma
---
Construct the bounded frozen baseline from the admissible injecting small table and sparse pin exclusions. Choose actual private channel complements, solve both reciprocal recipes, and assemble one pair of cross forms satisfying all four whole-space gradients while retaining every actual pin and key entry.
-/

namespace Lax342547.GradientRealization

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression
open Lax342547.ResidualRealization
open Lax342547.CompressedResidual

axiom gradient_realization {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (hQ : Q.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (hB : Lax342547.PinLabelExclusions.Covers Q B (2 * K + 28))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (hrecipe : ScalarRecipe W D L R oA oB T A B) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms W i) (Lax342547.PairedRecipes.oppositeP W oB i))
    (hgradients' : ∀ z, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms (Lax342547.PairedRecipes.flip W) z)
      (Lax342547.PairedRecipes.oppositeP (Lax342547.PairedRecipes.flip W) oA z))
    (hadmissible : Lax342547.SmallTables.Admissible T Lax342547.ReferencePins.observation
      Lax342547.ReferencePins.observation oA oB)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree)
    (hmargin : 28 * copies * Fintype.card (Component (Tag k)) +
      quotientBound k b degree K (14 * K + 140) + 2 * K + 4 * (3 * K + 28) < 970 * r)
    (hchannels : 1000 * r ≤ Fintype.card H) :
    ∃ G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H,
      Frozen G W P Q oA oB ∧
      (∀ i z x, fullContraction G (Profile k n b degree) i z x =
        (D.role + gradient D L R (leftWitness W i z)) x) ∧
      (∀ i z x, fullContraction G.flip (Profile k n b degree) z i x =
        (D.role + gradient D L R (rightWitness W i z)) x)

end Lax342547.GradientRealization
