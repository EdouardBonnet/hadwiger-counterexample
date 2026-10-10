import Lax342547.FrozenAssembly
import Lax342547.PairedRecipes

/-!
---
title: Whole-space gradient realization preserving the actual frozen entries
type: definition and theorem
---
Under the genuine scalar recipe, injecting table, matched keys, sparse covers and the explicit degree and channel margins, the bounded baseline and both reciprocal recipe solutions assemble into cross forms that preserve every frozen entry and satisfy all four gradients. The original small table may change away from its frozen rows and columns, as permitted by Theorem 6.3.
-/

namespace Lax342547.FrozenGradients

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression
open Lax342547.ResidualRealization
open Lax342547.CompressedResidual

axiom frozen_gradients {k n b degree r : ℕ} {hr : 2 * r ≤ n}
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
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU' : ∀ e j, IsCompl (protectedChannel Q j (e, true)) (U' e j))
    (hV' : ∀ e j, IsCompl (protectedChannel Q j (e, false)) (V' e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hF : Extends F T) (hbounded : Bounded F K)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms W i) (Lax342547.PairedRecipes.oppositeP W oB i))
    (hgradients' : ∀ z, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms (Lax342547.PairedRecipes.flip W) z)
      (Lax342547.PairedRecipes.oppositeP (Lax342547.PairedRecipes.flip W) oA z))
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

end Lax342547.FrozenGradients
