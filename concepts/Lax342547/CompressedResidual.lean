import Lax342547.ConstrainedCompression

/-!
---
title: A bounded-rank pure correction for the actual scalar recipe
type: lemma
---
The actual unrestricted pure remainder is precomposed with chosen block compression maps on both barred quotients. Its response on the full cut-profile pair space is unchanged and its component rank is at most the paper quotient bound. The genuine recipe wrapper retains the bounded derivative families and the exact recipe residual response.
-/

namespace Lax342547.CompressedResidual

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression
open Lax342547.ResidualRealization

noncomputable def blockBound (k b degree K R : ℕ) : ℕ :=
  2 * Fintype.card (SelectorCoordinates b degree) * Fintype.card (Component (Tag k)) * (K + 14 + R)

noncomputable def quotientBound (k b degree K R : ℕ) : ℕ :=
  2 * Fintype.card (SelectorCoordinates b degree) *
    (1 + ((2 * k + 1)^2 + 3) * blockBound k b degree K R) + 2 * K

axiom compressed_pure_solution {k n b degree r K R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e i, IsCompl (protectedChannel P i (e, true)) (U e i))
    (hV : ∀ e i, IsCompl (protectedChannel P i (e, false)) (V e i))
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (hM : ∀ i e, (M i e).rank ≤ R)
    (β : Lax342547.PureObstructions.Parameters W P U V)
    (hβ : Lax342547.PureObstructions.response W P U V β = matrixResponse (Profile k n b degree) M) :
    ∃ γ : Lax342547.PureObstructions.Parameters W P U V,
      Lax342547.PureObstructions.response W P U V γ = matrixResponse (Profile k n b degree) M ∧
      ∀ e, Module.finrank Binary (LinearMap.range (γ e)) ≤ quotientBound k b degree K R

axiom compressed_recipe {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hF : Extends F T) (hbounded : Bounded F K)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms W i) (Lax342547.PairedRecipes.oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2)
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (hM : matrixResponse (Profile k n b degree) M =
      ∑ i, (D.role + gradient D L R (leftWitness W i z)).comp (LinearMap.proj i)) :
    ∃ (M0 R0 : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β0 γ : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V γ = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (γ e)) ≤
        quotientBound k b degree K (14 * K + 140)) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e + γ e)) ≤
        (∑ i, (M i e).rank) + quotientBound k b degree K (14 * K + 140)) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28) ∧
      fullResponse W P Q U V F z (β0 + γ + extraFamily W P Q U V z δ ε) δ ε =
        ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i)

end Lax342547.CompressedResidual
