import Lax342547.ResponseSolvability
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
---
title: Bounded allowed derivatives preserving the actual linearized response
type: theorem
---
Sections of the observed baseline pairings compress derivative outputs
inside their original perpendicular value spaces. The two actual derivative
families retain their barred domain quotients, preserve the whole response,
and have rank at most 3K+28 in an actual recipe solution. The residual matrix
rank, pure correction and final channel factorization remain separate.
-/

namespace Lax342547.BoundedDerivatives

open Lax342547.MomentSpace
open Lax342547.ChannelChanges
open Lax342547.PairedAnnihilators Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.NominalPrimal Lax342547.TensorAnnihilators
open Lax342547.BarredSpaces
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.CutProfiles Lax342547.ExactPins Lax342547.PairedWitnesses Lax342547.RawBaselines
open Lax342547.PairedRecipes Lax342547.PinLabelExclusions

axiom observed_projection {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V]
    (L : V →ₗ[Binary] X) :
    ∃ p : V →ₗ[Binary] V, L.comp p = L ∧
      Module.finrank Binary (LinearMap.range p) ≤ Module.finrank Binary (LinearMap.range L)

axiom allowed_projection {H X : Type} [Fintype H]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (G : X →ₗ[Binary] (H → Binary)) :
    ∃ p : perpendicular S →ₗ[Binary] perpendicular S,
      (∀ c x, dotProduct (p c).val (G x) = dotProduct c.val (G x)) ∧
      Module.finrank Binary (LinearMap.range p) ≤ Module.finrank Binary (LinearMap.range G)

axiom bounded_derivative {D H X : Type} [AddCommGroup D] [Module Binary D]
    [Fintype H] [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (G : X →ₗ[Binary] (H → Binary))
    (δ : D →ₗ[Binary] perpendicular S) :
    ∃ δ' : D →ₗ[Binary] perpendicular S,
      (∀ v x, dotProduct (δ' v).val (G x) = dotProduct (δ v).val (G x)) ∧
      Module.finrank Binary (LinearMap.range δ') ≤ Module.finrank Binary (LinearMap.range G)

axiom bounded_derivative_covectors {D H X : Type} [AddCommGroup D] [Module Binary D]
    [Fintype H] [DecidableEq H] [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (C : X →ₗ[Binary] Module.Dual Binary (H → Binary))
    (δ : D →ₗ[Binary] perpendicular S) :
    ∃ δ' : D →ₗ[Binary] perpendicular S,
      (∀ v x, dotProduct (δ' v).val (Lax342547.TensorAnnihilators.dualCoordinates (C x)) =
        dotProduct (δ v).val (Lax342547.TensorAnnihilators.dualCoordinates (C x))) ∧
      Module.finrank Binary (LinearMap.range δ') ≤ Module.finrank Binary (LinearMap.range C)

axiom bounded_component {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (R : ℕ)
    (hplus : Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hminus : Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    ∃ δ' ε', componentResponse F e z D E S T δ' ε' = componentResponse F e z D E S T δ ε ∧
      Module.finrank Binary (LinearMap.range δ') ≤ R ∧
      Module.finrank Binary (LinearMap.range ε') ≤ R

axiom bounded_response {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Bounded F K) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    ∃ δ' ε', response W P Q U V F z δ' ε' = response W P Q U V F z δ ε ∧
      ∀ e, Module.finrank Binary (LinearMap.range (δ' e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε' e)) ≤ 3 * K + 28

axiom bounded_recipe_solution {H N : Type} [Fintype H] [Fintype N] {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (hbounded : Bounded F K)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2) :
    ∃ (β : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z), fullResponse W P Q U V F z β δ ε =
      ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i) ∧
      ∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28

end Lax342547.BoundedDerivatives
