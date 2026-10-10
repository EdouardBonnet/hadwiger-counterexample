import Lax342547.RankedProjection

/-!
---
title: The bounded pure remainder of an actual scalar recipe
type: definition and theorem
---
Projected target forms and the bounded derivative product are removed from
the actual recipe solution on the entire cut-profile pair space. The
remaining pure response has per-individual matrix rank at most 14K+140.
Compression and final channel factorization are separate obligations.
-/

namespace Lax342547.ResidualRealization

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

noncomputable def matrixResponse {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (M : Fin 2 → Comp → Matrix B B Binary) :
    Module.Dual Binary (Fin 2 → X) :=
  ∑ i, (∑ e, (matrixPair (M i e)).comp ((LinearMap.proj e).comp X.subtype)).comp (LinearMap.proj i)

axiom matrixPair_sub {B : Type} [Fintype B] (M Q : Matrix B B Binary) :
    matrixPair (M - Q) = matrixPair M - matrixPair Q

axiom matrix_response_sub {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (M Q : Fin 2 → Comp → Matrix B B Binary) :
    matrixResponse X (M - Q) = matrixResponse X M - matrixResponse X Q

axiom projected_target [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    {K : ℕ} (hK : P.rank ≤ K)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (M : Fin 2 → Component (Tag k) → Moment k n b degree) :
    ∃ (Q : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β : Lax342547.PureObstructions.Parameters W P U V),
      Lax342547.PureObstructions.response W P U V β = matrixResponse (Profile k n b degree) Q ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β e)) ≤ ∑ i, (M i e).rank) ∧
      ∀ i e, (M i e - Q i e).rank ≤ 2 * K + 28 ∧ (Q i e).rank ≤ (M i e).rank

noncomputable def baselineMatrices
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2) :
    Fin 2 → Component (Tag k) → Moment k n b degree :=
  fun i e => coefficients (fullPlus F e i z) (fullMinus F e i z)

axiom baseline_response
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2) :
    matrixResponse (Profile k n b degree) (baselineMatrices F z) =
      ∑ i, (fullContraction F (Profile k n b degree) i z).comp (LinearMap.proj i)

noncomputable def derivativeMatrices (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    Fin 2 → Component (Tag k) → Moment k n b degree :=
  fun i e => coefficients
    (restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i)
    (fullMinus F e i z) + coefficients (fullPlus F e i z)
    (restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε e) i)

axiom derivative_response (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    matrixResponse (Profile k n b degree) (derivativeMatrices W P Q U V F z δ ε) =
      response W P Q U V F z δ ε

noncomputable def extraFamily (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    Lax342547.PureObstructions.Parameters W P U V :=
  fun e => extraProduct (barred W P (U e) (e, true)) (barred W P (V e) (e, false))
    (protectedChannel Q z (e, false)) (protectedChannel Q z (e, true)) (δ e) (ε e)

noncomputable def productMatrices (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    Fin 2 → Component (Tag k) → Moment k n b degree :=
  fun i e => coefficients
    (restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i)
    (restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε e) i)

axiom product_response (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    Lax342547.PureObstructions.response W P U V (extraFamily W P Q U V z δ ε) =
      matrixResponse (Profile k n b degree) (productMatrices W P Q U V z δ ε)

axiom pure_response_sub (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (β γ : Lax342547.PureObstructions.Parameters W P U V) :
    Lax342547.PureObstructions.response W P U V (β - γ) =
      Lax342547.PureObstructions.response W P U V β - Lax342547.PureObstructions.response W P U V γ

axiom bounded_remainder {K : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Bounded F K) (z : Fin 2)
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (β : Lax342547.PureObstructions.Parameters W P U V)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z)
    (hδ : ∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28)
    (hsol : fullResponse W P Q U V F z β δ ε = matrixResponse (Profile k n b degree) M -
      ∑ i, (fullContraction F (Profile k n b degree) i z).comp (LinearMap.proj i)) :
    ∃ (M0 R0 : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β0 β1 : Lax342547.PureObstructions.Parameters W P U V),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V β1 = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      β0 + β1 + extraFamily W P Q U V z δ ε = β

axiom paired_matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (t : Fin 2 → Module.Dual Binary X) :
    ∃ M : Fin 2 → Comp → Matrix B B Binary,
      matrixResponse X M = ∑ i, (t i).comp (LinearMap.proj i)

axiom recipe_remainder [Fintype N] {K : ℕ} {E : Moment k n b degree}
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
      (β0 β1 : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V β1 = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28) ∧
      fullResponse W P Q U V F z (β0 + β1 + extraFamily W P Q U V z δ ε) δ ε =
        ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i)

end Lax342547.ResidualRealization
