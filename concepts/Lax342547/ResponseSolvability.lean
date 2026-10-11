import Lax342547.EffectiveObstructions
import Lax342547.RecipeResiduals

/-!
---
title: Unrestricted linearized solutions for actual scalar recipes
type: lemma
---
The actual pure and allowed derivative response families are linear in their
parameters. The proved full obstruction decomposition and finite-dimensional
annihilator duality construct unrestricted solutions on the whole cut-profile
pair space. Bounded derivative ranks are treated separately; compression
and private-channel factorization remain further obligations.
-/

namespace Lax342547.ResponseSolvability


open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PairedAnnihilators Lax342547.BarredSpaces
open Lax342547.ChannelChanges Lax342547.TableContractions Lax342547.DerivativeResponses
open Lax342547.TableSpaces

open Lax342547.SelectedRemoval Lax342547.PairedRecipes Lax342547.RecipeResiduals
open Lax342547.PinLabelExclusions Lax342547.ProjectedPins Lax342547.RawBaselines

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

abbrev Parameters (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2) :=
  Lax342547.PureObstructions.Parameters W P U V ×
    (PlusParameters W P Q U z × MinusParameters W P Q V z)

axiom full_add (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (β β' : Lax342547.PureObstructions.Parameters W P U V)
    (δ δ' : PlusParameters W P Q U z) (ε ε' : MinusParameters W P Q V z) :
    fullResponse W P Q U V F z (β + β') (δ + δ') (ε + ε') =
      fullResponse W P Q U V F z β δ ε + fullResponse W P Q U V F z β' δ' ε'

axiom full_smul (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (a : Binary) (β : Lax342547.PureObstructions.Parameters W P U V)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    fullResponse W P Q U V F z (a • β) (a • δ) (a • ε) =
      a • fullResponse W P Q U V F z β δ ε

axiom dual_range {K A X : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (R : A →ₗ[K] Module.Dual K X) (t : Module.Dual K X)
    (h : ∀ x, (∀ a, R a x = 0) → t x = 0) : ∃ a, R a = t

axiom solvable_of_annihilator_zero (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (t : Module.Dual Binary (Fin 2 → Profile k n b degree))
    (h : ∀ x, Annihilates W P Q U V F z x → t x = 0) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε = t

axiom selected_part_correct (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) (i : Fin 2) :
    selectedPart W c i ∈ correctSpace W P i

axiom obstruction_correct {K : ℕ} (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∀ i, x i ∈ correctSpace W P i

axiom unrestricted_solution {K : ℕ} (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree)
    (t : Fin 2 → Module.Dual Binary (Profile k n b degree))
    (ht : ∀ i, correctSpace W P i ≤ LinearMap.ker (t i)) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε = ∑ i, (t i).comp (LinearMap.proj i)

axiom recipe_solution [Fintype N] {K : ℕ} {E : Moment k n b degree}
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
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2) :
    ∃ β δ ε, fullResponse W P Q U V F z β δ ε =
      ∑ i, (residual W D L R F i z).comp (LinearMap.proj i)

end Lax342547.ResponseSolvability
