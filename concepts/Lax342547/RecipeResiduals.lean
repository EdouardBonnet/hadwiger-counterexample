import Lax342547.FrozenValues

/-!
---
title: Gradient residuals vanish on effective profiles and selected atoms
type: definition and theorem
---
The scalar recipe and binary prescriptions make the target difference
zero on the effective space and the span of every selected atom at an
endpoint. This is the domain on which correctness is already established
before the whole-space annihilator argument.
-/

namespace Lax342547.RecipeResiduals

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.SmallTables
open Lax342547.TableContractions Lax342547.RawBaselines Lax342547.ConcreteRecipes

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

noncomputable def residual {H : Type} [Fintype H]
    (W : Lists k n b degree r hr) (D : Testers (k := k) (b := b) (degree := degree) hr)
    {copies : ℕ} (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (i z : Fin 2) :
    Profile k n b degree →ₗ[Binary] Binary :=
  D.role + gradient D L R (leftWitness W i z) - fullContraction F (Profile k n b degree) i z

def correctSpace {H N : Type} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N) (i : Fin 2) :
    Submodule Binary (Profile k n b degree) :=
  effective (Profile k n b degree) P i ⊔
    Submodule.span Binary (Set.range (fun x : Position W i => (endpointAtoms W i x).profile))

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

axiom selected_gradients (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oB : Unit (H := H) (N := N) (E := E)) (i : Fin 2)
    (h : RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (z z' : Fin 2) (t : Fin (W.length i z')) :
    D.role (W.left i z' t).profile +
      gradient D L R (leftWitness W i z) (W.left i z' t).profile =
      if z = z' then 0 else ownContraction oB z' (W.right i z' t).profile

axiom residual_correct (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (h : ScalarRecipe W D L R oA oB T A B) (htable : Extends F T)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i)) :
    ∀ i z, correctSpace W P i ≤ LinearMap.ker (residual W D L R F i z)

end Lax342547.RecipeResiduals
