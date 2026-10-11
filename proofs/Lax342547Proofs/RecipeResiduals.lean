import Lax342547.RecipeResiduals
import Lax342547.FrozenValues
import Lax342547.TableContractions

namespace Lax342547Proofs.RecipeResiduals

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.SmallTables
open Lax342547.TableContractions Lax342547.RawBaselines Lax342547.ConcreteRecipes Lax342547.RecipeResiduals

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

/--
---
conclusion: Lax342547.RecipeResiduals.selected_gradients
---
The four row-sum identities at one endpoint are precisely the two-list
self and opposite gradient equations. Enumerate the two possible target
endpoints to identify their prescribed opposite p values.
-/
theorem selected_gradients (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oB : Unit (H := H) (N := N) (E := E)) (i : Fin 2)
    (h : RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (z z' : Fin 2) (t : Fin (W.length i z')) :
    D.role (W.left i z' t).profile +
      gradient D L R (leftWitness W i z) (W.left i z' t).profile =
      if z = z' then 0 else ownContraction oB z' (W.right i z' t).profile := by
  fin_cases z <;> fin_cases z'
  · simpa [endpointAtoms, leftWitness] using h.1 t
  · simpa [endpointAtoms, leftWitness, oppositeP] using h.2.1 t
  · simpa [endpointAtoms, leftWitness, oppositeP] using h.2.2.2 t
  · simpa [endpointAtoms, leftWitness] using h.2.2.1 t

/--
---
conclusion: Lax342547.RecipeResiduals.residual_correct
---
The effective equation agrees with the full contraction because the
baseline extends the table. On selected atoms the binary gradient
prescriptions agree with the frozen contraction values. Linearity makes
the residual zero on the sum of those two subspaces.
-/
theorem residual_correct (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (h : ScalarRecipe W D L R oA oB T A B) (htable : Lax342547.TableContractions.Extends F T)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i)) :
    ∀ i z, correctSpace W P i ≤ LinearMap.ker (residual W D L R F i z) := by
  intro i z
  apply sup_le
  · intro x hx
    change D.role x + gradient D L R (leftWitness W i z) x -
      fullContraction F (Profile k n b degree) i z x = 0
    rw [h.effectiveLeft i z ⟨x, hx⟩,
      Lax342547.TableContractions.star_extension T F htable (Profile k n b degree) i z ⟨x, hx⟩,
      ← add_assoc, ZModModule.add_self, zero_add, sub_self]
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change D.role (endpointAtoms W i x).profile +
      gradient D L R (leftWitness W i z) (endpointAtoms W i x).profile -
      fullContraction F (Profile k n b degree) i z (endpointAtoms W i x).profile = 0
    apply sub_eq_zero.mpr
    cases x with
    | inl t =>
      simp only [endpointAtoms, Sum.elim_inl]
      rw [Lax342547.FrozenValues.selected_values W P Q oA oB F hfrozen hkeys i z 0 t]
      exact Lax342547.RecipeResiduals.selected_gradients W D L R oB i (hgradients i) z 0 t
    | inr t =>
      simp only [endpointAtoms, Sum.elim_inr]
      rw [Lax342547.FrozenValues.selected_values W P Q oA oB F hfrozen hkeys i z 1 t]
      exact Lax342547.RecipeResiduals.selected_gradients W D L R oB i (hgradients i) z 1 t

end Lax342547Proofs.RecipeResiduals
