import Lax342547.PairedWitnesses
import Lax342547.ConcreteRecipes

/-!
---
title: Binary prescriptions at all endpoints of a paired scalar recipe
type: lemma
---
Swapping the units preserves the full scalar recipe. At each endpoint,
its two role equations and the opposite unit's coupled equation give
formal ordered mixer bits realizing the required selected-atom gradients.
These are prescriptions; their occurrence is a separate probability problem.
-/

namespace Lax342547.PairedRecipes

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms
open Lax342547.PairedWitnesses Lax342547.ConcreteRecipes
open Lax342547.ExactPins Lax342547.SmallTables Lax342547.TableContractions

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

def flip (W : Lists k n b degree r hr) : Lists k n b degree r hr where
  length i z := W.length z i
  positive i z := W.positive z i
  short i z := W.short z i
  left i z := W.right z i
  right i z := W.left z i
  same_tag i z t := (W.same_tag z i t).symm
  same_diagonal i z t := (W.same_diagonal z i t).symm
  left_fresh := W.right_fresh
  right_fresh := W.left_fresh

abbrev Position (W : Lists k n b degree r hr) (i : Fin 2) :=
  Fin (W.length i 0) ⊕ Fin (W.length i 1)

def endpointAtoms (W : Lists k n b degree r hr) (i : Fin 2) :
    Position W i → PointAtom k n b degree := Sum.elim (W.left i 0) (W.left i 1)

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

noncomputable def oppositeP (W : Lists k n b degree r hr)
    (oB : Unit (H := H) (N := N) (E := E)) (i : Fin 2) : Position W i → Binary :=
  Sum.elim (fun t => ownContraction oB 0 (W.right i 0 t).profile)
    (fun t => ownContraction oB 1 (W.right i 1 t).profile)

def Prescriptions (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (oB : Unit (H := H) (N := N) (E := E)) (copies : ℕ) : Prop :=
  ∀ i, ∃ lbits rbits : Position W i → Position W i → ProductIndex k copies → Binary,
    (∀ x y t, ¬ allowedIndex ((endpointAtoms W i x).numerical hr)
      ((endpointAtoms W i y).numerical hr) t → lbits x y t = 0 ∧ rbits x y t = 0) ∧
    ∀ L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree,
      (∀ x y, x ≠ y → ∀ t, allowedIndex ((endpointAtoms W i x).numerical hr)
        ((endpointAtoms W i y).numerical hr) t →
        (L t.1 t.2.1 t.2.2).toBilin' (endpointAtoms W i x).vector
          (endpointAtoms W i y).vector = lbits x y t ∧
        (R t.1 t.2.1 t.2.2).toBilin' (endpointAtoms W i x).vector
          (endpointAtoms W i y).vector = rbits x y t) →
      RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i)

axiom endpoint_fresh (W : Lists k n b degree r hr) (i : Fin 2) :
    Function.Injective (fun x : Position W i => (endpointAtoms W i x).label)

axiom flip_recipe (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (h : ScalarRecipe W D L R oA oB T A B) :
    ScalarRecipe (flip W) D L R oB oA (flipTable T) B A

axiom paired_prescriptions (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (hk : 0 < k) (hcopies : 0 < copies)
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (h : ScalarRecipe W D L R oA oB T A B) :
    Prescriptions W D oB copies ∧ Prescriptions (flip W) D oA copies

end Lax342547.PairedRecipes
