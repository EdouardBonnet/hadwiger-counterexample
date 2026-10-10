import Lax342547.WitnessAtoms
import Lax342547.RawContractions
import Mathlib.Data.Fintype.Sigma

/-!
---
title: Full paired witness lists and scalar recipe equations
type: definition and theorem
---
Four cross pairs carry matched lists of one to seven actual point atoms.
Freshness holds across both lists at each endpoint. The scalar recipe
records odd diagonal sums, role parity, both effective-space equations,
and both coupled endpoint equations, using the actual contractions.
-/

namespace Lax342547.PairedWitnesses

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms Lax342547.WitnessAtoms
open Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.SmallTables Lax342547.TableContractions

def diagonalBit {k n b degree r : ℕ} (hr : 2 * r ≤ n) (x : PointAtom k n b degree) : Binary :=
  eta hr (pointMoment (selectorEval (degree := degree)) x.label x.base)

structure Lists (k n b degree r : ℕ) (hr : 2 * r ≤ n) where
  length : Fin 2 → Fin 2 → ℕ
  positive : ∀ i z, 1 ≤ length i z
  short : ∀ i z, length i z ≤ 7
  left : ∀ i z, Fin (length i z) → PointAtom k n b degree
  right : ∀ i z, Fin (length i z) → PointAtom k n b degree
  same_tag : ∀ i z t, (left i z t).tag = (right i z t).tag
  same_diagonal : ∀ i z t, diagonalBit hr (left i z t) = diagonalBit hr (right i z t)
  left_fresh : ∀ i, Function.Injective (fun t : Σ z, Fin (length i z) => (left i t.1 t.2).label)
  right_fresh : ∀ z, Function.Injective (fun t : Σ i, Fin (length i z) => (right t.1 z t.2).label)

def other (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

noncomputable def leftRepresentation (W : Lists k n b degree r hr) (i z : Fin 2) :
    Representation k n b degree :=
  ∑ t, atomRepresentation (W.left i z t).tag (W.left i z t).label
    (W.left i z t).base (W.left i z t).supported

noncomputable def rightRepresentation (W : Lists k n b degree r hr) (i z : Fin 2) :
    Representation k n b degree :=
  ∑ t, atomRepresentation (W.right i z t).tag (W.right i z t).label
    (W.right i z t).base (W.right i z t).supported

noncomputable def leftWitness (W : Lists k n b degree r hr) (i z : Fin 2) : Profile k n b degree :=
  ∑ t, (W.left i z t).profile

noncomputable def rightWitness (W : Lists k n b degree r hr) (i z : Fin 2) : Profile k n b degree :=
  ∑ t, (W.right i z t).profile

def FreshAgainst (W : Lists k n b degree r hr) (A B : Fin 2 → Finset (Fin b → Binary)) : Prop :=
  (∀ i z t, (W.left i z t).label ∉ A i) ∧ (∀ i z t, (W.right i z t).label ∉ B z)

variable {H N : Type} [Fintype H] [Fintype N]
  {E : Moment k n b degree}

abbrev Unit := Fin 2 → Component (Tag k) → Frame (Coordinate k n b degree) H N E

noncomputable def ownContraction (o : Unit (H := H) (N := N) (E := E)) (i : Fin 2) :
    Profile k n b degree →ₗ[Binary] Binary :=
  (profileContraction (o (other i))).comp ((profileMap (o i)).comp (Profile k n b degree).subtype)

def MatchedKeys (W : Lists k n b degree r hr) (oA oB : Unit (H := H) (N := N) (E := E)) : Prop :=
  ∀ i z t (e : Component (Tag k)), (W.left i z t).tag ∈ e.val →
    (oA i e).P.mulVec (W.left i z t).vector = (oB z e).P.mulVec (W.right i z t).vector ∧
    (oA i e).Q.mulVec (W.left i z t).vector = (oB z e).Q.mulVec (W.right i z t).vector

structure ScalarRecipe (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary)) : Prop where
  fresh : FreshAgainst W A B
  odd : ∀ i z, (∑ t, diagonalBit hr (W.left i z t)) = 1
  roles : ∀ i z, D.role (leftWitness W i z) + D.role (rightWitness W i z) = 1
  effectiveLeft : ∀ i z (x : effective (Profile k n b degree) P i),
    gradient D L R (leftWitness W i z) x.val = D.role x.val +
      starContraction T (Profile k n b degree) i z x
  effectiveRight : ∀ i z (x : effective (Profile k n b degree) Q z),
    gradient D L R (rightWitness W i z) x.val = D.role x.val +
      starContraction (flipTable T) (Profile k n b degree) z i x
  coupledLeft : ∀ i z,
    (ownContraction oA i + D.role) (leftWitness W i z) =
      (ownContraction oA (other i) + D.role) (leftWitness W (other i) z)
  coupledRight : ∀ i z,
    (ownContraction oB z + D.role) (rightWitness W i z) =
      (ownContraction oB (other z) + D.role) (rightWitness W i (other z))

axiom list_budgets (W : Lists k n b degree r hr) :
    (∀ i, Fintype.card (Σ z, Fin (W.length i z)) ≤ 14) ∧
      ∀ z, Fintype.card (Σ i, Fin (W.length i z)) ≤ 14

axiom diagonal_sums (W : Lists k n b degree r hr) (i z : Fin 2) :
    chiStar hr (leftRepresentation W i z) = ∑ t, diagonalBit hr (W.left i z t) ∧
    chiStar hr (rightRepresentation W i z) = ∑ t, diagonalBit hr (W.left i z t)

axiom tensor_sharing (W : Lists k n b degree r hr)
    (oA oB : Unit (H := H) (N := N) (E := E)) (hkeys : MatchedKeys W oA oB) (i z : Fin 2) :
    profileMap (oA i) (leftWitness W i z).val = profileMap (oB z) (rightWitness W i z).val

end Lax342547.PairedWitnesses
