import Lax342547.PairedWitnesses
import Lax342547Proofs.Atoms
import Lax342547.Atoms

namespace Lax342547Proofs.PairedWitnesses

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms Lax342547.WitnessAtoms
open Lax342547.RawFrames Lax342547.PairedWitnesses

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

/--
---
conclusion: Lax342547.PairedWitnesses.list_budgets
---
Each endpoint has exactly two lists, each of length at most seven. The
dependent sum of their position types therefore has at most fourteen elements.
-/
theorem list_budgets (W : Lists k n b degree r hr) :
    (∀ i, Fintype.card (Σ z, Fin (W.length i z)) ≤ 14) ∧
      ∀ z, Fintype.card (Σ i, Fin (W.length i z)) ≤ 14 := by
  constructor
  · intro i
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ _z : Fin 2, 7 := Finset.sum_le_sum (fun z _ => W.short i z)
      _ = 14 := by simp
  · intro z
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ _i : Fin 2, 7 := Finset.sum_le_sum (fun i _ => W.short i z)
      _ = 14 := by simp

/--
---
conclusion: Lax342547.PairedWitnesses.diagonal_sums
---
The diagonal functional is linear on the chosen representation. Evaluate
each atom and use the pairing's positionwise equality of diagonal bits.
-/
theorem diagonal_sums (W : Lists k n b degree r hr) (i z : Fin 2) :
    chiStar hr (leftRepresentation W i z) = ∑ t, diagonalBit hr (W.left i z t) ∧
    chiStar hr (rightRepresentation W i z) = ∑ t, diagonalBit hr (W.left i z t) := by
  constructor
  · simp only [leftRepresentation, map_sum, Atoms.atom_diagonal, diagonalBit]
  · calc
      _ = ∑ t, diagonalBit hr (W.right i z t) := by
        simp only [rightRepresentation, map_sum, Atoms.atom_diagonal, diagonalBit]
      _ = _ := Finset.sum_congr rfl (fun t _ => (W.same_diagonal i z t).symm)

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

theorem atom_sharing (F G : Component (Tag k) → Frame (Coordinate k n b degree) H N E)
    (x y : PointAtom k n b degree) (htag : x.tag = y.tag)
    (hkeys : ∀ e, x.tag ∈ e.val → (F e).P.mulVec x.vector = (G e).P.mulVec y.vector ∧
      (F e).Q.mulVec x.vector = (G e).Q.mulVec y.vector) :
    profileMap F x.profile.val = profileMap G y.profile.val := by
  classical
  ext e a b
  change (sandwich (F e).P (F e).Q (x.profile.val e)) a b =
    (sandwich (G e).P (G e).Q (y.profile.val e)) a b
  simp only [PointAtom.profile, Lax342547.Atoms.atom_component]
  by_cases he : x.tag ∈ e.val
  · have hey : y.tag ∈ e.val := htag ▸ he
    simp only [he, hey, if_pos]
    have hxy := hkeys e he
    change ((F e).P * Matrix.vecMulVec x.vector x.vector * (F e).Q.transpose) a b =
      ((G e).P * Matrix.vecMulVec y.vector y.vector * (G e).Q.transpose) a b
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hxy.1, hxy.2]
  · have hey : y.tag ∉ e.val := htag ▸ he
    simp [he, hey, sandwich]

/--
---
conclusion: Lax342547.PairedWitnesses.tensor_sharing
---
On each atom's tag star, matched plus and minus keys give equal outer
products. Off the star both atom components vanish. Sum these exact
tensor identities along each paired list.
-/
theorem tensor_sharing (W : Lists k n b degree r hr)
    (oA oB : Unit (H := H) (N := N) (E := E)) (hkeys : MatchedKeys W oA oB) (i z : Fin 2) :
    profileMap (oA i) (leftWitness W i z).val = profileMap (oB z) (rightWitness W i z).val := by
  change ((profileMap (oA i)).comp (Profile k n b degree).subtype) (leftWitness W i z) =
    ((profileMap (oB z)).comp (Profile k n b degree).subtype) (rightWitness W i z)
  simp only [leftWitness, rightWitness, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact atom_sharing (oA i) (oB z) (W.left i z t) (W.right i z t)
    (W.same_tag i z t) (hkeys i z t)

end Lax342547Proofs.PairedWitnesses
