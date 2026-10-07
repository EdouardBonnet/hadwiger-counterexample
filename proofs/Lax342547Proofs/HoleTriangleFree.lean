import Lax342547.HoleTriangleFree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.HoleTriangleFree

open Lax342547.HoleRelation

universe u v w
variable {Ω : Type u} {X : Type v} {V : Type w}
variable [AddCommGroup X] [Module (ZMod 2) X]
variable [AddCommGroup V] [Module (ZMod 2) V]

theorem hole_symmetric (D : HoleData Ω X V) : (∀ ⦃i j⦄, Hole D i j → Hole D j i) := by
  rintro i j ⟨x, y, hxy, hx, hy, hpar⟩
  exact ⟨y, x, hxy.symm, hy, hx, by simpa [add_comm] using hpar⟩

theorem hole_irreflexive (D : HoleData Ω X V) : (∀ i, ¬ Hole D i i) := by
  rintro i ⟨x, y, hxy, _, _, hpar⟩
  have h : x = y := D.injective i hxy
  subst y
  simp [ZModModule.add_self] at hpar

theorem hole_triangle_free (D : HoleData Ω X V) (i j k : Ω)
    (hij : Hole D i j) (hjk : Hole D j k) : ¬ Hole D k i := by
  rintro ⟨z, z', hki, hki₁, hki₂, hz⟩
  obtain ⟨x, x', hij, hij₁, hij₂, hx⟩ := hij
  obtain ⟨y, y', hjk, hjk₁, hjk₂, hy⟩ := hjk
  have e₁ : D.a y + D.T x' y = D.a y' + D.T z y' := by
    calc
      D.a y + D.T x' y = D.u i (D.U j y) := (hij₂ y).symm
      _ = D.u i (D.U k y') := congrArg (D.u i) hjk
      _ = D.a y' + D.T z y' := hki₁ y'
  have e₂ : D.a z + D.T y' z = D.a z' + D.T x z' := by
    calc
      D.a z + D.T y' z = D.u j (D.U k z) := (hjk₂ z).symm
      _ = D.u j (D.U i z') := congrArg (D.u j) hki
      _ = D.a z' + D.T x z' := hij₁ z'
  have e₃ : D.a x + D.T z' x = D.a x' + D.T y x' := by
    calc
      D.a x + D.T z' x = D.u k (D.U i x) := (hki₂ x).symm
      _ = D.u k (D.U j x') := congrArg (D.u k) hij
      _ = D.a x' + D.T y x' := hjk₁ x'
  rw [D.symmetric x' y] at e₁
  rw [D.symmetric y' z] at e₂
  rw [D.symmetric z' x] at e₃
  have hbad : (0 : ZMod 2) = 1 := by
    linear_combination (norm := ring_nf) e₁ + e₂ + e₃ - hx - hy - hz
    simp only [show (2 : ZMod 2) = 0 from rfl,
      show (4 : ZMod 2) = 0 from rfl, mul_zero, neg_zero, zero_add]
  exact zero_ne_one hbad

/--
---
conclusion: Lax342547.HoleTriangleFree.hole_properties
---
Symmetry exchanges the witnesses. Injectivity rules out loops. Evaluating
the functional equations on the other witnesses around a triangle cancels
the symmetric bilinear terms and contradicts the three parity equations.
-/
theorem hole_properties (D : HoleData Ω X V) :
    (∀ ⦃i j⦄, Hole D i j → Hole D j i) ∧ (∀ i, ¬ Hole D i i) ∧
      ∀ i j k, Hole D i j → Hole D j k → ¬ Hole D k i :=
  ⟨hole_symmetric D, hole_irreflexive D, hole_triangle_free D⟩

end Lax342547Proofs.HoleTriangleFree
