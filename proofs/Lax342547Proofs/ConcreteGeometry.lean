import Lax342547.ConcreteGeometry
import Lax342547Proofs.MomentSpace
import Lax342547Proofs.GradientForm
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.ConcreteGeometry

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

variable {k n b degree r : ℕ}

@[simp] theorem eval_empty (s : Fin b → Binary) : selectorEval s (emptySelector b degree) = 1 := by
  simp [selectorEval, emptySelector]

@[simp] theorem eval_bit (h : 1 ≤ degree) (a : Fin b) (s : Fin b → Binary) :
    selectorEval s (bitSelector h a) = s a := by simp [selectorEval, bitSelector]

theorem blockTester_apply (h : 2 * r ≤ n) (c : Fin n → Base k n) (w : Moment k n b degree) :
    blockTester h c w = ∑ ρ : Fin r,
      w (emptySelector b degree, some (c (pairLeft h ρ)))
        (emptySelector b degree, some (c (pairRight h ρ))) := by
  simp [blockTester, matrixEntry, LinearMap.sum_apply]

theorem blockTester_point (h : 2 * r ≤ n) (c : Fin n → Base k n)
    (s : Fin b → Binary) (z : Base k n → Binary) :
    blockTester (b := b) (degree := degree) h c (pointMoment selectorEval s z) =
      ∑ ρ : Fin r, z (c (pairLeft h ρ)) * z (c (pairRight h ρ)) := by
  simp [blockTester_apply, pointMoment, point, baseEval]

theorem ordinaryTester_common_zero (h : 2 * r ≤ n) (d t : Tag k)
    {w : Moment k n b degree} (hw : w ∈ momentSpace selectorEval (commonBase k n)) :
    blockTester h (ordinary d t) w = 0 := by
  rw [blockTester_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  exact MomentSpace.entries_zero selectorEval hw _ _ (Or.inl (by change ¬False; exact not_false))

theorem blockForm_apply (h : 2 * r ≤ n) (c : Fin n → Base k n) (v w : Vector k n b degree) :
    blockForm h c v w = ∑ ρ : Fin r,
      v (emptySelector b degree, some (c (pairLeft h ρ))) *
        w (emptySelector b degree, some (c (pairRight h ρ))) := by
  simp [blockForm, GradientForm.rankOne_apply, LinearMap.sum_apply]

theorem testerForm_point (h : 2 * r ≤ n) (s : Fin b → Binary) (z : Base k n → Binary) :
    testerForm (b := b) (degree := degree) h (point selectorEval s z) (point selectorEval s z) =
      eta (degree := degree) h (pointMoment selectorEval s z) := by
  simp [testerForm, eta, etaO, LinearMap.sum_apply, blockForm_apply, blockTester_apply, pointMoment]

theorem sharpForm_apply (h : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (v w : Vector k n b degree) :
    sharpForm h M v w = ∑ a, ∑ i, ∑ j, M a i j *
      (v (bitSelector h a, some (sharp i)) * w (emptySelector b degree, some (sharp j)) +
        v (emptySelector b degree, some (sharp i)) * w (bitSelector h a, some (sharp j))) := by
  simp [sharpForm, GradientForm.rankOne_apply, LinearMap.sum_apply, mul_add]

theorem sharpForm_point (h : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s t : Fin b → Binary) (z y : Base k n → Binary) :
    sharpForm h M (point selectorEval s z) (point selectorEval t y) =
      ∑ a, (s a + t a) * (∑ i, ∑ j, z (sharp i) * M a i j * y (sharp j)) := by
  rw [sharpForm_apply]
  simp only [point, baseEval, eval_bit, eval_empty, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sharpForm_point_self (h : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (s : Fin b → Binary) (z : Base k n → Binary) :
    sharpForm h M (point selectorEval s z) (point selectorEval s z) = 0 := by
  simp [sharpForm_point, ZModModule.add_self]

set_option backward.isDefEq.respectTransparency false in
theorem matrixPair_point {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    [DecidableEq (Coord × Option Base)]
    (E : Matrix (Coord × Option Base) (Coord × Option Base) Binary)
    (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    matrixPair E (pointMoment p s z) = E.toBilin' (point p s z) (point p s z) := by
  classical
  simp only [matrixPair, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    matrixEntry, LinearMap.coe_mk, AddHom.coe_mk, pointMoment, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.ConcreteGeometry.selfGram_moments
---
The ordered tester form has precisely the tester values on point moments.
The # form vanishes on equal point inputs, since each selector difference
is zero. Linearity extends this equality to their full span.
-/
theorem selfGram_moments (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (w : Moment k n b degree)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ) :
    matrixPair (selfGram hr hd M) w = eta hr w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, z, _, rfl⟩ := hw
    rw [matrixPair_point, selfGram, Matrix.toBilin'_toMatrix']
    simp [testerForm_point, sharpForm_point_self]
  | zero => simp
  | add w v _ _ hw hv => simp [hw, hv]
  | smul c w _ hw => simp [hw]

theorem testerForm_changeZ (hr : 2 * r ≤ n) (A : Matrix (Fin n) (Fin n) Binary)
    (v w : Vector k n b degree) :
    testerForm hr (changeZ A v) (changeZ A w) = testerForm hr v w := by
  simp [testerForm, LinearMap.sum_apply, blockForm_apply, changeZ, ordinary, shared]

theorem sharpForm_changeZ (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (A : Matrix (Fin n) (Fin n) Binary) (v w : Vector k n b degree) :
    sharpForm hd M (changeZ A v) (changeZ A w) = sharpForm hd M v w := by
  simp [sharpForm_apply, changeZ, sharp]

/--
---
conclusion: Lax342547.ConcreteGeometry.selfGram_changeZ
---
Every coordinate read by the ordered tester and # forms is unchanged by
the Z-coordinate map. This proves the matrix identity for any linear Z
change, in particular for every invertible one.
-/
theorem selfGram_changeZ (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (A : Matrix (Fin n) (Fin n) Binary) :
    (changeZ A).toMatrix'.transpose * selfGram (k := k) (b := b) hr hd M *
      (changeZ A).toMatrix' = selfGram hr hd M := by
  unfold selfGram
  rw [← LinearMap.BilinForm.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact congrArg₂ (· + ·) (testerForm_changeZ hr A v w) (sharpForm_changeZ hd M A v w)

end Lax342547Proofs.ConcreteGeometry
