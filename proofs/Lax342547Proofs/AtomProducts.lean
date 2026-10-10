import Lax342547.AtomProducts
import Lax342547Proofs.WitnessAtoms

namespace Lax342547Proofs.AtomProducts

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms
open Lax342547.BinaryPrescriptions Lax342547.AtomProducts

theorem pair_outer {B : Type} [Fintype B] (u v x y : B → Binary) :
    matrixPair (Matrix.vecMulVec u v) (Matrix.vecMulVec x y) = dotProduct u x * dotProduct v y := by
  simp only [matrixPair, LinearMap.sum_apply, LinearMap.smul_apply, matrixEntry,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Matrix.vecMulVec_apply, dotProduct,
    Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pair_sandwich {B : Type} [Fintype B] [DecidableEq B]
    (L R : Matrix B B Binary) (u v : B → Binary) :
    matrixPair (Matrix.vecMulVec u u) (L * Matrix.vecMulVec v v * R.transpose) =
      L.toBilin' u v * R.toBilin' u v := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, pair_outer]
  simp only [Matrix.toBilin'_apply']

/--
---
conclusion: Lax342547.AtomProducts.mixing_atoms
---
On an incident component the atom is its point outer product, and it is
zero on every other component. Pairing two outer products through L and
R factors into their two ordered bilinear evaluations.
-/
theorem mixing_atoms {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : PointAtom k n b degree) :
    mixingForm L R x.profile y.profile = productSum (evaluatedBits L) (evaluatedBits R) x y := by
  classical
  rw [ConcreteCut.mixingForm_apply]
  simp only [productSum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  simp only [PointAtom.profile, Atoms.atom_component]
  by_cases hx : x.tag ∈ e.val <;> by_cases hy : y.tag ∈ f.val
  · simp only [hx, hy, if_pos]
    rw [show pointMoment selectorEval x.label x.base = Matrix.vecMulVec x.vector x.vector from rfl,
      show pointMoment selectorEval y.label y.base = Matrix.vecMulVec y.vector y.vector from rfl]
    simpa only [evaluatedBits, hx, hy, and_self, if_true] using
      pair_sandwich (L j e f) (R j e f) x.vector y.vector
  · simp [evaluatedBits, hx, hy, matrixPair, matrixEntry]
  · simp [evaluatedBits, hx, hy, matrixPair, matrixEntry]
  · simp [evaluatedBits, hx, hy, matrixPair, matrixEntry]

/--
---
conclusion: Lax342547.AtomProducts.gradient_atoms
---
Separate the tester part from the two ordered mixer sums. The numerical
tester record determines the first part; the ordered product identities
determine the other two exactly.
-/
theorem gradient_atoms {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : PointAtom k n b degree) :
    gradient D L R x.profile y.profile = testerEntry (x.numerical hr) (y.numerical hr) +
      productSum (evaluatedBits L) (evaluatedBits R) x y +
      productSum (evaluatedBits L) (evaluatedBits R) y x := by
  obtain ⟨hx, hxa, hxb⟩ := WitnessAtoms.atom_testers D x
  obtain ⟨hy, hya, hyb⟩ := WitnessAtoms.atom_testers D y
  simp [gradient, Lax342547.GradientForm.form, GradientForm.rankOne_apply, LinearMap.sum_apply,
    mixing_atoms, testerEntry, hx, hy, hxa, hxb, hya, hyb]

/--
---
conclusion: Lax342547.AtomProducts.gradient_of_prescriptions
---
Only allowed distinct-atom evaluations are tested. Outside the incident
stars both prescribed bits vanish. On the diagonal each ordered product
occurs twice and cancels, so no same-atom evaluations need be prescribed.
-/
theorem gradient_of_prescriptions {I : Type} {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (atoms : I → PointAtom k n b degree) (lbits rbits : I → I → ProductIndex k J → Binary)
    (hzero : ∀ x y t, ¬ allowedIndex ((atoms x).numerical hr) ((atoms y).numerical hr) t →
      lbits x y t = 0 ∧ rbits x y t = 0)
    (hbits : ∀ x y, x ≠ y → ∀ t,
      allowedIndex ((atoms x).numerical hr) ((atoms y).numerical hr) t →
      (L t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = lbits x y t ∧
      (R t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = rbits x y t) :
    ∀ x y, gradient D L R (atoms x).profile (atoms y).profile =
      testerEntry ((atoms x).numerical hr) ((atoms y).numerical hr) +
        productSum lbits rbits x y + productSum lbits rbits y x := by
  classical
  have hsum (x y : I) (hxy : x ≠ y) :
      productSum (evaluatedBits L) (evaluatedBits R) (atoms x) (atoms y) = productSum lbits rbits x y := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : allowedIndex ((atoms x).numerical hr) ((atoms y).numerical hr) t
    · have hb := hbits x y hxy t ht
      simpa only [evaluatedBits, show (atoms x).tag ∈ t.2.1.val ∧ (atoms y).tag ∈ t.2.2.val from ht,
        and_self, if_true] using congrArg₂ (· * ·) hb.1 hb.2
    · have hb := hzero x y t ht
      simp only [allowedIndex, PointAtom.numerical] at ht
      simp [evaluatedBits, ht, hb.1, hb.2]
  intro x y
  rw [gradient_atoms]
  by_cases hxy : x = y
  · subst y
    simp only [add_assoc, ZModModule.add_self, add_zero]
  · rw [hsum x y hxy, hsum y x (Ne.symm hxy)]

end Lax342547Proofs.AtomProducts
