import Lax342547.OrderedMixerLaw
import Lax342547Proofs.AtomDirections
import Lax342547Proofs.MixerCompatibility
import Lax342547Proofs.FiniteLinearLaw

namespace Lax342547Proofs.OrderedMixerLaw

set_option backward.isDefEq.respectTransparency false

open Lax342547.OrderedMixerLaw

variable {K I N P : Type} [Field K] [Fintype I] [Fintype N] [Fintype P]

theorem full_restriction_surjective (D : Matrix I N K) (hD : Function.Injective D.mulVec) :
    Function.Surjective (fun L : Matrix I I K => D.transpose * L * D) := by
  classical
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse D hD
  have hDU : D.transpose * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  intro A
  refine ⟨U.transpose * A * U, ?_⟩
  calc
    _ = (D.transpose * U.transpose) * A * (U * D) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hDU, hU, Matrix.one_mul, Matrix.mul_one]

/--
---
conclusion: Lax342547.OrderedMixerLaw.orders_surjective
---
Take a left inverse of the combined columns. Pull back a block matrix
whose off-diagonal blocks are the two prescribed ordered restrictions.
-/
theorem orders_surjective (D : Matrix I N K) (E : Matrix I P K)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec) :
    Function.Surjective (orders D E) := by
  classical
  rintro ⟨A, B⟩
  obtain ⟨L, hL⟩ := full_restriction_surjective (Matrix.fromCols D E) hDE
    (Matrix.fromBlocks 0 A B 0)
  dsimp only at hL
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at hL
  have hb := Matrix.fromBlocks_inj.mp hL
  exact ⟨L, Prod.ext hb.2.1 hb.2.2.1⟩

omit [Fintype I] [Fintype N] [Fintype P] in
theorem parity_surjective (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Surjective (parity (N := N) (P := P) a b) := by
  intro A
  rcases hab with ha | hb
  · refine ⟨(a⁻¹ • A, 0), ?_⟩
    simp [parity, smul_smul, ha]
  · refine ⟨(0, b⁻¹ • A.transpose), ?_⟩
    simp [parity, smul_smul, hb]

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AtomDirections

/--
---
conclusion: Lax342547.OrderedMixerLaw.orders_uniform
---
The ordered-block observation is linear and surjective, so its uniform
input law pushes forward to the uniform law on the full product space.
-/
theorem orders_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (D : Matrix I N Binary) (E : Matrix I P Binary)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (orders D E) =
      PMF.uniformOfFintype (Matrix N P Binary × Matrix P N Binary) :=
  FiniteLinearLaw.uniform_image_of_surjective _ (orders_surjective D E hDE)

/--
---
conclusion: Lax342547.OrderedMixerLaw.ordered_parity_uniform
---
Any nonzero coefficient selects a surjective linear combination of the
independent forward and reverse blocks, with the reverse transposed to
the common input order.
-/
theorem ordered_parity_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (D : Matrix I N Binary) (E : Matrix I P Binary)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec)
    (a b : Binary) (hab : a ≠ 0 ∨ b ≠ 0) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map ((parity a b).comp (orders D E)) =
      PMF.uniformOfFintype (Matrix N P Binary) :=
  FiniteLinearLaw.uniform_image_of_surjective _
    ((parity_surjective a b hab).comp (orders_surjective D E hDE))

/--
---
conclusion: Lax342547.OrderedMixerLaw.atom_orders_uniform
---
Distinct selector labels have independent combined free-direction columns.
Apply the ordered-block law to these concrete Z-direction matrices.
-/
theorem atom_orders_uniform {k n b degree : ℕ} (hd : 1 ≤ degree)
    (s t : Fin b → Binary) (hst : s ≠ t) :
    (PMF.uniformOfFintype (Moment k n b degree)).map
      (orders (blockDirections s free) (blockDirections t free)) =
      PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary × Matrix (Fin n) (Fin n) Binary) := by
  apply orders_uniform
  apply AtomDirections.distinct_directions_injective hd s t hst free
  intro i j hij
  simpa [free] using hij

end Lax342547Proofs.OrderedMixerLaw
