import Lax342547.QuadraticDegree
import Mathlib.Data.Matrix.Basis
import Lax342547.BooleanWeight
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.QuadraticDegree
set_option maxHeartbeats 200000
open Lax342547.QuadraticDegree

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

/--
---
conclusion: Lax342547.QuadraticDegree.quadratic_function_degree
---
-/
theorem quadratic_function_degree {b : ℕ} {I : Type} [Fintype I]
    (A : Matrix I I Binary) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b 1) :
    (fun x => ∑ i, ∑ j, A i j*z i x*z j x) ∈ selectorSpan b 2 := by
  classical
  have he : (fun x => ∑ i, ∑ j, A i j*z i x*z j x) = ∑ i, ∑ j, A i j • (z i*z j) := by
    ext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,mul_assoc]
  rw [he]
  exact (selectorSpan b 2).sum_mem (fun i _ => (selectorSpan b 2).sum_mem
    (fun j _ => (selectorSpan b 2).smul_mem _ (Lax342547Proofs.SelectorInterpolation.mul_mem (d := 1) (e := 1) (hz i) (hz j))))

/--
---
conclusion: Lax342547.QuadraticDegree.linear_outer_product_degree
---
-/
theorem linear_outer_product_degree {b : ℕ} {I : Type} [Fintype I]
    (φ : Module.Dual Binary (Matrix I I Binary)) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b 1) :
    (fun x => φ (Matrix.of (fun i j => z i x*z j x))) ∈ selectorSpan b 2 := by
  classical
  let A : Matrix I I Binary := fun i j => φ (Matrix.single i j 1)
  have he (x : Fin b → Binary) : φ (Matrix.of (fun i j => z i x*z j x)) =
      ∑ i, ∑ j, A i j*z i x*z j x := by
    rw [Matrix.matrix_eq_sum_single (Matrix.of (fun i j => z i x*z j x)),map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : Matrix.single i j (z i x*z j x) = (z i x*z j x) • Matrix.single i j (1 : Binary) := by
      ext u v
      simp [Matrix.single,smul_eq_mul]
    simp only [Matrix.of_apply]
    rw [hs,map_smul]
    simp only [smul_eq_mul,A]
    ring
  simp_rw [he]
  exact Lax342547.QuadraticDegree.quadratic_function_degree A z hz

/--
---
conclusion: Lax342547.QuadraticDegree.quadratic_error_exactification
---
-/
theorem quadratic_error_exactification {b : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b 2)
    (herr : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) < 1/4) : f = 0 := by
  apply Lax342547.BooleanWeight.uniform_error_exactification f hf
  simpa only [show (2 : ℝ)^2 = 4 from by norm_num] using herr

end Lax342547Proofs.QuadraticDegree
