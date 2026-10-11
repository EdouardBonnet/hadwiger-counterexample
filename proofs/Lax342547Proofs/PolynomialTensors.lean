import Lax342547.PolynomialTensors
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.PolynomialTensors
open Lax342547.PolynomialTensors

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

/--
---
conclusion: Lax342547.PolynomialTensors.linear_outer_product_degree_bound
---
-/
theorem linear_outer_product_degree_bound {b d : ℕ} {I : Type} [Fintype I]
    (φ : Module.Dual Binary (Matrix I I Binary)) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b d) :
    (fun x => φ (Matrix.of (fun i j => z i x*z j x))) ∈ selectorSpan b (d+d) := by
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
  have he' : (fun x => ∑ i, ∑ j,A i j*z i x*z j x) = ∑ i,∑ j,A i j • (z i*z j) := by
    ext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,mul_assoc]
  rw [he']
  exact (selectorSpan b (d+d)).sum_mem (fun i _ => (selectorSpan b (d+d)).sum_mem
    (fun j _ => (selectorSpan b (d+d)).smul_mem _
      (Lax342547Proofs.SelectorInterpolation.mul_mem (d := d) (e := d) (hz i) (hz j))))

/--
---
conclusion: Lax342547.PolynomialTensors.selector_tensor_degree
---
-/
theorem selector_tensor_degree {b degree : ℕ} {Base : Type} [Fintype Base]
    (φ : Module.Dual Binary (Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)) (z : Base → Binary) :
    (fun s => φ (pointMoment selectorEval s z)) ∈ selectorSpan b (degree+degree) := by
  have hz (i : SelectorCoordinates b degree × Option Base) :
      (fun s => point selectorEval s z i) ∈ selectorSpan b degree := by
    have hs := Lax342547Proofs.SelectorInterpolation.monomial_mem i.1.val i.1.property
    have hm := (selectorSpan b degree).smul_mem (baseEval z i.2) hs
    convert hm using 1
    ext s
    simp only [Pi.smul_apply,smul_eq_mul,point,selectorEval,monomial]
    ring
  exact Lax342547.PolynomialTensors.linear_outer_product_degree_bound φ (fun i s => point selectorEval s z i) hz

end Lax342547Proofs.PolynomialTensors
