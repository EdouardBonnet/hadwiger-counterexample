import Lax793645Proofs.Simplifications.QuadraticFrameCounts
import Lax793645Proofs.Simplifications.LinearFourier
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
noncomputable section

private theorem linear_test_discrepancy (h : ℕ) (d : Wgt (Hyperbolic h)) (δ : ℝ)
    (hcoeff : ∀ ℓ : Module.Dual F (Hyperbolic h),
      |avg unif (fun v => d v * wsign (ℓ v))| = δ)
    (r : ℕ) (L : Hyperbolic h →ₗ[F] Vec (Fin r)) (φ : Wgt (Vec (Fin r)))
    (hφ : ∀ x, |φ x| ≤ 1) :
    |avg unif (fun v => d v * φ (L v))| ≤ bp r * δ := by
  let coeff := linearFourier φ
  have expand v : d v * φ (L v) = ∑ ξ : Vec (Fin r),
      coeff ξ * (d v * wsign (((dotL ξ).comp L) v)) := by
    conv_lhs => rw [←hat_eqn φ (L v)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ξ _ => by dsimp [coeff,linearFourier,vectorPhase,dotL]; ring
  have bound ξ : |coeff ξ| ≤ 1 := by
    refine (abs_avg_le unif_law.nz).trans (unif_law.avg_le fun x => ?_)
    change |wsign (dotProduct ξ x) * φ x| ≤ 1
    simpa only [abs_mul,wsign_abs,one_mul] using hφ x
  simp_rw [expand,avg_sum,avg_mul']
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ _ξ : Vec (Fin r), δ := Finset.sum_le_sum fun ξ _ => by
      rw [abs_mul, hcoeff]
      have hδ : 0 ≤ δ := (abs_nonneg _).trans_eq (hcoeff 0)
      exact (mul_le_mul_of_nonneg_right (bound ξ) hδ).trans_eq (one_mul _)
    _ = bp r * δ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,dim_vec,Fintype.card_fin]

/-- Two disjoint, substantial key sets whose probabilities differ by only
two to the minus half-dimension against every linear character. A test of r
linear coordinates distinguishes their means by at most two to the power r-h. -/
theorem quadratic_cut_linear_tests (h : ℕ) (hh : 1 ≤ h) :
    ∃ f g : Wgt (Hyperbolic h),
      (∀ v, 0 ≤ f v ∧ f v ≤ 1 ∧ 0 ≤ g v ∧ g v ≤ 1) ∧
      1/4 ≤ avg unif f ∧ 1/4 ≤ avg unif g ∧ dip unif f g = 0 ∧
      (∀ ℓ : Module.Dual F (Hyperbolic h),
        |avg unif (fun v => (f v - g v) * wsign (ℓ v))| = bp (-(h:ℝ))) ∧
      ∀ (r : ℕ) (L : Hyperbolic h →ₗ[F] Vec (Fin r)) (φ : Wgt (Vec (Fin r))),
        (∀ x, |φ x| ≤ 1) →
        |avg unif (fun v => (f v - g v) * φ (L v))| ≤ bp r * bp (-(h:ℝ)) := by
  let q := hyperbolicQuadratic h
  let f v := (1 + wsign (q v))/2
  let g v := (1 - wsign (q v))/2
  have hp : 0 ≤ bp (-(h:ℝ)) := (bp_pos _).le
  have hcap : bp (-(h:ℝ)) ≤ 1/2 := calc
    _ ≤ bp (-1) := bp_le (neg_le_neg (by exact_mod_cast hh))
    _ = _ := by rw [bp_neg,bp_one]; norm_num
  refine ⟨f,g,?_,?_,?_,?_,?_⟩
  · intro v
    rcases bit_cases (q v) with hz|hz <;> norm_num [f,g,hz,wsign]
  · change 1/4 ≤ avg unif (fun v => (1+wsign (hyperbolicQuadratic h v))/2)
    rw [avg_div,avg_add,unif_law.avg_const,hyperbolic_gauss]
    linarith
  · change 1/4 ≤ avg unif (fun v => (1-wsign (hyperbolicQuadratic h v))/2)
    rw [avg_div,avg_sub,unif_law.avg_const,hyperbolic_gauss]
    linarith
  · have hzero v : f v * g v = 0 := by
      rcases bit_cases (q v) with hz|hz <;> norm_num [f,g,hz,wsign]
    simp only [dip,hzero,avg_zero]
  · have coeff (ℓ : Module.Dual F (Hyperbolic h)) :
        |avg unif (fun v => (f v - g v) * wsign (ℓ v))| = bp (-(h:ℝ)) := by
      let β : LinearMap.BilinForm F (Hyperbolic h) := q.polarBilin
      let t := (β.toDual (hyperbolic_nondegenerate h)).symm ℓ
      have eval (v) : ℓ v = q.polarBilin t v :=
        (LinearMap.BilinForm.apply_toDual_symm_apply (B:=β) (hB:=hyperbolic_nondegenerate h) ℓ v).symm
      simp_rw [eval]
      have hdiff v : (f v - g v) * wsign (q.polarBilin t v) =
          wsign (q v + q.polarBilin t v) := by
        rw [wsign_add]
        dsimp only [f,g]
        ring
      change |avg unif (fun v => (f v - g v) * wsign (q.polarBilin t v))| = _
      simp_rw [hdiff]
      dsimp only [q]
      rw [hyperbolic_fourier,abs_mul,wsign_abs,one_mul,abs_of_nonneg hp]
    exact ⟨coeff,linear_test_discrepancy h _ _ coeff⟩

end
end Lax793645Proofs.Simplifications

#print axioms Lax793645Proofs.Simplifications.quadratic_cut_linear_tests
