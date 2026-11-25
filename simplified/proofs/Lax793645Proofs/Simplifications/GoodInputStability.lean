import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Tactic

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section

variable {X : Type} [Fintype X]

/-- Inserting a good-input event costs its raw rejection probability.
Acceptance weights remain unnormalized, so no acceptance or leaf mass occurs
in the denominator. -/
theorem good_input_bounded_test (w a f : Wgt X) (G : X → Prop) (C δ : ℝ)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1)
    (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (hG : pr w (fun x => ¬G x) ≤ δ) :
    |avg w (fun x => a x*f x)-avg w (fun x => a x*ind (G x)*f x)| ≤ C*δ := by
  rw [←avg_sub]
  refine (abs_avg_le hw).trans ?_
  have hp (x) : |a x*f x-a x*ind (G x)*f x| ≤ C*ind (¬G x) := by
    by_cases h : G x
    · simp [ind_one h,ind_zero (not_not.mpr h),hC]
    rw [ind_zero h,ind_one h,mul_zero,zero_mul,sub_zero,mul_one,abs_mul,
      abs_of_nonneg (ha x).1]
    exact (mul_le_mul_of_nonneg_left (hf x) (ha x).1).trans
      ((mul_le_mul_of_nonneg_right (ha x).2 hC).trans_eq (one_mul C))
  refine (avg_mono hw hp).trans ?_
  rw [avg_mul']
  exact mul_le_mul_of_nonneg_left hG hC

/-- A bounded structured comparison survives insertion of the same good-input
event on both sides, with the sum of the two sup-norm costs. -/
theorem good_input_comparison (w a f s : Wgt X) (G : X → Prop) (C D δ ε : ℝ)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ∀ x, |f x| ≤ C) (hs : ∀ x, |s x| ≤ D)
    (hG : pr w (fun x => ¬G x) ≤ δ)
    (hcomp : |avg w (fun x => a x*f x)-avg w (fun x => a x*s x)| ≤ ε) :
    |avg w (fun x => a x*ind (G x)*f x)-
      avg w (fun x => a x*ind (G x)*s x)| ≤ ε+(C+D)*δ := by
  have h1 := good_input_bounded_test w a f G C δ hw ha hC hf hG
  have h2 := good_input_bounded_test w a s G D δ hw ha hD hs hG
  have h := abs_sub_le (avg w (fun x => a x*ind (G x)*f x))
    (avg w (fun x => a x*f x)) (avg w (fun x => a x*ind (G x)*s x))
  have h' := abs_sub_le (avg w (fun x => a x*f x))
    (avg w (fun x => a x*s x)) (avg w (fun x => a x*ind (G x)*s x))
  rw [abs_sub_comm (avg w (fun x => a x*ind (G x)*f x))
    (avg w (fun x => a x*f x))] at h
  nlinarith

theorem clipped_difference (x y R : ℝ) (hxy : y ≤ x) :
    0 ≤ min x R-min y R ∧ min x R-min y R ≤ x-y := by
  constructor
  · exact sub_nonneg.mpr (min_le_min_right _ hxy)
  by_cases hx : x ≤ R
  · rw [min_eq_left hx,min_eq_left (hxy.trans hx)]
  by_cases hy : y ≤ R
  · rw [min_eq_right (le_of_not_ge hx),min_eq_left hy]; linarith
  rw [min_eq_right (le_of_not_ge hx),min_eq_right (le_of_not_ge hy),sub_self]
  linarith

/-- Truncated overlap is stable under deleting small unnormalized mass.
The factor R is essential; this statement makes no claim about unbounded
density products. -/
theorem good_input_truncated_overlap (w d e dg eg : Wgt X) (R δA δB : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hR : 0 ≤ R)
    (hA : ∀ x, 0 ≤ dg x ∧ dg x ≤ d x) (hB : ∀ x, 0 ≤ eg x ∧ eg x ≤ e x)
    (hδA : avg w (fun x => d x-dg x) ≤ δA)
    (hδB : avg w (fun x => e x-eg x) ≤ δB) :
    avg w (fun x => min (d x) R*min (e x) R)-R*(δA+δB) ≤
      avg w (fun x => min (dg x) R*min (eg x) R) := by
  have hp (x) : min (d x) R*min (e x) R-min (dg x) R*min (eg x) R ≤
      R*((d x-dg x)+(e x-eg x)) := by
    obtain ⟨ha,ha'⟩ := clipped_difference (d x) (dg x) R (hA x).2
    obtain ⟨hb,hb'⟩ := clipped_difference (e x) (eg x) R (hB x).2
    have hc := le_min (hA x).1 hR
    have hd := le_min (hB x).1 hR
    have hca := min_le_right (dg x) R
    have hcb := min_le_right (e x) R
    have h1 := mul_le_mul_of_nonneg_left ha' hR
    have h2 := mul_le_mul_of_nonneg_left hb' hR
    have h3 := mul_le_mul_of_nonneg_left hcb ha
    have h4 := mul_le_mul_of_nonneg_right hca hb
    nlinarith
  have h := avg_mono hw hp
  rw [avg_sub,avg_mul',avg_add] at h
  have he := mul_le_mul_of_nonneg_left (add_le_add hδA hδB) hR
  linarith

end
end Lax793645Proofs.Simplifications
