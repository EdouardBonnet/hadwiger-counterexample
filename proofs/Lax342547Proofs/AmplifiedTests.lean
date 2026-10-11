import Lax342547.AmplifiedTests

namespace Lax342547Proofs.AmplifiedTests
open Lax342547.AmplifiedTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.AmplifiedTests.test_fubini
---
-/
theorem test_fubini {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (T : A → B → Prop) :
    (∑ b,β b*cellMass α (fun a => T a b)) =
      ∑ a,α a*cellMass β (T a) := by
  classical
  unfold cellMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : T a b <;> simp [h,mul_comm]

/--
---
conclusion: Lax342547.AmplifiedTests.amplified_bad_mass
---
-/
theorem amplified_bad_mass {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (T : A → B → Prop) (bad : B → Prop) (c U : ℝ)
    (hα : Probability α) (hβ : ∀ b,0 ≤ β b) (hc : 0 < c)
    (hlower : ∀ b,bad b → c ≤ cellMass α (fun a => T a b))
    (hupper : ∀ a,cellMass β (T a) ≤ U) : cellMass β bad ≤ U/c := by
  classical
  have hn (b : B) : 0 ≤ cellMass α (fun a => T a b) := by
    unfold cellMass
    apply Finset.sum_nonneg
    intro a _
    split_ifs <;> simp [hα.1 a]
  have hl : c*cellMass β bad ≤ ∑ b,β b*cellMass α (fun a => T a b) := by
    unfold cellMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    by_cases h : bad b
    · simp only [h,ite_true]
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left (hlower b h) (hβ b)
    · simp only [h,ite_false,mul_zero]
      exact mul_nonneg (hβ b) (hn b)
  rw [Lax342547.AmplifiedTests.test_fubini] at hl
  have hu : (∑ a,α a*cellMass β (T a)) ≤ U := by
    calc
      _ ≤ ∑ a,α a*U := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hupper a) (hα.1 a))
      _ = U := by rw [← Finset.sum_mul,hα.2,one_mul]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using hl.trans hu

end Lax342547Proofs.AmplifiedTests
