import Lax342547.EmpiricalVariance

namespace Lax342547Proofs.EmpiricalVariance

open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.EmpiricalVariance.empirical_variance
---
-/
theorem empirical_variance {Ω A : Type} [Fintype Ω] [Fintype A]
    (ρ : Ω → ℝ) (κ : A → ℝ) (F : Ω → A → ℝ) (good : A → A → Prop)
    (m ε δ : ℝ) (hρ : Probability ρ) (hκ : Probability κ)
    (hf : ∀ ω a,|F ω a| ≤ 1) (hm : |m| ≤ 1) (hε : 0 ≤ ε)
    (hmean : ∀ a b,good a b → (∑ ω,ρ ω*F ω a) = m ∧ (∑ ω,ρ ω*F ω b) = m)
    (hpair : ∀ a b,good a b → |(∑ ω,ρ ω*F ω a*F ω b)-m^2| ≤ ε)
    (hbad : cellMass (fun ab : A × A => κ ab.1*κ ab.2) (fun ab => ¬ good ab.1 ab.2) ≤ δ) :
    (∑ ω,ρ ω*((∑ a,κ a*F ω a)-m)^2) ≤ ε+4*δ := by
  classical
  have hcenter (ω : Ω) : (∑ a,κ a*F ω a)-m = ∑ a,κ a*(F ω a-m) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hκ.2,one_mul]
  have hfub : (∑ ω,ρ ω*((∑ a,κ a*F ω a)-m)^2) =
      ∑ a,∑ b,κ a*κ b*(∑ ω,ρ ω*(F ω a-m)*(F ω b-m)) := by
    simp_rw [hcenter,pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hcgood (a b : A) (hab : good a b) : ∑ ω,ρ ω*(F ω a-m)*(F ω b-m) ≤ ε := by
    have he : (∑ ω,ρ ω*(F ω a-m)*(F ω b-m)) = (∑ ω,ρ ω*F ω a*F ω b)-m^2 := by
      have hh : (∑ ω,ρ ω*(F ω a-m)*(F ω b-m)) =
          (∑ ω,ρ ω*F ω a*F ω b)-m*(∑ ω,ρ ω*F ω a)-m*(∑ ω,ρ ω*F ω b)+m^2*(∑ ω,ρ ω) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      rw [hh,(hmean a b hab).1,(hmean a b hab).2,hρ.2]
      ring
    rw [he]
    exact (le_abs_self _).trans (hpair a b hab)
  have hcany (a b : A) : ∑ ω,ρ ω*(F ω a-m)*(F ω b-m) ≤ 4 := by
    have hc (ω : Ω) (a : A) : |F ω a-m| ≤ 2 := (abs_sub _ _).trans (by linarith [hf ω a])
    have hh : (∑ ω,ρ ω*(F ω a-m)*(F ω b-m)) ≤ ∑ ω,ρ ω*4 := by
      apply Finset.sum_le_sum
      intro ω _
      have hmul : (F ω a-m)*(F ω b-m) ≤ 4 := by
        have hh := mul_le_mul (hc ω a) (hc ω b) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        rw [← abs_mul] at hh
        exact (le_abs_self _).trans (by norm_num at hh ⊢; exact hh)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul (hρ.1 ω)
    exact hh.trans_eq (by rw [← Finset.sum_mul,hρ.2,one_mul])
  have hb (a b : A) : (∑ ω,ρ ω*(F ω a-m)*(F ω b-m)) ≤ ε+(if good a b then 0 else 4) := by
    by_cases hab : good a b
    · simpa [hab] using hcgood a b hab
    · simp only [if_neg hab]; linarith [hcany a b]
  rw [hfub]
  calc
    _ ≤ ∑ a,∑ b,κ a*κ b*(ε+(if good a b then 0 else 4)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hb a b) (mul_nonneg (hκ.1 a) (hκ.1 b))
    _ = ε+4*cellMass (fun ab : A × A => κ ab.1*κ ab.2) (fun ab => ¬ good ab.1 ab.2) := by
      simp only [mul_add,Finset.sum_add_distrib,cellMass,Fintype.sum_prod_type]
      have he : (∑ a,∑ b,κ a*κ b*ε) = ε := by
        simp only [← Finset.mul_sum,← Finset.sum_mul,hκ.2,mul_one,one_mul]
      rw [he]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : good a b <;> simp [hab,mul_comm]
    _ ≤ _ := by linarith

end Lax342547Proofs.EmpiricalVariance
