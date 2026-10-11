import Lax342547.ConditionedMixing
import Lax342547.FiniteSampling
import Lax342547.FourierTests

namespace Lax342547Proofs.ConditionedMixing

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.FourierTests
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.ConditionedMixing.signed_pattern_error
---
-/
theorem signed_pattern_error {Ω S : Type} [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (bits : Ω → S → Binary) (target : S → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hchar : ∀ t : S → Binary,t ≠ 0 → |characterMean w bits target t| ≤ ε) :
    |patternMass w bits target-(∑ ω,w ω)/(2 : ℝ)^Fintype.card S| ≤ ε := by
  classical
  let m := ∑ ω,w ω
  have ht (t : S → Binary) :
      |characterMean w bits target t-(if t = 0 then m else 0)| ≤ ε := by
    by_cases hz : t = 0
    · subst t
      simpa [m,Lax342547.FourierTests.character_zero] using hε
    · simpa only [if_neg hz,sub_zero] using hchar t hz
  have hs := (Finset.abs_sum_le_sum_abs (s := Finset.univ)
    (f := fun t => characterMean w bits target t-(if t = 0 then m else 0))).trans
    (Finset.sum_le_sum (fun t _ => ht t))
  have hc : (Fintype.card (S → Binary) : ℝ) = (2 : ℝ)^Fintype.card S := by simp [ZMod.card]
  simp only [Finset.sum_sub_distrib,Lax342547.FourierTests.pattern_inversion,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc] at hs
  have hp : 0 < (2 : ℝ)^Fintype.card S := by positivity
  have he : patternMass w bits target-(∑ ω,w ω)/(2 : ℝ)^Fintype.card S =
      ((2 : ℝ)^Fintype.card S*patternMass w bits target-m)/(2 : ℝ)^Fintype.card S := by
    dsimp [m]
    field_simp
  rw [he,abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hs)

/--
---
conclusion: Lax342547.ConditionedMixing.conditional_test_comparison
---
-/
theorem conditional_test_comparison {Ω S : Type} [Fintype Ω] [Fintype S] [DecidableEq S]
    (ρ f : Ω → ℝ) (bits : Ω → S → Binary) (target : S → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (htotal : ∑ ω,ρ ω = 1) (hmean : |∑ ω,ρ ω*f ω| ≤ 1)
    (hraw : ∀ t : S → Binary,t ≠ 0 → |characterMean ρ bits target t| ≤ ε)
    (htest : ∀ t : S → Binary,t ≠ 0 → |characterMean (fun ω => ρ ω*f ω) bits target t| ≤ ε)
    (hmass : 0 < patternMass ρ bits target) :
    |patternMass (fun ω => ρ ω*f ω) bits target/patternMass ρ bits target-
      (∑ ω,ρ ω*f ω)| ≤ 2*ε/patternMass ρ bits target := by
  let q := patternMass ρ bits target
  let m := ∑ ω,ρ ω*f ω
  let a := patternMass (fun ω => ρ ω*f ω) bits target
  let b := 1/(2 : ℝ)^Fintype.card S
  have h₁ : |a-m*b| ≤ ε := by
    simpa only [a,m,b,div_eq_mul_inv,one_div,one_mul] using Lax342547.ConditionedMixing.signed_pattern_error (fun ω => ρ ω*f ω) bits target ε hε htest
  have h₂ : |q-b| ≤ ε := by
    simpa only [htotal] using Lax342547.ConditionedMixing.signed_pattern_error ρ bits target ε hε hraw
  have he : a-m*q = (a-m*b)-m*(q-b) := by ring
  have hprod : |m*(q-b)| ≤ ε := by
    rw [abs_mul]
    have hm : |m| ≤ 1 := hmean
    nlinarith [abs_nonneg m,abs_nonneg (q-b)]
  have hn : |a-m*q| ≤ 2*ε := by
    rw [he]
    have hh := (abs_sub (a-m*b) (m*(q-b))).trans (add_le_add h₁ hprod)
    linarith
  have hq : 0 < q := hmass
  have hdiff : a/q-m = (a-m*q)/q := by field_simp
  change |a/q-m| ≤ 2*ε/q
  rw [hdiff,abs_div,abs_of_pos hq]
  exact div_le_div_of_nonneg_right hn hq.le

/--
---
conclusion: Lax342547.ConditionedMixing.bounded_integral_deletion
---
-/
theorem bounded_integral_deletion {Ω : Type} [Fintype Ω] (ρ f : Ω → ℝ)
    (C : Ω → Prop) (hρ : Lax342547.RelativeEntropy.Probability ρ)
    (hf : ∀ x,|f x| ≤ 1) (hC : 0 < Lax342547.RetainedImages.cellMass ρ C) : by
    classical
    exact |(∑ x,if C x then ρ x*f x else 0)/Lax342547.RetainedImages.cellMass ρ C-
        (∑ x,ρ x*f x)| ≤ 2*(1-Lax342547.RetainedImages.cellMass ρ C) := by
  classical
  let q := Lax342547.RetainedImages.cellMass ρ C
  let a := ∑ x,if C x then ρ x*f x else 0
  let b := ∑ x,ρ x*f x
  have hq : q ≤ 1 := by
    have hh := Lax342547.FiniteSampling.cell_mass_mono ρ C (fun _ => True) hρ.1 (by simp)
    simpa [Lax342547.RetainedImages.cellMass,hρ.2,q] using hh
  have hint (D : Ω → Prop) : |∑ x,if D x then ρ x*f x else 0| ≤
      Lax342547.RetainedImages.cellMass ρ D := by
    apply (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun x => if D x then ρ x*f x else 0)).trans
    unfold Lax342547.RetainedImages.cellMass
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : D x
    · simp only [if_pos hx,abs_mul,abs_of_nonneg (hρ.1 x)]
      exact (mul_le_mul_of_nonneg_left (hf x) (hρ.1 x)).trans_eq (mul_one _)
    · simp [hx]
  have ha : |a/q| ≤ 1 := by
    rw [abs_div,abs_of_pos hC]
    exact (div_le_one hC).mpr (hint C)
  have hc : b-a = ∑ x,if ¬ C x then ρ x*f x else 0 := by
    simp only [a,b,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : C x <;> simp [hx]
  have hqc : Lax342547.RetainedImages.cellMass ρ (fun x => ¬ C x) = 1-q := by
    have hs : q+Lax342547.RetainedImages.cellMass ρ (fun x => ¬ C x) = 1 := by
      unfold q Lax342547.RetainedImages.cellMass
      rw [← Finset.sum_add_distrib]
      convert hρ.2 using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : C x <;> simp [hx]
    linarith
  have hb : |b-a| ≤ 1-q := by
    rw [hc,← hqc]
    convert hint (fun x => ¬ C x) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : C x <;> simp [hx]
  have he : a/q-b = (1-q)*(a/q)-(b-a) := by
    have hq0 : q ≠ 0 := ne_of_gt hC
    field_simp [hq0]
    ring
  change |a/q-b| ≤ 2*(1-q)
  rw [he]
  calc
    _ ≤ |(1-q)*(a/q)|+|b-a| := abs_sub _ _
    _ = (1-q)*|a/q|+|b-a| := by rw [abs_mul,abs_of_nonneg (by linarith)]
    _ ≤ (1-q)*1+(1-q) := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith)) hb
    _ = _ := by ring

end Lax342547Proofs.ConditionedMixing
