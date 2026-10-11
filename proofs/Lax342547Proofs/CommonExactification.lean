import Lax342547.CommonExactification
import Lax342547.BooleanWeight
import Lax342547.FiniteSampling
import Lax342547.MomentTails

namespace Lax342547Proofs.CommonExactification
open Lax342547.CommonExactification

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators

/--
---
conclusion: Lax342547.CommonExactification.discrepancy_mass_union
---
-/
theorem discrepancy_mass_union {X : Type} [Fintype X]
    (α : X → ℝ) (f p q : X → Binary) (hα : ∀ x, 0 ≤ α x) :
    cellMass α (fun x => p x ≠ q x) ≤
      cellMass α (fun x => p x ≠ f x)+cellMass α (fun x => q x ≠ f x) := by
  classical
  unfold cellMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all

/--
---
conclusion: Lax342547.CommonExactification.common_prediction_exact
---
-/
theorem common_prediction_exact {b d : ℕ}
    (f p q : (Fin b → Binary) → Binary)
    (hp : p ∈ selectorSpan b d) (hq : q ∈ selectorSpan b d)
    (herr : cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) (fun x => p x ≠ f x)+
      cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) (fun x => q x ≠ f x) < 1/(2 : ℝ)^d) : p = q := by
  have hsmall := (Lax342547.CommonExactification.discrepancy_mass_union (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) f p q (fun _ => by positivity)).trans_lt herr
  have he : (fun x => p x-q x) = 0 :=
    Lax342547.BooleanWeight.uniform_error_exactification (fun x => p x-q x)
      ((selectorSpan b d).sub_mem hp hq) (by simpa only [sub_ne_zero] using hsmall)
  exact sub_eq_zero.mp he

/--
---
conclusion: Lax342547.CommonExactification.prediction_good_mass
---
-/
theorem prediction_good_mass {U X : Type} [Fintype U] [Fintype X]
    (β : U → ℝ) (α : X → ℝ) (f : X → Binary) (p : U → X → Binary) (ε a : ℝ)
    (hβ : Probability β) (hα : ∀ x, 0 ≤ α x) (ha : 0 < a)
    (herror : (∑ u, β u*cellMass α (fun x => p u x ≠ f x)) ≤ ε) :
    1-ε/a ≤ cellMass β (fun u => cellMass α (fun x => p u x ≠ f x) < a) := by
  classical
  let err := fun u => cellMass α (fun x => p u x ≠ f x)
  have hn (u : U) : 0 ≤ err u := by
    unfold err cellMass
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> simp [hα x]
  have hm := Lax342547.MomentTails.finite_moment_markov β err a 1 hβ.1 ha
  simp only [abs_of_nonneg (hn _),pow_one] at hm
  have hb : cellMass β (fun u => a ≤ err u) ≤ ε/a := hm.trans (div_le_div_of_nonneg_right herror ha.le)
  have hs : cellMass β (fun u => err u < a)+cellMass β (fun u => a ≤ err u) = 1 := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ u, β u := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases h : err u < a
        · simp [h,not_le.mpr h]
        · simp [h,le_of_not_gt h]
      _ = 1 := hβ.2
  change 1-ε/a ≤ cellMass β (fun u => err u < a)
  linarith

/--
---
conclusion: Lax342547.CommonExactification.retained_common_prediction
---
-/
theorem retained_common_prediction {U : Type} [Fintype U] {b d : ℕ}
    (β : U → ℝ) (f : (Fin b → Binary) → Binary)
    (p : U → (Fin b → Binary) → Binary) (ε a : ℝ)
    (hβ : Probability β) (hp : ∀ u, p u ∈ selectorSpan b d)
    (ha : 0 < a) (hε : ε < a) (hdegree : 2*a ≤ 1/(2 : ℝ)^d)
    (herror : (∑ u, β u*cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => p u x ≠ f x)) ≤ ε) :
    ∃ u₀ : U, 1-ε/a ≤ cellMass β (fun u => p u = p u₀) := by
  classical
  let err := fun u => cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) (fun x => p u x ≠ f x)
  have hm := Lax342547.CommonExactification.prediction_good_mass β (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) f p ε a hβ
    (fun _ => by positivity) ha herror
  have hpos : 0 < 1-ε/a := by
    have ht := (div_lt_one ha).mpr hε
    linarith
  have hex : ∃ u : U, err u < a := by
    by_contra hn
    push Not at hn
    have hz : cellMass β (fun u => err u < a) = 0 := by
      unfold cellMass
      apply Finset.sum_eq_zero
      intro u _
      exact if_neg (not_lt.mpr (hn u))
    change 1-ε/a ≤ cellMass β (fun u => err u < a) at hm
    rw [hz] at hm
    linarith
  obtain ⟨u₀,hu₀⟩ := hex
  refine ⟨u₀,hm.trans ?_⟩
  apply Lax342547.FiniteSampling.cell_mass_mono _ _ _ hβ.1
  intro u hu
  apply Lax342547.CommonExactification.common_prediction_exact f (p u) (p u₀) (hp u) (hp u₀)
  exact (add_lt_add hu hu₀).trans_le (by simpa only [two_mul] using hdegree)

end Lax342547Proofs.CommonExactification
