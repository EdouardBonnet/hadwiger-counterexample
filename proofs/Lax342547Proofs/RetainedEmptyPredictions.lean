import Lax342547.RetainedEmptyPredictions
import Lax342547Proofs.EmptyPredictions
import Lax342547Proofs.MomentTails

namespace Lax342547Proofs.RetainedEmptyPredictions
open Lax342547.RetainedEmptyPredictions

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RelativeEntropy
open Lax342547.AtomParameters
open scoped BigOperators

/--
---
conclusion: Lax342547.RetainedEmptyPredictions.prediction_error_nonneg
---
-/
theorem prediction_error_nonneg {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (l : Tag k) (s : Fin b → Binary) :
    0 ≤ predictionError hr φ γ l s := by
  classical
  unfold predictionError cellMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> positivity

/--
---
conclusion: Lax342547.RetainedEmptyPredictions.prediction_error_le_total
---
-/
theorem prediction_error_le_total {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (E : Finset (Fin b → Binary))
    (l : Tag k) (s : Fin b → Binary) (hs : s ∉ E) :
    predictionError hr φ γ l s ≤ totalPredictionError hr φ γ E := by
  classical
  have hn (l : Tag k) (s : Fin b → Binary) : 0 ≤ if s ∈ E then (0 : ℝ) else predictionError hr φ γ l s := by
    split_ifs
    · exact le_rfl
    · exact prediction_error_nonneg hr φ γ l s
  have h₁ := Finset.single_le_sum (fun t (_ : t ∈ Finset.univ) => hn l t) (Finset.mem_univ s)
  have h₂ := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Finset.sum_nonneg (s := Finset.univ) (fun t _ => hn j t))
    (Finset.mem_univ l)
  simpa only [hs,ite_false,totalPredictionError] using h₁.trans h₂

/--
---
conclusion: Lax342547.RetainedEmptyPredictions.retained_vanishing_predictions
---
-/
theorem retained_vanishing_predictions {U : Type} [Fintype U] {k n b degree r : ℕ}
    (hr : 2*r ≤ n) (hr0 : 0 < r) (β : U → ℝ)
    (φ : U → Module.Dual Binary (Profile k n b degree)) (γ : U → Binary)
    (E : U → Finset (Fin b → Binary)) (ε : ℝ) (hβ : Probability β)
    (hE : ∀ u,2^(degree+degree)*(E u).card < 2^b)
    (herr : (∑ u,β u*totalPredictionError hr (φ u) (γ u) (E u)) ≤ ε) :
    1-4*ε ≤ cellMass β (fun u => γ u = 0 ∧ φ u = 0) := by
  classical
  let err := fun u => totalPredictionError hr (φ u) (γ u) (E u)
  have hn (u : U) : 0 ≤ err u := by
    unfold err totalPredictionError
    apply Finset.sum_nonneg
    intro l _
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact le_rfl
    · exact prediction_error_nonneg hr (φ u) (γ u) l s
  have hm := Lax342547Proofs.MomentTails.finite_moment_markov β err (1/4) 1 hβ.1 (by norm_num)
  simp only [abs_of_nonneg (hn _),pow_one] at hm
  have ht : cellMass β (fun u => 1/4 ≤ err u) ≤ 4*ε := by
    have hh := hm.trans (div_le_div_of_nonneg_right herr (by norm_num : (0 : ℝ) ≤ 1/4))
    have he : ε/(1/4) = 4*ε := by ring
    simpa only [he] using hh
  have hs : cellMass β (fun u => err u < 1/4)+cellMass β (fun u => 1/4 ≤ err u) = 1 := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ u,β u := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases he : err u < 1/4
        · simp only [if_pos he,if_neg (not_le.mpr he),add_zero]
        · simp only [if_neg he,if_pos (le_of_not_gt he),zero_add]
      _ = 1 := hβ.2
  have hgood : 1-4*ε ≤ cellMass β (fun u => err u < 1/4) := by linarith
  apply hgood.trans
  apply Lax342547Proofs.FiniteSampling.cell_mass_mono _ _ _ hβ.1
  intro u hu
  apply Lax342547Proofs.EmptyPredictions.vanishing_prediction_exact hr hr0 (φ u) (γ u) (E u) (hE u)
  intro l s hs
  exact (prediction_error_le_total hr (φ u) (γ u) (E u) l s hs).trans_lt hu

end Lax342547Proofs.RetainedEmptyPredictions
