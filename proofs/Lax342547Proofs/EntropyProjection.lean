import Lax342547.EntropyProjection
import Lax342547.EntropyLines
import Lax342547.RelativeEntropy

namespace Lax342547Proofs.EntropyProjection
open Lax342547.EntropyProjection

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.EntropyLines
open scoped Topology BigOperators
open Filter

/--
---
conclusion: Lax342547.EntropyProjection.minimizer_full_support
---
-/
theorem minimizer_full_support {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) :
    ∀ ρ' ∈ P, ∀ x, 0 < ρ' x → 0 < ρ x := by
  classical
  intro ρ' hρ' x hx
  by_contra hn
  have hz : ρ x = 0 := le_antisymm (not_lt.mp hn) ((hprob ρ hρ).1 x)
  have hnew : 0 < newMass ρ ρ' := by
    unfold newMass
    apply Finset.sum_pos'
    · intro y _
      split_ifs <;> first | exact (hprob ρ' hρ').1 y | exact le_rfl
    · refine ⟨x, Finset.mem_univ x, ?_⟩
      rw [if_pos hz]
      exact hx
  have htend := Lax342547.EntropyLines.entropy_new_support_slope
    ρ ρ' q (hprob ρ' hρ').1 hnew
  have he := htend.eventually (eventually_lt_atBot (0:ℝ))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,hneg,ht1,ht0⟩ := (he.and (hsmall.and self_mem_nhdsWithin)).exists
  have ht : 0 < t := ht0
  have hp : mix ρ ρ' t ∈ P := by
    exact hconv hρ hρ' (by linarith : 0 ≤ 1-t) ht.le (by ring)
  have hnonneg : 0 ≤ (entropy (mix ρ ρ' t) q-entropy ρ q)/t :=
    div_nonneg (sub_nonneg.mpr (hmin _ hp)) ht.le
  linarith

/--
---
conclusion: Lax342547.EntropyProjection.minimizer_variational
---
-/
theorem minimizer_variational {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P) :
    0 ≤ ∑ x, (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x)) := by
  classical
  have hs := Lax342547.EntropyProjection.minimizer_full_support P q ρ hprob hconv hρ hmin ρ' hρ'
  have hz (x : Ω) (hx : ρ x = 0) : ρ' x = 0 := by
    by_contra hn
    have hp : 0 < ρ' x := lt_of_le_of_ne ((hprob ρ' hρ').1 x) (Ne.symm hn)
    have hh := hs x hp
    rw [hx] at hh
    linarith
  have hid (t : ℝ) : oldEntropy ρ ρ' q t = entropy (mix ρ ρ' t) q := by
    unfold oldEntropy entropy
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ρ x = 0
    · simp [hx, hz x hx, mix]
    · simp [hx, coordinate]
  have hd := (Lax342547.EntropyLines.old_entropy_derivative ρ ρ' q).tendsto_slope_zero_right
  have hd' : Tendsto (fun t => (oldEntropy ρ ρ' q t-oldEntropy ρ ρ' q 0)/t)
      (𝓝[>] 0) (𝓝 (oldDerivative ρ ρ' q)) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 ≤ (oldEntropy ρ ρ' q t-oldEntropy ρ ρ' q 0)/t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht0 ht1
    have ht : 0 < t := ht0
    have hp : mix ρ ρ' t ∈ P :=
      hconv hρ hρ' (by linarith : 0 ≤ 1-t) ht.le (by ring)
    rw [hid, Lax342547.EntropyLines.old_entropy_zero]
    exact div_nonneg (sub_nonneg.mpr (hmin _ hp)) ht.le
  have hder : 0 ≤ oldDerivative ρ ρ' q := ge_of_tendsto hd' hnonneg
  have he : oldDerivative ρ ρ' q = ∑ x, (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x)) := by
    unfold oldDerivative
    have hi (x : Ω) : (if ρ x = 0 then 0 else (ρ' x-ρ x)*(Real.log (ρ x)+1-Real.log (q x))) =
        (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x))+(ρ' x-ρ x) := by
      by_cases hx : ρ x = 0
      · simp [hx, hz x hx]
      · simp only [hx, if_false]; ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, (hprob ρ' hρ').2, (hprob ρ hρ).2]
    ring
  rwa [he] at hder

/--
---
conclusion: Lax342547.EntropyProjection.projection_inequality
---
-/
theorem projection_inequality {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P) :
    entropy ρ' ρ ≤ entropy ρ' q-entropy ρ q := by
  have hs := Lax342547.EntropyProjection.minimizer_full_support P q ρ hprob hconv hρ hmin ρ' hρ'
  have hv := Lax342547.EntropyProjection.minimizer_variational P q ρ hprob hconv hρ hmin ρ' hρ'
  rw [Lax342547.RelativeEntropy.entropy_decomposition ρ ρ' q hs (hprob ρ hρ).1 (hprob ρ' hρ').1]
  linarith

/--
---
conclusion: Lax342547.EntropyProjection.projection_support_cost
---
-/
theorem projection_support_cost {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P)
    (S : Ω → Prop) (hS : ∀ x, ¬ S x → ρ' x = 0)
    (hmass : 0 < Lax342547.RetainedImages.cellMass ρ S) :
    -Real.log (Lax342547.RetainedImages.cellMass ρ S) ≤ entropy ρ' q-entropy ρ q := by
  have hs := Lax342547.EntropyProjection.minimizer_full_support P q ρ hprob hconv hρ hmin ρ' hρ'
  exact (Lax342547.RelativeEntropy.entropy_support_cost ρ' ρ S
    (hprob ρ' hρ') (hprob ρ hρ) hs hS hmass).trans
    (Lax342547.EntropyProjection.projection_inequality P q ρ hprob hconv hρ hmin ρ' hρ')

/--
---
conclusion: Lax342547.EntropyProjection.entropy_projection
---
-/
theorem entropy_projection {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q : Ω → ℝ) (hcompact : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (hprob : ∀ p ∈ P, Probability p) :
    ∃ ρ ∈ P, (∀ ρ' ∈ P, entropy ρ q ≤ entropy ρ' q) ∧
      (∀ ρ' ∈ P, ∀ x, 0 < ρ' x → 0 < ρ x) ∧
      (∀ ρ' ∈ P, entropy ρ' ρ ≤ entropy ρ' q-entropy ρ q) := by
  obtain ⟨ρ,hρ,hmin⟩ := Lax342547.RelativeEntropy.compact_entropy_minimizer P q hcompact hne
  exact ⟨ρ,hρ,hmin,Lax342547.EntropyProjection.minimizer_full_support P q ρ hprob hconv hρ hmin,
    fun ρ' hρ' => Lax342547.EntropyProjection.projection_inequality P q ρ hprob hconv hρ hmin ρ' hρ'⟩

end Lax342547Proofs.EntropyProjection
