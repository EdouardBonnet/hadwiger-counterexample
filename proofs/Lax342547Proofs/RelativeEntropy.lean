import Lax342547.RelativeEntropy
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.StdSimplex
import Lax342547Proofs.RetainedImages

namespace Lax342547Proofs.RelativeEntropy
open Lax342547.RelativeEntropy

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.RelativeEntropy.entropy_nonneg
---
-/
theorem entropy_nonneg {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ)
    (hρ : Probability ρ) (hq : Probability q) (hsupport : ∀ x, 0 < ρ x → 0 < q x) :
    0 ≤ entropy ρ q := by
  have ht (x : Ω) : ρ x - q x ≤ ρ x * Real.log (ρ x) - ρ x * Real.log (q x) := by
    by_cases hp : ρ x = 0
    · simp [hp, hq.1 x]
    · have hp0 : 0 < ρ x := lt_of_le_of_ne (hρ.1 x) (Ne.symm hp)
      have hq0 := hsupport x hp0
      have hlog := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
      rw [Real.log_div hq0.ne' hp0.ne'] at hlog
      have hm := mul_le_mul_of_nonneg_left hlog hp0.le
      have he : ρ x*(q x/ρ x) = q x := by field_simp
      nlinarith
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => ht x)
  simpa [entropy, Finset.sum_sub_distrib, hρ.2, hq.2] using h

/--
---
conclusion: Lax342547.RelativeEntropy.entropy_density_bound
---
-/
theorem entropy_density_bound {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) (cap : ℝ)
    (hρ : Probability ρ) (hq : ∀ x, 0 < q x) (_hcap : 0 < cap)
    (hbound : ∀ x, ρ x ≤ cap*q x) : entropy ρ q ≤ Real.log cap := by
  have ht (x : Ω) : ρ x * Real.log (ρ x) - ρ x * Real.log (q x) ≤ ρ x*Real.log cap := by
    by_cases hp : ρ x = 0
    · simp [hp]
    · have hp0 : 0 < ρ x := lt_of_le_of_ne (hρ.1 x) (Ne.symm hp)
      have hb : ρ x/q x ≤ cap := (div_le_iff₀ (hq x)).mpr (hbound x)
      have hlog := Real.log_le_log (div_pos hp0 (hq x)) hb
      rw [Real.log_div hp0.ne' (hq x).ne'] at hlog
      nlinarith [mul_le_mul_of_nonneg_left hlog hp0.le]
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => ht x)
  simpa [entropy, ← Finset.sum_mul, hρ.2] using h

/--
---
conclusion: Lax342547.RelativeEntropy.continuous_entropy
---
-/
theorem continuous_entropy {Ω : Type} [Fintype Ω] (q : Ω → ℝ) : Continuous (fun ρ : Ω → ℝ => entropy ρ q) := by
  unfold entropy
  apply continuous_finsetSum
  intro x _
  exact (Real.continuous_mul_log.comp (continuous_apply x)).sub ((continuous_apply x).mul continuous_const)

/--
---
conclusion: Lax342547.RelativeEntropy.compact_entropy_minimizer
---
-/
theorem compact_entropy_minimizer {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q : Ω → ℝ) (hP : IsCompact P) (hne : P.Nonempty) :
    ∃ ρ ∈ P, ∀ ρ' ∈ P, entropy ρ q ≤ entropy ρ' q := by
  obtain ⟨ρ,hρ,hmin⟩ := hP.exists_isMinOn hne (continuous_entropy q).continuousOn
  exact ⟨ρ,hρ,hmin⟩

/--
---
conclusion: Lax342547.RelativeEntropy.entropy_decomposition
---
-/
theorem entropy_decomposition {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (_hsupport : ∀ x, 0 < ρ' x → 0 < ρ x)
    (_hρ : ∀ x, 0 ≤ ρ x) (_hρ' : ∀ x, 0 ≤ ρ' x) :
    entropy ρ' q - entropy ρ q = entropy ρ' ρ +
      ∑ x, (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x)) := by
  unfold entropy
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/--
---
conclusion: Lax342547.RelativeEntropy.probability_compact
---
-/
theorem probability_compact {Ω : Type} [Fintype Ω] : IsCompact {ρ : Ω → ℝ | Probability ρ} := by
  exact isCompact_stdSimplex ℝ Ω

/--
---
conclusion: Lax342547.RelativeEntropy.probability_convex
---
-/
theorem probability_convex {Ω : Type} [Fintype Ω] : Convex ℝ {ρ : Ω → ℝ | Probability ρ} := by
  exact convex_stdSimplex ℝ Ω

/--
---
conclusion: Lax342547.RelativeEntropy.entropy_support_cost
---
-/
theorem entropy_support_cost {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) (S : Ω → Prop)
    (hρ : Probability ρ) (hq : Probability q)
    (hsupport : ∀ x, 0 < ρ x → 0 < q x) (hS : ∀ x, ¬ S x → ρ x = 0)
    (hmass : 0 < Lax342547.RetainedImages.cellMass q S) :
    -Real.log (Lax342547.RetainedImages.cellMass q S) ≤ entropy ρ q := by
  classical
  let m := Lax342547.RetainedImages.cellMass q S
  let qS := Lax342547.RetainedImages.conditionalLaw q S
  have hqS : Probability qS := ⟨Lax342547Proofs.RetainedImages.conditional_law_nonneg q S hq.1,
    Lax342547Proofs.RetainedImages.conditional_law_total q S hmass⟩
  have hρS (x : Ω) (hp : 0 < ρ x) : S x := by by_contra hn; rw [hS x hn] at hp; linarith
  have hqSsupport (x : Ω) (hp : 0 < ρ x) : 0 < qS x := by
    dsimp [qS, Lax342547.RetainedImages.conditionalLaw]
    rw [if_pos (hρS x hp)]
    exact div_pos (hsupport x hp) hmass
  have hn := entropy_nonneg ρ qS hρ hqS hqSsupport
  have he : entropy ρ qS = entropy ρ q + Real.log m := by
    unfold entropy
    have hx (x : Ω) : ρ x*Real.log (ρ x)-ρ x*Real.log (qS x) =
        (ρ x*Real.log (ρ x)-ρ x*Real.log (q x))+ρ x*Real.log m := by
      by_cases hp : ρ x = 0
      · simp [hp]
      · have hp0 : 0 < ρ x := lt_of_le_of_ne (hρ.1 x) (Ne.symm hp)
        dsimp [qS, Lax342547.RetainedImages.conditionalLaw]
        rw [if_pos (hρS x hp0), Real.log_div (hsupport x hp0).ne' hmass.ne']
        ring
    simp_rw [hx]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hρ.2, one_mul]
  rw [he] at hn
  linarith

end Lax342547Proofs.RelativeEntropy
