import Lax342547.UnitLaws
import Lax342547.EntropyProjection
import Lax342547.RelativeEntropy

namespace Lax342547Proofs.UnitLaws
open Lax342547.UnitLaws

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy
open scoped BigOperators

/--
---
conclusion: Lax342547.UnitLaws.feasible_closed
---
-/
theorem feasible_closed {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : IsClosed {ρ | Feasible μ R M κ ρ} := by
  have hprob : IsClosed {ρ : Ω × Ω → ℝ | Probability ρ} := isClosed_stdSimplex ℝ (Ω × Ω)
  have hleft : IsClosed {ρ : Ω × Ω → ℝ | ∀ x, (∑ y, ρ (x,y)) ≤ M*μ x} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_le (by fun_prop) continuous_const
  have hright : IsClosed {ρ : Ω × Ω → ℝ | ∀ y, (∑ x, ρ (x,y)) ≤ M*μ y} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    exact isClosed_le (by fun_prop) continuous_const
  have hpair : IsClosed {ρ : Ω × Ω → ℝ | ∀ xy, ρ xy ≤ κ*(μ xy.1*μ xy.2)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro xy
    exact isClosed_le (continuous_apply xy) continuous_const
  have hsupp : IsClosed {ρ : Ω × Ω → ℝ | ∀ xy, ¬ R xy.1 xy.2 → ρ xy = 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro xy
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_apply xy) continuous_const
  exact hprob.inter (hleft.inter (hright.inter (hpair.inter hsupp)))

/--
---
conclusion: Lax342547.UnitLaws.feasible_compact
---
-/
theorem feasible_compact {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : IsCompact {ρ | Feasible μ R M κ ρ} := by
  exact (Lax342547.RelativeEntropy.probability_compact (Ω := Ω × Ω)).of_isClosed_subset
    (Lax342547.UnitLaws.feasible_closed μ R M κ) (fun _ h => h.1)

/--
---
conclusion: Lax342547.UnitLaws.feasible_convex
---
-/
theorem feasible_convex {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : Convex ℝ {ρ | Feasible μ R M κ ρ} := by
  intro ρ hρ ρ' hρ' a b ha hb hab
  refine ⟨Lax342547.RelativeEntropy.probability_convex hρ.1 hρ'.1 ha hb hab,?_,?_,?_,?_⟩
  · intro x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left (hρ.2.1 x) ha
    have h₂ := mul_le_mul_of_nonneg_left (hρ'.2.1 x) hb
    calc
      _ ≤ a*(M*μ x)+b*(M*μ x) := add_le_add h₁ h₂
      _ = M*μ x := by rw [← add_mul,hab,one_mul]
  · intro y
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left (hρ.2.2.1 y) ha
    have h₂ := mul_le_mul_of_nonneg_left (hρ'.2.2.1 y) hb
    calc
      _ ≤ a*(M*μ y)+b*(M*μ y) := add_le_add h₁ h₂
      _ = M*μ y := by rw [← add_mul,hab,one_mul]
  · intro xy
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have h₁ := mul_le_mul_of_nonneg_left (hρ.2.2.2.1 xy) ha
    have h₂ := mul_le_mul_of_nonneg_left (hρ'.2.2.2.1 xy) hb
    calc
      _ ≤ a*(κ*(μ xy.1*μ xy.2))+b*(κ*(μ xy.1*μ xy.2)) := add_le_add h₁ h₂
      _ = κ*(μ xy.1*μ xy.2) := by rw [← add_mul,hab,one_mul]
  · intro xy hxy
    simp [hρ.2.2.2.2 xy hxy,hρ'.2.2.2.2 xy hxy]

/--
---
conclusion: Lax342547.UnitLaws.entropy_minimizer
---
-/
theorem entropy_minimizer {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ)
    (hne : ∃ ρ, Feasible μ R M κ ρ) :
    ∃ ρ, Feasible μ R M κ ρ ∧
      (∀ ρ', Feasible μ R M κ ρ' → entropy ρ (fun xy => μ xy.1*μ xy.2) ≤ entropy ρ' (fun xy => μ xy.1*μ xy.2)) ∧
      (∀ ρ', Feasible μ R M κ ρ' → ∀ xy, 0 < ρ' xy → 0 < ρ xy) ∧
      (∀ ρ', Feasible μ R M κ ρ' → entropy ρ' ρ ≤
        entropy ρ' (fun xy => μ xy.1*μ xy.2)-entropy ρ (fun xy => μ xy.1*μ xy.2)) := by
  exact Lax342547.EntropyProjection.entropy_projection
    {ρ | Feasible μ R M κ ρ} (fun xy => μ xy.1*μ xy.2)
    (Lax342547.UnitLaws.feasible_compact μ R M κ) hne (Lax342547.UnitLaws.feasible_convex μ R M κ) (fun _ h => h.1)

/--
---
conclusion: Lax342547.UnitLaws.feasible_entropy_budget
---
-/
theorem feasible_entropy_budget {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) (ρ : Ω × Ω → ℝ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x) (hκ : 0 < κ) (hρ : Feasible μ R M κ ρ) :
    0 ≤ entropy ρ (fun xy => μ xy.1*μ xy.2) ∧ entropy ρ (fun xy => μ xy.1*μ xy.2) ≤ Real.log κ := by
  have hq : Probability (fun xy : Ω × Ω => μ xy.1*μ xy.2) := by
    refine ⟨fun xy => mul_nonneg (hμ.1 xy.1) (hμ.1 xy.2),?_⟩
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,hμ.2,mul_one]
  exact ⟨Lax342547.RelativeEntropy.entropy_nonneg ρ _ hρ.1 hq (fun xy _ => mul_pos (hμpos xy.1) (hμpos xy.2)),
    Lax342547.RelativeEntropy.entropy_density_bound ρ _ κ hρ.1
      (fun xy => mul_pos (hμpos xy.1) (hμpos xy.2)) hκ hρ.2.2.2.1⟩

end Lax342547Proofs.UnitLaws
