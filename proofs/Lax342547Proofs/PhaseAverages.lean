import Lax342547.PhaseAverages

namespace Lax342547Proofs.PhaseAverages
open Lax342547.PhaseAverages

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ChannelCharacters Lax342547.TensorCharacters
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.PhaseAverages.tensor_character_abs
---
-/
theorem tensor_character_abs {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    (h : ℕ) (A : e → Matrix I J Binary) (c : e × Fin h → (I → Binary) × (J → Binary)) :
    |tensorCharacter h A c| = 1 := by
  unfold tensorCharacter
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  unfold character phase sign
  split_ifs <;> norm_num

/--
---
conclusion: Lax342547.PhaseAverages.conditional_phase_abs_le_one
---
-/
theorem conditional_phase_abs_le_one {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ)
    (h : ℕ) (c : e × Fin h → (I → Binary) × (J → Binary))
    (hμ : Probability μ) (hψ : ∀ x, |ψ x| ≤ 1) :
    |∑ x, μ x*ψ x*tensorCharacter h (A x) c| ≤ 1 := by
  calc
    _ ≤ ∑ x, |μ x*ψ x*tensorCharacter h (A x) c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, μ x := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul,abs_mul,abs_of_nonneg (hμ.1 x),Lax342547.PhaseAverages.tensor_character_abs,mul_one]
      exact mul_le_of_le_one_right (hμ.1 x) (hψ x)
    _ = 1 := hμ.2

/--
---
conclusion: Lax342547.PhaseAverages.finite_event_density
---
-/
theorem finite_event_density {Ω : Type} [Fintype Ω] (α β : Ω → ℝ) (L : ℝ)
    (hcap : ∀ x, β x ≤ L*α x) (E : Ω → Prop) : cellMass β E ≤ L*cellMass α E := by
  classical
  unfold cellMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx,hcap x]

/--
---
conclusion: Lax342547.PhaseAverages.average_from_phase_tail
---
-/
theorem average_from_phase_tail {Ω : Type} [Fintype Ω] (β : Ω → ℝ) (f : Ω → ℝ)
    (θ : ℝ) (hβ : Probability β) (hf : ∀ x, |f x| ≤ 1) (hθ : 0 ≤ θ) :
    |∑ x, β x*f x| ≤ θ+cellMass β (fun x => θ ≤ |f x|) := by
  classical
  have hh : (∑ x, β x*|f x|) ≤ θ+cellMass β (fun x => θ ≤ |f x|) := by
    calc
      _ ≤ ∑ x, (β x*θ+if θ ≤ |f x| then β x else 0) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : θ ≤ |f x|
        · simp only [hx,ite_true]
          have ha := mul_le_of_le_one_right (hβ.1 x) (hf x)
          have hb := mul_nonneg (hβ.1 x) hθ
          linarith
        · simp only [hx,ite_false,add_zero]
          exact mul_le_mul_of_nonneg_left (le_of_not_ge hx) (hβ.1 x)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.sum_mul,hβ.2,one_mul]; rfl
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [abs_mul,abs_of_nonneg (hβ.1 _)] using hh

end Lax342547Proofs.PhaseAverages
