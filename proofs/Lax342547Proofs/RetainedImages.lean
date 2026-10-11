import Lax342547.RetainedImages
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Lax342547Proofs.RetainedImages
open Lax342547.RetainedImages

set_option backward.isDefEq.respectTransparency false
open Lax342547.PushforwardWalsh

/--
---
conclusion: Lax342547.RetainedImages.conditional_law_nonneg
---
-/
theorem conditional_law_nonneg {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (ω : Ω) : 0 ≤ conditionalLaw ρ C ω := by
  classical
  have hm : 0 ≤ cellMass ρ C := Finset.sum_nonneg (fun ω _ => by split_ifs; exact hρ ω; exact le_rfl)
  unfold conditionalLaw
  split_ifs
  · exact div_nonneg (hρ ω) hm
  · simp

/--
---
conclusion: Lax342547.RetainedImages.conditional_law_total
---
-/
theorem conditional_law_total {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop)
    (hC : 0 < cellMass ρ C) : ∑ ω, conditionalLaw ρ C ω = 1 := by
  classical
  unfold conditionalLaw
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hC)

/--
---
conclusion: Lax342547.RetainedImages.conditional_image_cap
---
-/
theorem conditional_image_cap {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ cap : ℝ) (hρ : ∀ ω, 0 ≤ ρ ω) (hτ : 0 < τ)
    (hC : τ ≤ cellMass ρ C) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, cellMass ρ (fun ω => joint ω ∧ image ω = x) ≤ cap) (x : X) :
    push (conditionalLaw ρ C) image x ≤ cap / τ := by
  classical
  have hm : 0 < cellMass ρ C := lt_of_lt_of_le hτ hC
  have he : push (conditionalLaw ρ C) image x =
      cellMass ρ (fun ω => C ω ∧ image ω = x) / cellMass ρ C := by
    unfold push conditionalLaw cellMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hcx : C ω <;> by_cases hix : image ω = x <;> simp [hcx, hix]
  have hnum : cellMass ρ (fun ω => C ω ∧ image ω = x) ≤
      cellMass ρ (fun ω => joint ω ∧ image ω = x) := by
    unfold cellMass
    apply Finset.sum_le_sum
    intro ω _
    by_cases hc : C ω ∧ image ω = x
    · have hj : joint ω ∧ image ω = x := ⟨hCJ ω hc.1, hc.2⟩
      rw [if_pos hc, if_pos hj]
    · rw [if_neg hc]
      split_ifs
      · exact hρ ω
      · exact le_rfl
  have hcap0 : 0 ≤ cap := le_trans (Finset.sum_nonneg (fun ω _ => by
    split_ifs; exact hρ ω; exact le_rfl)) (hcap x)
  rw [he]
  exact (div_le_div_of_nonneg_right (hnum.trans (hcap x)) hm.le).trans
    (div_le_div_of_nonneg_left hcap0 hτ hC)

/--
---
conclusion: Lax342547.RetainedImages.paper_cell_exponent
---
-/
theorem paper_cell_exponent (ζ k t : ℝ) (_hζ : 0 ≤ ζ)
    (hζsmall : ζ ≤ 1 / 1000) (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) :
    -(1 - 2 * ζ) * (k + t) + (k + 1 / 100) ≤ -(95 / 100 : ℝ) * t := by
  have hζt : 2 * ζ * t ≤ t / 500 := by nlinarith
  nlinarith

/--
---
conclusion: Lax342547.RetainedImages.paper_conditional_cap
---
-/
theorem paper_conditional_cap (ζ k t N : ℝ) (hζ : 0 ≤ ζ)
    (hζsmall : ζ ≤ 1 / 1000) (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) (hN : 0 ≤ N) :
    (2 : ℝ) ^ (-(1 - 2 * ζ) * (k + t) * N) /
        (2 : ℝ) ^ (-(k + 1 / 100) * N) ≤ (2 : ℝ) ^ (-(95 / 100 : ℝ) * t * N) := by
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have h := mul_le_mul_of_nonneg_right (Lax342547.RetainedImages.paper_cell_exponent ζ k t hζ hζsmall hk ht) hN
  linarith

end Lax342547Proofs.RetainedImages
