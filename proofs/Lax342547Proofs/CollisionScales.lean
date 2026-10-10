import Lax342547.CollisionScales
import Lax342547Proofs.CollisionCosts

namespace Lax342547Proofs.CollisionScales
open Lax342547.CollisionScales

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CollisionScales.record_scale
---
-/
theorem record_scale (C M₀ n : ℝ) (hn : 1 ≤ n) (hM : 200*(C+1) ≤ M₀) :
    1+C*n ≤ M₀*n/200 := by
  have hp := mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ n)
  nlinarith

/--
---
conclusion: Lax342547.CollisionScales.scalar_scale
---
-/
theorem scalar_scale (c M₀ n : ℝ) (hn : 0 ≤ n) (hM : 100*c ≤ M₀)
    (s : ℕ) (hs : (s:ℝ) ≤ c*n) : (s:ℝ) ≤ M₀*n/100 := by
  have hp := mul_le_mul_of_nonneg_right hM hn
  nlinarith

/--
---
conclusion: Lax342547.CollisionScales.eventual_pruning_gap
---
-/
theorem eventual_pruning_gap (η : ℝ) (hη : η < 1/200) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → 100 ≤ N ∧ 1 ≤ (1/200-η)*N := by
  refine ⟨max 100 (1/(1/200-η)), ?_⟩
  intro N hN
  have hg : 0 < (1/200:ℝ)-η := by linarith
  constructor
  · exact le_trans (le_max_left _ _) hN
  · have h := le_trans (le_max_right _ _) hN
    exact (div_le_iff₀ hg).mp h |>.trans_eq (mul_comm N _)

/--
---
conclusion: Lax342547.CollisionScales.bounded_options
---
-/
theorem bounded_options {O : Type} [Fintype O] [Nonempty O]
    (f : O → ℝ) (overlap : ℝ) (h : overlap ≤ ∑ o, f o) :
    ∃ o, overlap / Fintype.card O ≤ f o := by
  classical
  by_contra hn
  have hf : ∀ o, f o < overlap/Fintype.card O := by simpa using hn
  have hs := Finset.sum_lt_sum (fun o _ => (hf o).le)
    (by obtain ⟨o⟩ := ‹Nonempty O›; exact ⟨o, Finset.mem_univ o, hf o⟩)
  have hc : (Fintype.card O : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have he : (Fintype.card O : ℝ)*(overlap/Fintype.card O) = overlap := by field_simp
  rw [he] at hs
  linarith

/--
---
conclusion: Lax342547.CollisionScales.bounded_option_exponent
---
-/
theorem bounded_option_exponent (cost δ N options probability : ℝ)
    (hoptions : 0 < options) (hcount : options ≤ (2:ℝ)^(δ*N))
    (hprobability : (2:ℝ)^(-cost*N)/options ≤ probability) :
    (2:ℝ)^(-(cost+δ)*N) ≤ probability := by
  calc
    (2:ℝ)^(-(cost+δ)*N) = (2:ℝ)^(-cost*N)/(2:ℝ)^(δ*N) := by
      rw [← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    _ ≤ (2:ℝ)^(-cost*N)/options :=
      div_le_div_of_nonneg_left (by positivity) hoptions hcount
    _ ≤ probability := hprobability

end Lax342547Proofs.CollisionScales
