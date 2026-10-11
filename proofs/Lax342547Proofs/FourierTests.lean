import Lax342547.FourierTests
import Lax342547Proofs.Walsh
import Lax342547.Walsh

namespace Lax342547Proofs.FourierTests
open Lax342547.FourierTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh

/--
---
conclusion: Lax342547.FourierTests.character_zero
---
-/
theorem character_zero {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) :
    characterMean ρ bits target 0 = ∑ ω, ρ ω := by
  simp [characterMean, phase, Lax342547Proofs.Walsh.sign_zero]

/--
---
conclusion: Lax342547.FourierTests.pattern_inversion
---
-/
theorem pattern_inversion {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) :
    (∑ t : I → Binary, characterMean ρ bits target t) =
      (2 : ℝ) ^ Fintype.card I * patternMass ρ bits target := by
  classical
  unfold characterMean
  rw [Finset.sum_comm]
  have hω (ω : Ω) : (∑ t : I → Binary, ρ ω * phase t (bits ω) * phase t target) =
      (2 : ℝ) ^ Fintype.card I * (if bits ω = target then ρ ω else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    have ho := Lax342547.Walsh.orthogonality (bits ω) target
    simp_rw [Lax342547Proofs.Walsh.phase_comm (bits ω), Lax342547Proofs.Walsh.phase_comm target] at ho
    rw [ho]
    split_ifs <;> ring
  simp only [hω]
  rw [← Finset.mul_sum]
  rfl

/--
---
conclusion: Lax342547.FourierTests.pattern_lower
---
-/
theorem pattern_lower {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t) :
    1 / (2 : ℝ) ^ Fintype.card I - ε ≤ patternMass ρ bits target := by
  classical
  have ht (t : I → Binary) : (if t = 0 then 1 else 0 : ℝ) - ε ≤ characterMean ρ bits target t := by
    by_cases h : t = 0
    · subst t
      rw [if_pos rfl, Lax342547.FourierTests.character_zero, hρ]
      linarith
    · simpa only [if_neg h, zero_sub] using hchar t h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  have hc : (Fintype.card (I → Binary) : ℝ) = (2 : ℝ) ^ Fintype.card I := by
    simp [ZMod.card]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, Lax342547.FourierTests.pattern_inversion] at hs
  have hpow : 0 < (2 : ℝ) ^ Fintype.card I := pow_pos (by norm_num) _
  have hh : (1 - (2 : ℝ) ^ Fintype.card I * ε) / (2 : ℝ) ^ Fintype.card I ≤
      patternMass ρ bits target := (div_le_iff₀ hpow).mpr (by simpa only [mul_comm] using hs)
  have he : (1 - (2 : ℝ) ^ Fintype.card I * ε) / (2 : ℝ) ^ Fintype.card I =
      1 / (2 : ℝ) ^ Fintype.card I - ε := by
    field_simp
  rw [he] at hh
  exact hh


/--
---
conclusion: Lax342547.FourierTests.pattern_lower_sharp
---
-/
theorem pattern_lower_sharp {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t) :
    (1 - ((2 : ℝ) ^ Fintype.card I - 1) * ε) / (2 : ℝ) ^ Fintype.card I ≤
      patternMass ρ bits target := by
  classical
  have ht (t : I → Binary) : (if t = 0 then 1 + ε else 0 : ℝ) - ε ≤ characterMean ρ bits target t := by
    by_cases h : t = 0
    · subst t
      rw [if_pos rfl, Lax342547.FourierTests.character_zero, hρ]
      linarith
    · simpa only [if_neg h, zero_sub] using hchar t h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  have hc : (Fintype.card (I → Binary) : ℝ) = (2 : ℝ) ^ Fintype.card I := by
    simp [ZMod.card]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, Lax342547.FourierTests.pattern_inversion] at hs
  have hpow : 0 < (2 : ℝ) ^ Fintype.card I := pow_pos (by norm_num) _
  apply (div_le_iff₀ hpow).mpr
  nlinarith

/--
---
conclusion: Lax342547.FourierTests.four_bit_pattern
---
-/
theorem four_bit_pattern {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Lax342547.MomentSpace.Binary)
    (target : Fin 4 → Lax342547.MomentSpace.Binary) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : Fin 4 → Lax342547.MomentSpace.Binary, t ≠ 0 →
      |characterMean ρ bits target t| ≤ 1 / 200) :
    (37 : ℝ) / 640 ≤ patternMass ρ bits target := by
  have h := Lax342547.FourierTests.pattern_lower_sharp ρ bits target (1 / 200) hρ (fun t ht => (abs_le.mp (hchar t ht)).1)
  norm_num at h
  exact h

/--
---
conclusion: Lax342547.FourierTests.scalar_agreement_half
---
-/
theorem scalar_agreement_half {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t)
    (hsmall : ε ≤ 1 / (2 : ℝ) ^ (Fintype.card I + 1)) :
    1 / (2 : ℝ) ^ (Fintype.card I + 1) ≤ patternMass ρ bits target := by
  have h := Lax342547.FourierTests.pattern_lower ρ bits target ε hε hρ hchar
  have hp : (2 : ℝ) ^ Fintype.card I ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
  have he : 1 / (2 : ℝ) ^ Fintype.card I = 2 * (1 / (2 : ℝ) ^ (Fintype.card I + 1)) := by
    rw [pow_succ]
    field_simp
  rw [he] at h
  linarith

end Lax342547Proofs.FourierTests
