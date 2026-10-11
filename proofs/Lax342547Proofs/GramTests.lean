import Lax342547.GramTests
import Lax342547.FourierTests
import Lax342547.PushforwardWalsh

namespace Lax342547Proofs.GramTests
open Lax342547.GramTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.PushforwardWalsh
open Lax342547.FourierTests

/--
---
conclusion: Lax342547.GramTests.paper_walsh_factor
---
-/
theorem paper_walsh_factor (d : ℝ) :
    Real.sqrt ((2 : ℝ)^d * (2 : ℝ)^(-(95/100 : ℝ)*d) * (2 : ℝ)^(-(95/100 : ℝ)*d)) =
      (2 : ℝ)^(-(45/100 : ℝ)*d) := by
  have he : (2 : ℝ)^d * (2 : ℝ)^(-(95/100 : ℝ)*d) * (2 : ℝ)^(-(95/100 : ℝ)*d) =
      ((2 : ℝ)^(-(45/100 : ℝ)*d))^2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]

/--
---
conclusion: Lax342547.GramTests.paper_image_walsh
---
-/
theorem paper_image_walsh {ΩA ΩB I : Type} [Fintype ΩA] [Fintype ΩB]
    [Fintype I] [DecidableEq I]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (imageA : ΩA → I → Binary) (imageB : ΩB → I → Binary)
    (f : ΩA → ℝ) (g : ΩB → ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1)
    (hcapA : ∀ x, push α imageA x ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hcapB : ∀ y, push β imageB y ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hf : ∀ a, |f a| ≤ 1) (hg : ∀ b, |g b| ≤ 1) :
    |∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b)| ≤
      (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card I) := by
  have h := Lax342547.PushforwardWalsh.image_walsh_bound α β imageA imageB f g _ _
    hα hβ hαsum hβsum hcapA hcapB hf hg
  rw [← Real.rpow_natCast, Lax342547.GramTests.paper_walsh_factor] at h
  exact h

/--
---
conclusion: Lax342547.GramTests.zero_or_biased_agreement
---
-/
theorem zero_or_biased_agreement {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 →
      characterMean ρ bits target t = 1 ∨ |characterMean ρ bits target t| ≤ ε)
    (hsmall : ε ≤ 1 / (2 : ℝ) ^ (Fintype.card I + 1)) :
    1 / (2 : ℝ) ^ (Fintype.card I + 1) ≤ patternMass ρ bits target := by
  apply Lax342547.FourierTests.scalar_agreement_half ρ bits target ε hε hρ _ hsmall
  intro t ht
  rcases hchar t ht with he | hb
  · rw [he]
    linarith
  · exact (abs_le.mp hb).1

end Lax342547Proofs.GramTests
