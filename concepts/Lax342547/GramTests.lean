import Lax342547.RetainedImages
import Lax342547.FourierTests

/-!
---
title: Scalar agreement after quotient character estimates
type: definition and theorem
---
The .95 image exponent gives the .45 Walsh exponent. Exact zero quotient characters and bounded nonzero characters give simultaneous scalar agreement with the full binary Fourier cost.
-/

namespace Lax342547.GramTests

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.PushforwardWalsh
open Lax342547.FourierTests

axiom paper_walsh_factor (d : ℝ) :
    Real.sqrt ((2 : ℝ)^d * (2 : ℝ)^(-(95/100 : ℝ)*d) * (2 : ℝ)^(-(95/100 : ℝ)*d)) =
      (2 : ℝ)^(-(45/100 : ℝ)*d)

axiom paper_image_walsh {ΩA ΩB I : Type} [Fintype ΩA] [Fintype ΩB]
    [Fintype I] [DecidableEq I]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (imageA : ΩA → I → Binary) (imageB : ΩB → I → Binary)
    (f : ΩA → ℝ) (g : ΩB → ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1)
    (hcapA : ∀ x, push α imageA x ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hcapB : ∀ y, push β imageB y ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hf : ∀ a, |f a| ≤ 1) (hg : ∀ b, |g b| ≤ 1) :
    |∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b)| ≤
      (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card I)

axiom zero_or_biased_agreement {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 →
      characterMean ρ bits target t = 1 ∨ |characterMean ρ bits target t| ≤ ε)
    (hsmall : ε ≤ 1 / (2 : ℝ) ^ (Fintype.card I + 1)) :
    1 / (2 : ℝ) ^ (Fintype.card I + 1) ≤ patternMass ρ bits target

end Lax342547.GramTests
