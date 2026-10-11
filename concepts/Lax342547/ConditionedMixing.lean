import Lax342547.FourierTests
import Lax342547.RelativeEntropy

/-!
---
title: Exact finite conditioning of separated Fourier tests
type: definition and theorem
---
Fourier inversion controls signed test integrals and their normalization
separately. Division by the actual conditioning mass gives a quantitative
comparison, uniform over bounded tests.
-/

namespace Lax342547.ConditionedMixing

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.FourierTests
open scoped BigOperators

axiom signed_pattern_error {Ω S : Type} [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (bits : Ω → S → Binary) (target : S → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hchar : ∀ t : S → Binary,t ≠ 0 → |characterMean w bits target t| ≤ ε) :
    |patternMass w bits target-(∑ ω,w ω)/(2 : ℝ)^Fintype.card S| ≤ ε

axiom conditional_test_comparison {Ω S : Type} [Fintype Ω] [Fintype S] [DecidableEq S]
    (ρ f : Ω → ℝ) (bits : Ω → S → Binary) (target : S → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (htotal : ∑ ω,ρ ω = 1) (hmean : |∑ ω,ρ ω*f ω| ≤ 1)
    (hraw : ∀ t : S → Binary,t ≠ 0 → |characterMean ρ bits target t| ≤ ε)
    (htest : ∀ t : S → Binary,t ≠ 0 → |characterMean (fun ω => ρ ω*f ω) bits target t| ≤ ε)
    (hmass : 0 < patternMass ρ bits target) :
    |patternMass (fun ω => ρ ω*f ω) bits target/patternMass ρ bits target-
      (∑ ω,ρ ω*f ω)| ≤ 2*ε/patternMass ρ bits target

axiom bounded_integral_deletion {Ω : Type} [Fintype Ω] (ρ f : Ω → ℝ)
    (C : Ω → Prop) (hρ : Lax342547.RelativeEntropy.Probability ρ)
    (hf : ∀ x,|f x| ≤ 1) (hC : 0 < Lax342547.RetainedImages.cellMass ρ C) : by
    classical
    exact |(∑ x,if C x then ρ x*f x else 0)/Lax342547.RetainedImages.cellMass ρ C-
        (∑ x,ρ x*f x)| ≤ 2*(1-Lax342547.RetainedImages.cellMass ρ C)

end Lax342547.ConditionedMixing
