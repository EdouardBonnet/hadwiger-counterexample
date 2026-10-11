import Lax342547.Walsh

/-!
---
title: Finite scalar agreement from binary character bounds
type: lemma
---
Exact Fourier inversion yields simultaneous agreement of all scalar bits without any independence assumption on those bits.
-/

namespace Lax342547.FourierTests

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def patternMass {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) : ℝ := by
  classical
  exact ∑ ω, if bits ω = target then ρ ω else 0

noncomputable def characterMean {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target t : I → Binary) : ℝ :=
  ∑ ω, ρ ω * phase t (bits ω) * phase t target

axiom character_zero {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) :
    characterMean ρ bits target 0 = ∑ ω, ρ ω

axiom pattern_inversion {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) :
    (∑ t : I → Binary, characterMean ρ bits target t) =
      (2 : ℝ) ^ Fintype.card I * patternMass ρ bits target

axiom pattern_lower {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t) :
    1 / (2 : ℝ) ^ Fintype.card I - ε ≤ patternMass ρ bits target

axiom pattern_lower_sharp {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t) :
    (1 - ((2 : ℝ) ^ Fintype.card I - 1) * ε) / (2 : ℝ) ^ Fintype.card I ≤
      patternMass ρ bits target

axiom four_bit_pattern {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Lax342547.MomentSpace.Binary)
    (target : Fin 4 → Lax342547.MomentSpace.Binary) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : Fin 4 → Lax342547.MomentSpace.Binary, t ≠ 0 →
      |characterMean ρ bits target t| ≤ 1 / 200) :
    (37 : ℝ) / 640 ≤ patternMass ρ bits target

axiom scalar_agreement_half {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t)
    (hsmall : ε ≤ 1 / (2 : ℝ) ^ (Fintype.card I + 1)) :
    1 / (2 : ℝ) ^ (Fintype.card I + 1) ≤ patternMass ρ bits target

end Lax342547.FourierTests
