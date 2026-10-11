import Lax342547.FourierTests
import Lax342547.TinyCompatibility

/-!
---
title: Tiny-cover four-bit parity bounds
type: lemma
---
Four even-support characters exactly recover the compatible-pair probability; twelve remaining characters contribute an explicit error, preserving inverse-polynomial mass.
-/

namespace Lax342547.FourPhaseParity

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.FourierTests
open Lax342547.RelativeEntropy Lax342547.CellAveraging
open scoped BigOperators

def duplicate (t : Fin 2 → Binary) : Fin 4 → Binary := ![t 0,t 0,t 1,t 1]
def parity (b : Fin 4 → Binary) : Fin 2 → Binary := ![b 0+b 1,b 2+b 3]
abbrev Even (t : Fin 4 → Binary) : Prop := t 0 = t 1 ∧ t 2 = t 3

axiom phase_duplicate (t : Fin 2 → Binary) (b : Fin 4 → Binary) :
    phase (duplicate t) b = phase t (parity b)

axiom duplicate_injective : Function.Injective duplicate

axiom even_iff_duplicate (t : Fin 4 → Binary) :
    Even t ↔ ∃ s, duplicate s = t

axiom even_character_sum {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Binary) :
    (∑ t ∈ Finset.univ.filter Even, characterMean ρ bits 0 t) =
      4*patternMass ρ (fun ω => parity (bits ω)) 0

axiom odd_character_card : (Finset.univ.filter (fun t : Fin 4 → Binary => ¬ Even t)).card = 12

axiom four_phase_parity_lower {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (bits : Ω → Fin 4 → Binary) (ε : ℝ)
    (hodd : ∀ t, ¬ Even t → |characterMean ρ bits 0 t| ≤ ε) :
    patternMass ρ (fun ω => parity (bits ω)) 0/4-3*ε/4 ≤ patternMass ρ bits 0

axiom tiny_four_phase_lower {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (bits : Ω × Ω → Fin 4 → Binary) (d N : ℕ) (ε : ℝ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N)
    (hparity : ∀ a b, parity (bits (a,b)) = ![F a b,F b a])
    (hodd : ∀ t, ¬ Even t → |characterMean (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 t| ≤ ε) :
    1/(16*(1+(d : ℝ)*N)^4)-3*ε/4 ≤
      patternMass (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0

axiom tiny_four_phase_positive {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (bits : Ω × Ω → Fin 4 → Binary) (d N : ℕ) (ε : ℝ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N)
    (hparity : ∀ a b, parity (bits (a,b)) = ![F a b,F b a])
    (hodd : ∀ t, ¬ Even t → |characterMean (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0 t| ≤ ε)
    (hε : ε ≤ 1/(24*(1+(d : ℝ)*N)^4)) :
    1/(32*(1+(d : ℝ)*N)^4) ≤
      patternMass (fun ab : Ω × Ω => μ ab.1*μ ab.2) bits 0

end Lax342547.FourPhaseParity
