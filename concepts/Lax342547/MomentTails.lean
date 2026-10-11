import Lax342547.FiniteMoments

/-!
---
title: Finite moment probability and rank split
type: definition and theorem
---
Finite Markov bounds and the low-rank/high-rank decomposition preserve the actual sample masses and explicit channel rank exponent.
-/

namespace Lax342547.MomentTails

open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

axiom finite_moment_markov {C : Type} [Fintype C] (ν : C → ℝ) (f : C → ℝ)
    (a : ℝ) (n : ℕ) (hν : ∀ c, 0 ≤ ν c) (ha : 0 < a) :
    cellMass ν (fun c => a ≤ |f c|) ≤ (∑ c, ν c*|f c|^n)/a^n

axiom rank_moment_split {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (rank : Ω → ℕ) (h R : ℕ) (hμ : Probability μ) :
    (∑ x, μ x/(2 : ℝ)^(h*rank x)) ≤
      cellMass μ (fun x => rank x < R)+1/(2 : ℝ)^(h*R)

end Lax342547.MomentTails
