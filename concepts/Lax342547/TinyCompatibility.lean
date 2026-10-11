import Lax342547.HadamardRank
import Lax342547.PairPositions

/-!
---
title: Inverse-polynomial tiny-cover compatibility
type: lemma
---
The actual binary pairing kernel of rank at most d*N has compatible pair mass at least 1/(4*(1+d*N)^4) under any finite probability law with zero diagonal.
-/

namespace Lax342547.TinyCompatibility

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.CellAveraging

axiom tiny_compatible_mass {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) :
    1/(((1+F.rank)^2+1 : ℕ) : ℝ)^2 ≤ pairEventMass μ μ (fun a b => F a b = 0 ∧ F b a = 0)

axiom tiny_compatible_mass_rank_bound {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (d N : ℕ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N) :
    1/(4*(1+(d : ℝ)*N)^4) ≤ pairEventMass μ μ (fun a b => F a b = 0 ∧ F b a = 0)

end Lax342547.TinyCompatibility
