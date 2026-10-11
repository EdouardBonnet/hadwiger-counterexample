import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
---
title: Rank and density budgets for exact-image peeling
type: lemma
---
Compare the retained leaf mass with its absolute reference-image cap.
The comparison bounds the cumulative new rank, including a single large
violating tuple, and controls the cost of normalizing the leaf law.
-/

namespace Lax342547.PeelingBudget

open scoped ENNReal

axiom rank_comparison (D ζ ε : ℝ) (N u : ℕ) (hN : 0 < N) (m : ℝ≥0∞)
    (hlower : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u < m)
    (hupper : m ≤ (2 : ℝ≥0∞) ^ (D * N) * ((2 : ℝ≥0∞) ^ (-((1 - ε) * N))) ^ u) :
    (ζ - ε) * u < D + ζ

axiom conservative_rank_bound (D ζ ε : ℝ) (u : ℕ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (h : (ζ - ε) * u < D + ζ) : (u : ℝ) < 4 * (D + 1) / ζ

axiom density_cost (D ζ : ℝ) (N u K : ℕ) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1)
    (hu : u ≤ K) (m : ℝ≥0∞)
    (hm : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u ≤ m) :
    (2 : ℝ≥0∞) ^ (D * N) / m ≤ (2 : ℝ≥0∞) ^ ((D + K + 1) * N)

end Lax342547.PeelingBudget
