import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.Distributions.Uniform

/-!
---
title: Factorization and counting of low-rank binary matrices
type: lemma
---
A rank-at-most-r matrix factors through r coordinates. Counting the two
factors gives the rectangular low-rank estimate used for binary mixer
tests, including the alternating off-diagonal block argument.
-/

namespace Lax342547.LowRankCounting

axiom factorization {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) (r : ℕ) (hr : M.rank ≤ r) :
    ∃ X : Matrix I (Fin r) K, ∃ Y : Matrix (Fin r) J K, X * Y = M

open Lax342547.MomentSpace
open scoped ENNReal

axiom card_low_rank {I J : Type} [Fintype I] [Fintype J] (r : ℕ) :
    Nat.card {M : Matrix I J Binary // M.rank ≤ r} ≤ 2 ^ ((Fintype.card I + Fintype.card J) * r)

axiom uniform_low_rank_bound {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : ℕ) : (PMF.uniformOfFintype (Matrix I J Binary)).toOuterMeasure {M | M.rank ≤ r} ≤
      (2 : ℝ≥0∞) ^ ((Fintype.card I + Fintype.card J) * r) / 2 ^ (Fintype.card I * Fintype.card J)

end Lax342547.LowRankCounting
