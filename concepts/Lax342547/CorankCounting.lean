import Lax342547.LowRankCounting

/-!
---
title: The row-corank bound for a uniform binary matrix
type: theorem
---
A matrix with row corank at least s admits s independent row relations.
Count the relation matrix first, then require every column to lie in its
kernel. This gives the sharper 2^(ms-sn) probability bound used for the
bounded row lists in Lemma 5.5, written as a ratio of nonnegative powers.
-/

namespace Lax342547.CorankCounting

axiom exists_row_relations {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) (s : ℕ) (hs : M.rank + s ≤ Fintype.card I) :
    ∃ C : Matrix (Fin s) I K, Function.Surjective C.mulVec ∧ C * M = 0

open Lax342547.MomentSpace
open scoped ENNReal

axiom card_corank {I J : Type} [Fintype I] [Fintype J] (s : ℕ) :
    Nat.card {M : Matrix I J Binary // M.rank + s ≤ Fintype.card I} ≤
      2 ^ (s * Fintype.card I + (Fintype.card I - s) * Fintype.card J)

axiom uniform_corank_bound {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (s : ℕ) :
    (PMF.uniformOfFintype (Matrix I J Binary)).toOuterMeasure {M | M.rank + s ≤ Fintype.card I} ≤
      (2 : ℝ≥0∞) ^ (s * Fintype.card I) / 2 ^ (s * Fintype.card J)

end Lax342547.CorankCounting
