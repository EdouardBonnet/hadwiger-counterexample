import Lax342547.LowRankCounting
import Mathlib.Data.Fintype.Card

/-!
---
title: Counting component tensors with bounded total rank
type: lemma
---
Actual rank budgets and matrix factors give the uniform candidate count with ambient exponent (dim I+dim J)*r, rather than paying r for each component separately.
-/

namespace Lax342547.TotalRankCount

open Lax342547.MomentSpace
open scoped BigOperators

abbrev RankBudgets (e : Type) [Fintype e] (r : ℕ) :=
  {a : e → Fin (r+1) // ∑ i, (a i).val ≤ r}

abbrev Factors {e : Type} [Fintype e] (I J : Type) (r : ℕ) (a : RankBudgets e r) :=
  (∀ i : e, Matrix I (Fin (a.val i).val) Binary) ×
    (∀ i : e, Matrix (Fin (a.val i).val) J Binary)

noncomputable def reconstruct {e I J : Type} [Fintype e] (r : ℕ) :
    (Σ a : RankBudgets e r, Factors I J r a) → e → Matrix I J Binary :=
  fun z i => z.2.1 i*z.2.2 i

axiom exists_rank_factors {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    (r : ℕ) (A : e → Matrix I J Binary) (hA : ∑ i, (A i).rank ≤ r) :
    ∃ z : Σ a : RankBudgets e r, Factors I J r a, reconstruct r z = A

axiom factor_card_bound {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (r : ℕ) (a : RankBudgets e r) :
    Fintype.card (Factors I J r a) ≤ 2^((Fintype.card I+Fintype.card J)*r)

axiom total_rank_card {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (r : ℕ) :
    Fintype.card {A : e → Matrix I J Binary // ∑ i, (A i).rank ≤ r} ≤
      (r+1)^Fintype.card e*2^((Fintype.card I+Fintype.card J)*r)

end Lax342547.TotalRankCount
