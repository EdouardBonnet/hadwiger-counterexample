import Lax342547.RankFactors
import Lax342547.RankedProjection
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
---
title: Entrywise product rank and incompatible tuples
type: lemma
---
Rank-factor expansions prove the entrywise product rank bound and the actual binary incompatibility obstruction.
-/

namespace Lax342547.HadamardRank

open Lax342547.MomentSpace
open scoped BigOperators Matrix

axiom hadamard_rank {I J : Type} [Fintype I] [Fintype J]
    (A B : Matrix I J Binary) : (A ⊙ B).rank ≤ A.rank*B.rank

axiom all_one_rank {I J : Type} [Fintype I] [Fintype J] :
    (Matrix.of (fun _ : I => fun _ : J => (1 : Binary))).rank ≤ 1

axiom one_add_rank {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J Binary) :
    ((Matrix.of (fun _ : I => fun _ : J => (1 : Binary)))+A).rank ≤ 1+A.rank

axiom incompatible_tuple_bound {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (F : Matrix Ω Ω Binary) (x : ι → Ω) (hdiag : ∀ a, F a a = 0)
    (hinc : ∀ i j, i ≠ j → ¬ (F (x i) (x j) = 0 ∧ F (x j) (x i) = 0)) :
    Fintype.card ι ≤ (1+F.rank)^2

axiom compatible_pair_in_tuple {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (F : Matrix Ω Ω Binary) (x : ι → Ω) (hdiag : ∀ a, F a a = 0)
    (hsize : (1+F.rank)^2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ F (x i) (x j) = 0 ∧ F (x j) (x i) = 0

end Lax342547.HadamardRank
