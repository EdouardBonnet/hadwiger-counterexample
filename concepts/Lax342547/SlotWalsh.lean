import Lax342547.BilinearWalsh

/-!
---
title: Bit rank and Walsh bounds for global vector-slot pairings
type: definition and theorem
---
Each of N bit coordinates carries the same cross-slot coefficient
matrix. The resulting bilinear bit matrix has rank N times its rank,
so a nonzero cross pattern has correlation at most 2^(-N/2).
-/

namespace Lax342547.SlotWalsh

open Lax342547.MomentSpace

def bitMatrix {I J : Type} (C : Matrix I J Binary) (N : ℕ) :
    Matrix (Fin N × I) (Fin N × J) Binary :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

axiom bit_evaluation {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) (N : ℕ) (x : Fin N × I → Binary) (y : Fin N × J → Binary) :
    dotProduct x ((bitMatrix C N).mulVec y) = ∑ i, ∑ j, C i j * ∑ a, x (a, i) * y (a, j)

axiom bit_rank {I J : Type} [Fintype J]
    (C : Matrix I J Binary) (N : ℕ) : (bitMatrix C N).rank = N * C.rank

axiom nonzero_pattern_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (C : Matrix I J Binary) (hC : C ≠ 0) (N : ℕ)
    (f : (Fin N × I → Binary) → ℝ) (g : (Fin N × J → Binary) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |BilinearWalsh.average (bitMatrix C N) f g| ≤ 1 / Real.sqrt ((2 : ℝ) ^ N)

end Lax342547.SlotWalsh
