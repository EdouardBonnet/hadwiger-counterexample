import Lax342547.LowRankCounting

/-!
---
title: Symmetric low-rank factorization, including characteristic two
type: theorem
---
A symmetric rank-r matrix has a factorization Z H Zᵀ with Z injective
and H symmetric and nonsingular. No assumption on the diagonal is made.
Counting these factors gives the symmetric-matrix estimate in Lemma 5.5.
-/

namespace Lax342547.SymmetricFactorization

axiom symmetric_factorization {K I : Type} [Field K] [Fintype I]
    (M : Matrix I I K) (hM : M.transpose = M) :
    ∃ Z : Matrix I (Fin M.rank) K, ∃ H : Matrix (Fin M.rank) (Fin M.rank) K,
      Function.Injective Z.mulVec ∧ H.transpose = H ∧ Function.Bijective H.mulVec ∧
      Z * H * Z.transpose = M

open Lax342547.MomentSpace

axiom card_symmetric_rank {I : Type} [Fintype I] (r : ℕ) :
    Nat.card {M : Matrix I I Binary // M.transpose = M ∧ M.rank = r} ≤
      2 ^ (Fintype.card I * r + r * r)

end Lax342547.SymmetricFactorization
