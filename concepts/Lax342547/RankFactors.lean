import Lax342547.ProductImages

/-!
---
title: Full rank coefficient factorizations
type: lemma
---
Every binary coefficient matrix factors into two independently injective tuples of exactly its rank. These tuples supply the independent image directions in the nonzero quotient character test.
-/

namespace Lax342547.RankFactors

open Lax342547.MomentSpace

axiom independent_rank_factors {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) :
    ∃ A : Matrix I (Fin C.rank) Binary, ∃ B : Matrix J (Fin C.rank) Binary,
      A * B.transpose = C ∧ Function.Injective A.mulVec ∧ Function.Injective B.mulVec

end Lax342547.RankFactors
