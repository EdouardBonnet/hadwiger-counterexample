import Lax342547.RestrictionRank
import Lax342547.QuotientRank

/-!
---
title: Rank loss under two restrictions
type: lemma
---
A composition loses at most the output kernel dimension and the input range codimension, including the two quotient modes of a tensor.
-/

namespace Lax342547.RankLoss



axiom composition_rank_loss {K U V W X : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] X) (M : V →ₗ[K] W) (B : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.range (A.comp (M.comp B))) +
        Module.finrank K (LinearMap.ker A) +
        (Module.finrank K V-Module.finrank K (LinearMap.range B))

axiom matrix_sandwich_rank_loss {K I J P Q : Type} [Field K]
    [Fintype I] [Fintype J] [Fintype P] [Fintype Q]
    (A : Matrix P I K) (M : Matrix I J K) (B : Matrix Q J K) :
    M.rank ≤ (A*M*B.transpose).rank +
      Module.finrank K (LinearMap.ker A.mulVecLin) +
      Module.finrank K (LinearMap.ker B.mulVecLin)

axiom quotient_tensor_rank_loss {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : Module.Dual K V →ₗ[K] W) (S : Submodule K W) (T : Submodule K V) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.range (S.mkQ.comp (M.comp T.mkQ.dualMap))) +
      Module.finrank K S+Module.finrank K T

end Lax342547.RankLoss
