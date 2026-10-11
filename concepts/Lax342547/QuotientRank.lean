import Lax342547.RestrictionRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
---
title: Rank of a tensor killed in two quotient spaces
type: lemma
---
The component-rank step in the annihilator argument of §6. Killing a
matrix after projecting both factors loses at most the sum of the two
kernel dimensions.
-/

namespace Lax342547.QuotientRank

axiom killed_composition_rank {K U V W X : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] X) (M : V →ₗ[K] W) (B : U →ₗ[K] V)
    (h : A.comp (M.comp B) = 0) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.ker A) +
        (Module.finrank K V - Module.finrank K (LinearMap.range B))

axiom killed_matrix_rank {K I J P Q : Type} [Field K]
    [Fintype I] [Fintype J] [Fintype P] [Fintype Q]
    (A : Matrix P I K) (M : Matrix I J K) (B : Matrix Q J K)
    (h : A * M * B.transpose = 0) :
    M.rank ≤ Module.finrank K (LinearMap.ker A.mulVecLin) +
      Module.finrank K (LinearMap.ker B.mulVecLin)

axiom killed_quotients_rank {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : Module.Dual K V →ₗ[K] W) (S : Submodule K W) (T : Submodule K V)
    (h : S.mkQ.comp (M.comp T.mkQ.dualMap) = 0) :
    Module.finrank K (LinearMap.range M) ≤ Module.finrank K S + Module.finrank K T

end Lax342547.QuotientRank
