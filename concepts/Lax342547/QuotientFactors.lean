import Lax342547.ProjectedCoefficients
import Lax342547.RankFactors

/-!
---
title: Rank factors independent modulo the actual frozen spaces
type: definition and theorem
---
Projecting the coefficient tensor to complements of the frozen spaces gives rank factors whose quotient images are injective. This is the exact independence needed for conditional image entropy.
-/

namespace Lax342547.QuotientFactors

open Lax342547.MomentSpace

axiom factor_range {I J R : Type} [Fintype I] [Fintype J] [Fintype R]
    (C : Matrix I J Binary) (A : Matrix I R Binary) (B : Matrix J R Binary)
    (hC : A * B.transpose = C) (hA : Function.Injective A.mulVec)
    (hr : Fintype.card R = C.rank) : LinearMap.range A.mulVecLin = LinearMap.range C.mulVecLin

axiom projection_range_quotient_injective {V U : Type}
    [AddCommGroup V] [Module Binary V] [AddCommGroup U] [Module Binary U]
    (D : Submodule Binary V) (p : V →ₗ[Binary] V)
    (hp : LinearMap.ker p = D) (hpid : p.comp p = p)
    (A : U →ₗ[Binary] V) (hA : Function.Injective A)
    (hrange : LinearMap.range A ≤ LinearMap.range p) : Function.Injective (D.mkQ.comp A)

axiom quotient_independent_factors {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : LinearMap.ker p = D) (hq : LinearMap.ker q = E)
    (hpid : p.comp p = p) (hqid : q.comp q = q) : by
      classical
      let Z := p.toMatrix' * C * q.toMatrix'.transpose
      exact ∃ A : Matrix I (Fin Z.rank) Binary, ∃ B : Matrix I (Fin Z.rank) Binary,
        A * B.transpose = Z ∧ Function.Injective (D.mkQ.comp A.mulVecLin) ∧
          Function.Injective (E.mkQ.comp B.mulVecLin)

end Lax342547.QuotientFactors
