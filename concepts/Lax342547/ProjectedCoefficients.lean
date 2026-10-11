import Lax342547.FrozenCharacters
import Lax342547.TargetMatrices

/-!
---
title: Split quotient projections preserve coefficient characters
type: lemma
---
Choose projections with the actual frozen space as kernel. Removing the projected coefficient matrix leaves a tensor annihilating every form on the two frozen quotients.
-/

namespace Lax342547.ProjectedCoefficients

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorAnnihilators

axiom exists_quotient_projection {I : Type} [Fintype I]
    (D : Submodule Binary (I → Binary)) :
    ∃ p : (I → Binary) →ₗ[Binary] (I → Binary),
      D.mkQ.comp p = D.mkQ ∧ LinearMap.ker p = D ∧ p.comp p = p

axiom projection_preserves_quotient_pairing {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : D.mkQ.comp p = D.mkQ) (hq : E.mkQ.comp q = E.mkQ) : by
      classical
      exact PureAnnihilates (C - p.toMatrix' * C * q.toMatrix'.transpose) D E

end Lax342547.ProjectedCoefficients
