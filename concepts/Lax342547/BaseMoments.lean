import Lax342547.MomentSpace

/-!
---
title: The exact space of binary base moments
type: lemma
---
The first assertion of Lemma 5.1: the span of $(1,z)(1,z)^T$ consists
exactly of the symmetric matrices satisfying $Z_{ii}=Z_{0i}$.
The distinguished constant coordinate is `none`.
-/

namespace Lax342547.BaseMoments

open Lax342547.MomentSpace

def baseMoment {Base : Type} (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  fun i j => baseEval z i * baseEval z j

def baseMomentSpace (Base : Type) : Submodule Binary (Matrix (Option Base) (Option Base) Binary) :=
  Submodule.span Binary (Set.range (baseMoment (Base := Base)))

def IsBaseMoment {Base : Type} (Z : Matrix (Option Base) (Option Base) Binary) : Prop :=
  (∀ i j, Z i j = Z j i) ∧ ∀ i, Z i i = Z none i

axiom mem_baseMomentSpace_iff {Base : Type} [Fintype Base]
    (Z : Matrix (Option Base) (Option Base) Binary) :
    Z ∈ baseMomentSpace Base ↔ IsBaseMoment Z

end Lax342547.BaseMoments
