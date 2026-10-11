import Lax342547.MomentSpace
import Mathlib.Algebra.Module.ZMod

/-!
---
title: Formal ordered product bits realize symmetric corrections
type: lemma
---
For every ordered pair there is at least one allowed product index. One
such term realizes any off-diagonal correction to a symmetric matrix,
while symmetrization keeps its diagonal fixed. These are formal bit
prescriptions; existence of actual parameters satisfying them is a
separate probabilistic assertion.
-/

namespace Lax342547.BinaryPrescriptions

open Lax342547.MomentSpace

def productSum {I Term : Type} [Fintype Term] (L R : I → I → Term → Binary) (x y : I) : Binary :=
  ∑ t, L x y t * R x y t

axiom realize {I Term : Type} [Fintype I] [Fintype Term]
    (allowed : I → I → Term → Prop) (hallowed : ∀ x y, ∃ t, allowed x y t)
    (T₀ M : Matrix I I Binary) (hT : ∀ x y, T₀ x y = T₀ y x)
    (hM : ∀ x y, M x y = M y x) (hdiag : ∀ x, M x x = T₀ x x) :
    ∃ L R : I → I → Term → Binary,
      (∀ x y t, ¬ allowed x y t → L x y t = 0 ∧ R x y t = 0) ∧
      ∀ x y, T₀ x y + productSum L R x y + productSum L R y x = M x y

end Lax342547.BinaryPrescriptions
