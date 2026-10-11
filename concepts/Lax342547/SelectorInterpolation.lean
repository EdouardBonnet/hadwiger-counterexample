import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
---
title: Interpolation of finitely many binary selector labels
type: lemma
---
The second assertion of Lemma 5.1: any u distinct selector evaluation
vectors are linearly independent when the degree bound is at least u−1.
-/

namespace Lax342547.SelectorInterpolation

open Lax342547.MomentSpace

def monomial {b : ℕ} (S : Finset (Fin b)) : (Fin b → Binary) → Binary :=
  fun s => ∏ i ∈ S, s i

def selectorSpan (b degree : ℕ) : Submodule Binary ((Fin b → Binary) → Binary) :=
  Submodule.span Binary {f | ∃ S : Finset (Fin b), S.card ≤ degree ∧ f = monomial S}

axiom selectorEval_linearIndependent {ι : Type} [Fintype ι] {b degree : ℕ}
    (s : ι → Fin b → Binary) (hs : Function.Injective s)
    (hdegree : Fintype.card ι ≤ degree + 1) :
    LinearIndependent Binary (fun i => selectorEval (degree := degree) (s i))

end Lax342547.SelectorInterpolation
