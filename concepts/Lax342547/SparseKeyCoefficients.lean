import Lax342547.QuotientExtractors

/-!
---
title: Unselected sparse vectors cannot conceal fresh key coefficients
type: theorem
---
If an unselected sparse vector differs from a short fresh key combination
by a projected pin, each key's base-vector coefficient is zero. This
also covers inactive keys whose base vector is already zero.
-/

namespace Lax342547.SparseKeyCoefficients

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.PinLabelExclusions Lax342547.SparsePins

axiom coefficients_zero {Base Comp H N I : Type} [Fintype I] {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (v : (Fin b → Binary) → Option Base → Binary)
    (label : I → Fin b → Binary) (hlabel : Function.Injective label)
    (base : I → Option Base → Binary) (hcard : Fintype.card I ≤ 14)
    (hfresh : ∀ j, label j ∉ A i)
    (hdisjoint : Disjoint L (Finset.univ.image label)) (c : I → Binary)
    (h : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) -
      (∑ j, c j • labelTensor (selectorEval (degree := degree)) (label j) (base j)) ∈ projected P i a) :
    ∀ j, c j • base j = 0

end Lax342547.SparseKeyCoefficients
