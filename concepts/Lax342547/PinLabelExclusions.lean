import Lax342547.KeySpans
import Lax342547.SparsePins

/-!
---
title: Sparse pin exclusions with arbitrary base coefficients
type: definition and theorem
---
The annihilator argument needs more than independence of fresh point
rays: an expansion may mix selected fresh labels with other labels in
the exclusion. The uniform cover bounds every nonzero base-vector label
coefficient of every short projected pin expansion.
-/

namespace Lax342547.PinLabelExclusions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.SparsePins Lax342547.KeySpans

variable {Base Comp H N : Type} {b degree : ℕ}

def Covers
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (R : ℕ) : Prop :=
  ∀ i a (L : Finset (Fin b → Binary)) (v : (Fin b → Binary) → Option Base → Binary),
    L.card ≤ R + 14 →
    (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈ projected P i a →
    ∀ s ∈ L, v s ≠ 0 → s ∈ A i

axiom covers_exists [Fintype Base] [Fintype Comp] [Fintype H] {K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ A : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (A i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧ Covers P A R

axiom fresh_coefficient {R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (v : (Fin b → Binary) → Option Base → Binary) (hL : L.card ≤ R + 14)
    (hmem : (∑ t ∈ L, labelTensor (selectorEval (degree := degree)) t (v t)) ∈ projected P i a)
    (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i) : v s = 0

axiom keys_exclusion {R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R) : Excludes P A

end Lax342547.PinLabelExclusions
