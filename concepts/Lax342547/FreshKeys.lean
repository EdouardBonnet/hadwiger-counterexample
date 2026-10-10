import Lax342547.TableSpaces
import Lax342547.SparsePins

/-!
---
title: Fresh key directions are independent modulo table spaces
type: theorem
---
One bounded exclusion set per endpoint works for all components and both
signs. Any short linear combination of distinct fresh point rays that
belongs to a table space has all its coefficients zero.
-/

namespace Lax342547.FreshKeys

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

axiom fresh_points {Base Comp : Type} [Fintype Base] [Fintype Comp] {b degree K R : ℕ}
    (U : Bool → Comp → Submodule Binary (SelectorCoordinates b degree × Option Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Comp * K * (R + 14) ∧
      ∀ sign e (L : Finset (Fin b → Binary)) (c : (Fin b → Binary) → Binary)
        (z : (Fin b → Binary) → Base → Binary),
        L.card ≤ R + 14 → Disjoint L B →
        (∑ s ∈ L, c s • point (selectorEval (degree := degree)) s (z s)) ∈ U sign e →
        ∀ s ∈ L, c s = 0

axiom fresh_keys {Base Comp H N : Type} [Fintype Base] [Fintype Comp] [Fintype H]
    {b degree K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (B i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧
      ∀ (a : Comp × Bool) (L : Fin 2 → Finset (Fin b → Binary))
        (c : Fin 2 → (Fin b → Binary) → Binary)
        (z : Fin 2 → (Fin b → Binary) → Base → Binary),
        (∀ i, (L i).card ≤ R + 14) → (∀ i, Disjoint (L i) (B i)) →
        (∑ i : Fin 2, ∑ s ∈ L i,
          c i s • primalEmbedding i (point (selectorEval (degree := degree)) s (z i s))) ∈
            tableSpace P a →
        ∀ i s, s ∈ L i → c i s = 0

end Lax342547.FreshKeys
