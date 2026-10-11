import Lax342547.FreshKeys
import Lax342547.NominalPrimal

/-!
---
title: Fresh point-ray spans are disjoint from the nominal table spaces
type: lemma
---
The finite-set sparse exclusions give independence for arbitrary indexed
families of at most fourteen rays per endpoint. In particular the span
of all selected rays intersects each table space only at zero.
-/

namespace Lax342547.KeySpans

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces

variable {Base Comp H N : Type} {b degree : ℕ}

def Excludes
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) : Prop :=
  ∀ (a : Comp × Bool) (L : Fin 2 → Finset (Fin b → Binary))
    (c : Fin 2 → (Fin b → Binary) → Binary)
    (z : Fin 2 → (Fin b → Binary) → Base → Binary),
    (∀ i, (L i).card ≤ 14) → (∀ i, Disjoint (L i) (A i)) →
    (∑ i : Fin 2, ∑ s ∈ L i, c i s •
      primalEmbedding i (point (selectorEval (degree := degree)) s (z i s))) ∈ tableSpace P a →
    ∀ i s, s ∈ L i → c i s = 0

def ray {I : Fin 2 → Type} (label : ∀ i, I i → Fin b → Binary)
    (base : ∀ i, I i → Base → Binary) (x : Σ i, I i) :
    (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) → Binary :=
  primalEmbedding x.1 (point (selectorEval (degree := degree)) (label x.1 x.2) (base x.1 x.2))

axiom exclusions_exists [Fintype Base] [Fintype Comp] [Fintype H] {K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ A : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (A i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧ Excludes P A

axiom independent_sum {I : Fin 2 → Type} [∀ i, Fintype (I i)]
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (label : ∀ i, I i → Fin b → Binary) (base : ∀ i, I i → Base → Binary)
    (hlabel : ∀ i, Function.Injective (label i)) (hcard : ∀ i, Fintype.card (I i) ≤ 14)
    (hfresh : ∀ i x, label i x ∉ A i) (a : Comp × Bool) (c : (Σ i, I i) → Binary)
    (h : (∑ x, c x • ray (H := H) label base x) ∈ tableSpace P a) : ∀ x, c x = 0

axiom span_disjoint {I : Fin 2 → Type} [∀ i, Fintype (I i)]
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (label : ∀ i, I i → Fin b → Binary) (base : ∀ i, I i → Base → Binary)
    (hlabel : ∀ i, Function.Injective (label i)) (hcard : ∀ i, Fintype.card (I i) ≤ 14)
    (hfresh : ∀ i x, label i x ∉ A i) (a : Comp × Bool) :
    Disjoint (tableSpace P a) (Submodule.span Binary (Set.range (ray (H := H) label base)))

end Lax342547.KeySpans
