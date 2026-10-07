/-
Adapted from OpenAI, openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
Changes: Lax package separation, namespaces, explicit variables, and archive annotations.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat

/-!
---
title: Clique minors and the Hadwiger number
type: definition
---
A $K_t$ minor is a family of $t$ nonempty connected, pairwise disjoint branch
sets, with an edge joining every two distinct branch sets. The Hadwiger
number $h(G)$ is the largest such $t$ for a finite graph.
-/

namespace Lax342547.CliqueMinor

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | HasCliqueMinor G t}


end Lax342547.CliqueMinor
