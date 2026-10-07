/-
Adapted from OpenAI, openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
Changes: Lax package separation, namespaces, explicit variables, and archive annotations.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: Connected matchings
type: definition
---
A connected matching is a matching whose distinct edges are joined by an edge.
Its maximum size is the connected-matching number $\mathrm{cm}(G)$.
-/

namespace Lax342547.ConnectedMatching

universe u
variable {V : Type u}

/-- A finite matching whose edges are pairwise touching: each member is a
two-vertex clique, and distinct members are disjoint and joined by an edge. -/
def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

/-- The supremum of the cardinalities of pairwise touching matchings.
For finite vertex types, this supremum is attained. -/
noncomputable def connectedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), IsTouchingMatching G M ∧ M.card = n}

end Lax342547.ConnectedMatching
