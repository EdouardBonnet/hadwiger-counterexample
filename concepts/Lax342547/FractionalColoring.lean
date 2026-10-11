import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
---
title: Ordinary fractional coloring
type: lemma
---
A fractional coloring assigns nonnegative real weights to independent sets
so that the weights covering each vertex sum to at least one. The fractional
chromatic number $\chi_f(G)$ is the infimum of the total weight.
For finite graphs with independence number at most two,
$|V(G)|/2\le\chi_f(G)\le\chi(G)$.
-/

namespace Lax342547.FractionalColoring

open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

structure Coloring (G : SimpleGraph V) where
  weight : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ weight S
  supported : ∀ (S : Finset V), ¬ G.IsIndepSet (S : Set V) → weight S = 0
  covers : ∀ v, 1 ≤ ∑ S : Finset V, if v ∈ S then weight S else 0

noncomputable def totalWeight {G : SimpleGraph V} (C : Coloring G) : ℝ :=
  ∑ S : Finset V, C.weight S

noncomputable def fractionalChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf {w : ℝ | ∃ C : Coloring G, totalWeight C = w}

axiom fractional_chromatic_lower_bound (G : SimpleGraph V) (hα : G.indepNum ≤ 2) :
    (Fintype.card V : ℝ) / 2 ≤ fractionalChromaticNumber G

axiom fractional_chromatic_le_chromatic (G : SimpleGraph V) :
    fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ)

end Lax342547.FractionalColoring
