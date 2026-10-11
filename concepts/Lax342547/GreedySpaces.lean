import Lax342547.FiniteSampling
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Greedy independence of subspaces
type: lemma
---
Disjointness from accumulated pin spans constructs independent subspaces with an explicit cumulative dimension budget.
-/

namespace Lax342547.GreedySpaces

open Lax342547.MomentSpace
open scoped BigOperators

axiom independent_snoc {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (U : Fin n → Submodule K V) (W : Submodule K V)
    (hU : iSupIndep U) (hW : Disjoint W (⨆ i,U i)) : iSupIndep (Fin.snoc U W)

axiom finite_span_dimension {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : ι → Submodule K V) (S : Finset ι) :
    Module.finrank K ↥(S.sup U) ≤ ∑ i ∈ S,Module.finrank K (U i)

axiom accumulated_dimension {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Ω → Submodule K V) (r n : ℕ) (s : Fin n → Ω)
    (hU : ∀ x,Module.finrank K (U x) ≤ r) :
    Module.finrank K ↥(⨆ i : Fin n,U (s i)) ≤ r*n

end Lax342547.GreedySpaces
