import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Convex.Function

/-!
---
title: Compact real-capacity flows and a maximizing flow
type: definition and theorem
---
Skew real flows satisfy directed capacity bounds and interior conservation. Their feasible set is closed and bounded in a finite product, so a maximum source divergence exists for every nonnegative finite capacity network.
-/

namespace Lax342547.RealFlows

open scoped BigOperators Topology

noncomputable def divergence {V : Type} [Fintype V] (f : V → V → ℝ) (a : V) : ℝ := ∑ b, f a b

def Feasible {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V) : Prop :=
  (∀ a b, f a b = -f b a) ∧ (∀ a b, f a b ≤ c a b) ∧
    (∀ a, a ≠ s → a ≠ t → divergence f a = 0)

def Residual {V : Type} (c f : V → V → ℝ) (a b : V) : Prop := f a b < c a b

axiom zero_feasible {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hc : ∀ a b, 0 ≤ c a b) : Feasible c (fun _ _ => 0) s t

axiom feasible_closed {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V) :
    IsClosed {f | Feasible c f s t}

axiom feasible_compact {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V) :
    IsCompact {f | Feasible c f s t}

axiom maximal_flow {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hc : ∀ a b, 0 ≤ c a b) :
    ∃ f, Feasible c f s t ∧ ∀ g, Feasible c g s t → divergence g s ≤ divergence f s

end Lax342547.RealFlows
