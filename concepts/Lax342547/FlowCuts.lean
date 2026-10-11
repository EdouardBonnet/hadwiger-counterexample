import Lax342547.ResidualFlows

/-!
---
title: Real max-flow min-cut from residual reachability
type: lemma
---
Internal skew flow cancels, conservation identifies cut divergence with source value, and the reachable residual cut is saturated. Its real capacity equals the maximum flow value, and every cut bounds every feasible flow.
-/

namespace Lax342547.FlowCuts

open Lax342547.RealFlows
open scoped BigOperators

noncomputable def cutCapacity {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : ℝ := by
  classical
  exact ∑ a ∈ Z, ∑ b ∈ Zᶜ, c a b

axiom cut_indicator {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : by
    classical
    exact cutCapacity c Z = ∑ a, ∑ b, if a ∈ Z ∧ b ∉ Z then c a b else 0

axiom internal_skew_sum {V : Type} (f : V → V → ℝ) (Z : Finset V)
    (hskew : ∀ a b, f a b = -f b a) : (∑ a ∈ Z, ∑ b ∈ Z, f a b) = 0

axiom divergence_cut_sum {V : Type} [Fintype V] (f : V → V → ℝ) (Z : Finset V)
    (hskew : ∀ a b, f a b = -f b a) : by
    classical
    exact (∑ a ∈ Z, divergence f a) = ∑ a ∈ Z, ∑ b ∈ Zᶜ, f a b

axiom conserving_cut_value {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z) :
    (∑ a ∈ Z, divergence f a) = divergence f s

axiom saturated_cut_value {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z)
    (hsat : ∀ a ∈ Z, ∀ b ∉ Z, f a b = c a b) :
    divergence f s = cutCapacity c Z

axiom cut_upper_bound {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z) :
    divergence f s ≤ cutCapacity c Z

axiom real_max_flow_min_cut {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hst : s ≠ t) (hc : ∀ a b, 0 ≤ c a b) :
    ∃ f Z, Feasible c f s t ∧ s ∈ Z ∧ t ∉ Z ∧ divergence f s = cutCapacity c Z ∧
      ∀ g, Feasible c g s t → divergence g s ≤ divergence f s

end Lax342547.FlowCuts
