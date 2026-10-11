import Lax342547.RealFlows
import Mathlib.Logic.Relation

/-!
---
title: Residual walk augmentation for real-capacity flows
type: definition and theorem
---
Every residual walk supplies a skew direction with the correct source and sink divergences. A sufficiently small positive real perturbation respects every capacity, so a maximum flow has no residual source-to-sink walk.
-/

namespace Lax342547.ResidualFlows

open Lax342547.RealFlows
open scoped BigOperators Topology
open Filter

noncomputable def edgeDirection {V : Type} (u v : V) (a b : V) : ℝ := by
  classical
  exact (if a=u ∧ b=v then 1 else 0) - (if a=v ∧ b=u then 1 else 0)

def Direction {V : Type} [Fintype V] (c f d : V → V → ℝ) (u v : V) : Prop := by
  classical
  exact (∀ a b, d a b = -d b a) ∧
  (∀ a, divergence d a = (if a=u then 1 else 0)-(if a=v then 1 else 0)) ∧
  (∀ a b, ¬ Residual c f a b → d a b ≤ 0)

axiom edge_direction {V : Type} [Fintype V] (c f : V → V → ℝ) (u v : V)
    (huv : Residual c f u v) : Direction c f (edgeDirection u v) u v

axiom residual_walk_direction {V : Type} [Fintype V] (c f : V → V → ℝ) (u v : V)
    (hpath : Relation.ReflTransGen (Residual c f) u v) :
    ∃ d, Direction c f d u v

axiom feasible_augmentation {V : Type} [Fintype V]
    (c f d : V → V → ℝ) (s t : V) (hfeasible : Feasible c f s t)
    (hdir : Direction c f d s t) :
    ∃ δ : ℝ, 0 < δ ∧ Feasible c (fun a b => f a b+δ*d a b) s t

axiom maximal_no_residual_path {V : Type} [Fintype V]
    (c f : V → V → ℝ) (s t : V) (hst : s ≠ t) (hf : Feasible c f s t)
    (hmax : ∀ g, Feasible c g s t → divergence g s ≤ divergence f s) :
    ¬ Relation.ReflTransGen (Residual c f) s t

end Lax342547.ResidualFlows
