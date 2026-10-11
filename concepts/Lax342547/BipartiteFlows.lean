import Lax342547.FlowCuts
import Mathlib.Algebra.BigOperators.Field

/-!
---
title: Bipartite capacity networks
type: lemma
---
Real flows encode probability laws with two marginal caps and a pointwise pair cap; infeasibility yields a cut of capacity less than one.
-/

namespace Lax342547.BipartiteFlows

open Lax342547.RealFlows
open scoped BigOperators

abbrev Vertex (A B : Type) := Bool ⊕ (A ⊕ B)

def source {A B : Type} : Vertex A B := .inl false
def sink {A B : Type} : Vertex A B := .inl true
def left {A B : Type} (a : A) : Vertex A B := .inr (.inl a)
def right {A B : Type} (b : B) : Vertex A B := .inr (.inr b)

noncomputable def capacity {A B : Type} (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) :
    Vertex A B → Vertex A B → ℝ
  | .inl false, .inr (.inl x) => a x
  | .inr (.inl x), .inr (.inr y) => p x y
  | .inr (.inr y), .inl true => b y
  | _, _ => 0

axiom capacity_nonneg {A B : Type} (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y) :
    ∀ u v, 0 ≤ capacity a b p u v

axiom zero_capacity_flow {V : Type} [Fintype V] (c f : V → V → ℝ) (s t u v : V)
    (hf : Feasible c f s t) (huv : c u v = 0) (hvu : c v u = 0) : f u v = 0

axiom forward_flow_nonneg {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (x : A) (y : B) : 0 ≤ f (left x) (right y)

axiom left_conservation {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (x : A) :
    (∑ y, f (left x) (right y)) = f source (left x)

axiom right_conservation {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (y : B) :
    (∑ x, f (left x) (right y)) = f (right y) sink

axiom source_flow_total {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) :
    divergence f source = ∑ x, ∑ y, f (left x) (right y)

def Law {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p ρ : A → B → ℝ) : Prop :=
  (∀ x y, 0 ≤ ρ x y) ∧ (∑ x, ∑ y, ρ x y) = 1 ∧
    (∀ x, (∑ y, ρ x y) ≤ a x) ∧ (∀ y, (∑ x, ρ x y) ≤ b y) ∧ (∀ x y, ρ x y ≤ p x y)

axiom normalized_flow_law {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y)
    (hv : 1 ≤ divergence f source) : ∃ ρ, Law a b p ρ

axiom infeasible_cut {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y)
    (hn : ¬ ∃ ρ, Law a b p ρ) :
    ∃ Z : Finset (Vertex A B), source ∈ Z ∧ sink ∉ Z ∧
      Lax342547.FlowCuts.cutCapacity (capacity a b p) Z < 1

end Lax342547.BipartiteFlows
