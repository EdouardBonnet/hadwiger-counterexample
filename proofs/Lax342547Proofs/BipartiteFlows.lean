import Lax342547.BipartiteFlows
import Mathlib.Algebra.BigOperators.Field
import Lax342547.FlowCuts

namespace Lax342547Proofs.BipartiteFlows
open Lax342547.BipartiteFlows

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealFlows
open scoped BigOperators

/--
---
conclusion: Lax342547.BipartiteFlows.capacity_nonneg
---
-/
theorem capacity_nonneg {A B : Type} (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y) :
    ∀ u v, 0 ≤ capacity a b p u v := by
  intro u v
  rcases u with (u|u) <;> rcases v with (v|v)
  · cases u <;> cases v <;> simp [capacity]
  · cases u <;> rcases v with (x|y) <;> simp [capacity,ha]
  · cases v <;> rcases u with (x|y) <;> simp [capacity,hb]
  · rcases u with (x|y) <;> rcases v with (x'|y') <;> simp [capacity,hp]

/--
---
conclusion: Lax342547.BipartiteFlows.zero_capacity_flow
---
-/
theorem zero_capacity_flow {V : Type} [Fintype V] (c f : V → V → ℝ) (s t u v : V)
    (hf : Feasible c f s t) (huv : c u v = 0) (hvu : c v u = 0) : f u v = 0 := by
  have h₁ := hf.2.1 u v
  have h₂ := hf.2.1 v u
  rw [huv] at h₁
  rw [hvu,hf.1 v u] at h₂
  linarith

/--
---
conclusion: Lax342547.BipartiteFlows.forward_flow_nonneg
---
-/
theorem forward_flow_nonneg {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (x : A) (y : B) : 0 ≤ f (left x) (right y) := by
  have h := hf.2.1 (right y) (left x)
  change f (right y) (left x) ≤ 0 at h
  rw [hf.1 (right y) (left x)] at h
  linarith

/--
---
conclusion: Lax342547.BipartiteFlows.left_conservation
---
-/
theorem left_conservation {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (x : A) :
    (∑ y, f (left x) (right y)) = f source (left x) := by
  have h := hf.2.2 (left x) (by simp [left,source]) (by simp [left,sink])
  have ht : f (left x) sink = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  have hl (z : A) : f (left x) (left z) = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  unfold divergence at h
  rw [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_sum_type] at h
  change f (left x) sink+f (left x) source+
    ((∑ z, f (left x) (left z))+(∑ y, f (left x) (right y))) = 0 at h
  rw [ht,hf.1 (left x) source] at h
  simp_rw [hl] at h
  simp only [Finset.sum_const_zero] at h
  linarith

/--
---
conclusion: Lax342547.BipartiteFlows.right_conservation
---
-/
theorem right_conservation {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (y : B) :
    (∑ x, f (left x) (right y)) = f (right y) sink := by
  have h := hf.2.2 (right y) (by simp [right,source]) (by simp [right,sink])
  have hs : f (right y) source = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  have hr (z : B) : f (right y) (right z) = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  unfold divergence at h
  rw [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_sum_type] at h
  change f (right y) sink+f (right y) source+
    ((∑ x, f (right y) (left x))+(∑ z, f (right y) (right z))) = 0 at h
  rw [hs] at h
  simp_rw [hr] at h
  have hh : (∑ x, f (right y) (left x)) = -(∑ x, f (left x) (right y)) := by
    simp_rw [hf.1 (right y)]
    rw [Finset.sum_neg_distrib]
  rw [hh] at h
  simp only [Finset.sum_const_zero] at h
  linarith

/--
---
conclusion: Lax342547.BipartiteFlows.source_flow_total
---
-/
theorem source_flow_total {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) :
    divergence f source = ∑ x, ∑ y, f (left x) (right y) := by
  have hss : f source source = 0 := by have h := hf.1 source source; linarith
  have hst : f source sink = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  have hr (y : B) : f source (right y) = 0 := Lax342547.BipartiteFlows.zero_capacity_flow _ f source sink _ _ hf rfl rfl
  unfold divergence
  rw [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_sum_type]
  change f source sink+f source source+((∑ x, f source (left x))+(∑ y, f source (right y))) = _
  simp_rw [hst,hss,hr]
  simp only [Finset.sum_const_zero,zero_add,add_zero]
  apply Finset.sum_congr rfl
  intro x _
  exact (Lax342547.BipartiteFlows.left_conservation a b p f hf x).symm

/--
---
conclusion: Lax342547.BipartiteFlows.normalized_flow_law
---
-/
theorem normalized_flow_law {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y)
    (hv : 1 ≤ divergence f source) : ∃ ρ, Law a b p ρ := by
  have hv0 : 0 < divergence f source := lt_of_lt_of_le zero_lt_one hv
  refine ⟨fun x y => f (left x) (right y)/divergence f source, ?_,?_,?_,?_,?_⟩
  · intro x y
    exact div_nonneg (Lax342547.BipartiteFlows.forward_flow_nonneg a b p f hf x y) hv0.le
  · change (∑ x, ∑ y, f (left x) (right y)/divergence f source) = 1
    simp_rw [← Finset.sum_div]
    rw [← Lax342547.BipartiteFlows.source_flow_total a b p f hf]
    exact div_self hv0.ne'
  · intro x
    rw [← Finset.sum_div,Lax342547.BipartiteFlows.left_conservation a b p f hf]
    apply (div_le_iff₀ hv0).mpr
    have h := hf.2.1 source (left x)
    change f source (left x) ≤ a x at h
    nlinarith [mul_nonneg (ha x) (sub_nonneg.mpr hv)]
  · intro y
    rw [← Finset.sum_div,Lax342547.BipartiteFlows.right_conservation a b p f hf]
    apply (div_le_iff₀ hv0).mpr
    have h := hf.2.1 (right y) sink
    change f (right y) sink ≤ b y at h
    nlinarith [mul_nonneg (hb y) (sub_nonneg.mpr hv)]
  · intro x y
    apply (div_le_iff₀ hv0).mpr
    have h := hf.2.1 (left x) (right y)
    change f (left x) (right y) ≤ p x y at h
    nlinarith [mul_nonneg (hp x y) (sub_nonneg.mpr hv)]

/--
---
conclusion: Lax342547.BipartiteFlows.infeasible_cut
---
-/
theorem infeasible_cut {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y)
    (hn : ¬ ∃ ρ, Law a b p ρ) :
    ∃ Z : Finset (Vertex A B), source ∈ Z ∧ sink ∉ Z ∧
      Lax342547.FlowCuts.cutCapacity (capacity a b p) Z < 1 := by
  obtain ⟨f,Z,hf,hs,ht,hval,_⟩ := Lax342547.FlowCuts.real_max_flow_min_cut
    (capacity a b p) source sink (by simp [source,sink]) (Lax342547.BipartiteFlows.capacity_nonneg a b p ha hb hp)
  refine ⟨Z,hs,ht,?_⟩
  rw [← hval]
  by_contra h
  exact hn (Lax342547.BipartiteFlows.normalized_flow_law a b p f hf ha hb hp (not_lt.mp h))

end Lax342547Proofs.BipartiteFlows
