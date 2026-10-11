import Lax342547.FlowCuts
import Lax342547Proofs.ResidualFlows

namespace Lax342547Proofs.FlowCuts
open Lax342547.FlowCuts

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealFlows
open scoped BigOperators

/--
---
conclusion: Lax342547.FlowCuts.cut_indicator
---
-/
theorem cut_indicator {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : by
    classical
    exact cutCapacity c Z = ∑ a, ∑ b, if a ∈ Z ∧ b ∉ Z then c a b else 0 := by
  classical
  unfold cutCapacity
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [← Finset.mem_compl,Finset.sum_ite_mem_eq]

/--
---
conclusion: Lax342547.FlowCuts.internal_skew_sum
---
-/
theorem internal_skew_sum {V : Type} (f : V → V → ℝ) (Z : Finset V)
    (hskew : ∀ a b, f a b = -f b a) : (∑ a ∈ Z, ∑ b ∈ Z, f a b) = 0 := by
  have he : (∑ a ∈ Z, ∑ b ∈ Z, f a b) = -(∑ a ∈ Z, ∑ b ∈ Z, f a b) := by
    conv_lhs => arg 2; intro a; arg 2; intro b; rw [hskew a b]
    simp only [Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  linarith

/--
---
conclusion: Lax342547.FlowCuts.divergence_cut_sum
---
-/
theorem divergence_cut_sum {V : Type} [Fintype V] (f : V → V → ℝ) (Z : Finset V)
    (hskew : ∀ a b, f a b = -f b a) : by
    classical
    exact (∑ a ∈ Z, divergence f a) = ∑ a ∈ Z, ∑ b ∈ Zᶜ, f a b := by
  classical
  have hr (a : V) : divergence f a = (∑ b ∈ Z, f a b)+(∑ b ∈ Zᶜ, f a b) :=
    (Finset.sum_add_sum_compl Z (fun b => f a b)).symm
  simp_rw [hr]
  rw [Finset.sum_add_distrib,internal_skew_sum f Z hskew,zero_add]

/--
---
conclusion: Lax342547.FlowCuts.conserving_cut_value
---
-/
theorem conserving_cut_value {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z) :
    (∑ a ∈ Z, divergence f a) = divergence f s := by
  classical
  rw [Finset.sum_eq_single s]
  · intro a ha has
    exact hf.2.2 a has (by intro hat; subst a; exact ht ha)
  · intro hn
    exact False.elim (hn hs)

/--
---
conclusion: Lax342547.FlowCuts.saturated_cut_value
---
-/
theorem saturated_cut_value {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z)
    (hsat : ∀ a ∈ Z, ∀ b ∉ Z, f a b = c a b) :
    divergence f s = cutCapacity c Z := by
  classical
  rw [← conserving_cut_value c f s t hf Z hs ht,divergence_cut_sum f Z hf.1]
  unfold cutCapacity
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact hsat a ha b (Finset.mem_compl.mp hb)

/--
---
conclusion: Lax342547.FlowCuts.cut_upper_bound
---
-/
theorem cut_upper_bound {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V)
    (hf : Feasible c f s t) (Z : Finset V) (hs : s ∈ Z) (ht : t ∉ Z) :
    divergence f s ≤ cutCapacity c Z := by
  classical
  rw [← conserving_cut_value c f s t hf Z hs ht,divergence_cut_sum f Z hf.1]
  unfold cutCapacity
  exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hf.2.1 a b))

/--
---
conclusion: Lax342547.FlowCuts.real_max_flow_min_cut
---
-/
theorem real_max_flow_min_cut {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hst : s ≠ t) (hc : ∀ a b, 0 ≤ c a b) :
    ∃ f Z, Feasible c f s t ∧ s ∈ Z ∧ t ∉ Z ∧ divergence f s = cutCapacity c Z ∧
      ∀ g, Feasible c g s t → divergence g s ≤ divergence f s := by
  classical
  obtain ⟨f,hf,hmax⟩ := Lax342547Proofs.RealFlows.maximal_flow c s t hc
  have hno := Lax342547Proofs.ResidualFlows.maximal_no_residual_path c f s t hst hf hmax
  let Z := Finset.univ.filter (fun a => Relation.ReflTransGen (Residual c f) s a)
  have hs : s ∈ Z := by simp [Z,Relation.ReflTransGen.refl]
  have ht : t ∉ Z := by simpa [Z] using hno
  refine ⟨f,Z,hf,hs,ht,?_,hmax⟩
  apply saturated_cut_value c f s t hf Z hs ht
  intro a ha b hb
  apply le_antisymm (hf.2.1 a b)
  apply le_of_not_gt
  intro hab
  have hreach : Relation.ReflTransGen (Residual c f) s a := (Finset.mem_filter.mp ha).2
  exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b,hreach.tail hab⟩)

end Lax342547Proofs.FlowCuts
