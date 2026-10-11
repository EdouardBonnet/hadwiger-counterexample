import Lax342547.ResidualFlows
import Mathlib.Logic.Relation

namespace Lax342547Proofs.ResidualFlows
open Lax342547.ResidualFlows

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealFlows
open scoped BigOperators Topology
open Filter

/--
---
conclusion: Lax342547.ResidualFlows.edge_direction
---
-/
theorem edge_direction {V : Type} [Fintype V] (c f : V → V → ℝ) (u v : V)
    (huv : Residual c f u v) : Direction c f (edgeDirection u v) u v := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro a b
    simp only [edgeDirection, and_comm]
    ring
  · intro a
    simp [divergence, edgeDirection, Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel]
  · intro a b hab
    by_cases h : a=u ∧ b=v
    · rcases h with ⟨rfl,rfl⟩
      exact False.elim (hab huv)
    · simp only [edgeDirection, h, if_false, zero_sub]
      split_ifs <;> norm_num

/--
---
conclusion: Lax342547.ResidualFlows.residual_walk_direction
---
-/
theorem residual_walk_direction {V : Type} [Fintype V] (c f : V → V → ℝ) (u v : V)
    (hpath : Relation.ReflTransGen (Residual c f) u v) :
    ∃ d, Direction c f d u v := by
  classical
  induction hpath with
  | refl =>
      refine ⟨fun _ _ => 0, fun _ _ => by simp, ?_, fun _ _ _ => le_rfl⟩
      intro a
      simp [divergence]
  | @tail b v hpath hbv ih =>
      obtain ⟨d,hskew,hdiv,hsupport⟩ := ih
      obtain ⟨heskew,hediv,hesupport⟩ := Lax342547.ResidualFlows.edge_direction c f b v hbv
      refine ⟨fun a b' => d a b'+edgeDirection b v a b', ?_,?_,?_⟩
      · intro a b'
        change d a b'+edgeDirection b v a b' = -(d b' a+edgeDirection b v b' a)
        rw [hskew a b',heskew a b']
        ring
      · intro a
        simp only [divergence, Finset.sum_add_distrib]
        change divergence d a + divergence (edgeDirection b v) a = _
        rw [hdiv,hediv]
        ring
      · intro a b' hn
        exact add_nonpos (hsupport a b' hn) (hesupport a b' hn)

/--
---
conclusion: Lax342547.ResidualFlows.feasible_augmentation
---
-/
theorem feasible_augmentation {V : Type} [Fintype V]
    (c f d : V → V → ℝ) (s t : V) (hfeasible : Feasible c f s t)
    (hdir : Direction c f d s t) :
    ∃ δ : ℝ, 0 < δ ∧ Feasible c (fun a b => f a b+δ*d a b) s t := by
  have heach (a b : V) : ∀ᶠ δ : ℝ in 𝓝[>] 0, f a b+δ*d a b ≤ c a b := by
    by_cases hstrict : f a b < c a b
    · have hc : ContinuousAt (fun δ : ℝ => f a b+δ*d a b) 0 := by fun_prop
      have hv : (fun δ : ℝ => f a b+δ*d a b) 0 < c a b := by simpa using hstrict
      have h := hc.eventually (gt_mem_nhds hv)
      exact (h.filter_mono nhdsWithin_le_nhds).mono (fun δ hd => hd.le)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ0 : 0 < δ := hδ
      have hnonpos := hdir.2.2 a b hstrict
      exact le_trans (by nlinarith : f a b+δ*d a b ≤ f a b) (hfeasible.2.1 a b)
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ a b, f a b+δ*d a b ≤ c a b :=
    eventually_all.mpr (fun a => eventually_all.mpr (fun b => heach a b))
  obtain ⟨δ,hcap,hδ⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨δ,hδ,?_,hcap,?_⟩
  · intro a b
    change f a b+δ*d a b = -(f b a+δ*d b a)
    rw [hfeasible.1 a b,hdir.1 a b]
    ring
  · intro a has hat
    simp only [divergence, Finset.sum_add_distrib, ← Finset.mul_sum]
    change divergence f a+δ*divergence d a = 0
    rw [hfeasible.2.2 a has hat,hdir.2.1 a]
    simp [has,hat]

/--
---
conclusion: Lax342547.ResidualFlows.maximal_no_residual_path
---
-/
theorem maximal_no_residual_path {V : Type} [Fintype V]
    (c f : V → V → ℝ) (s t : V) (hst : s ≠ t) (hf : Feasible c f s t)
    (hmax : ∀ g, Feasible c g s t → divergence g s ≤ divergence f s) :
    ¬ Relation.ReflTransGen (Residual c f) s t := by
  classical
  intro hpath
  obtain ⟨d,hdir⟩ := Lax342547.ResidualFlows.residual_walk_direction c f s t hpath
  obtain ⟨δ,hδ,hg⟩ := Lax342547.ResidualFlows.feasible_augmentation c f d s t hf hdir
  have hm := hmax _ hg
  simp only [divergence, Finset.sum_add_distrib, ← Finset.mul_sum] at hm
  change divergence f s+δ*divergence d s ≤ divergence f s at hm
  rw [hdir.2.1 s] at hm
  simp [hst] at hm
  linarith

end Lax342547Proofs.ResidualFlows
