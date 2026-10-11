import Lax342547.RealFlows
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Convex.Function

namespace Lax342547Proofs.RealFlows
open Lax342547.RealFlows

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology

/--
---
conclusion: Lax342547.RealFlows.zero_feasible
---
-/
theorem zero_feasible {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hc : ∀ a b, 0 ≤ c a b) : Feasible c (fun _ _ => 0) s t := by
  exact ⟨fun _ _ => by simp, hc, fun _ _ _ => by simp [divergence]⟩

/--
---
conclusion: Lax342547.RealFlows.feasible_closed
---
-/
theorem feasible_closed {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V) :
    IsClosed {f | Feasible c f s t} := by
  unfold Feasible
  have hskew : IsClosed {f : V → V → ℝ | ∀ a b, f a b = -f b a} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro b
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hcap : IsClosed {f : V → V → ℝ | ∀ a b, f a b ≤ c a b} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro b
    exact isClosed_le ((continuous_apply b).comp (continuous_apply a)) continuous_const
  have hcons : IsClosed {f : V → V → ℝ | ∀ a, a ≠ s → a ≠ t → divergence f a = 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro _
    apply isClosed_iInter
    intro _
    apply isClosed_eq _ continuous_const
    unfold divergence
    exact continuous_finsetSum _ (fun b _ => (continuous_apply b).comp (continuous_apply a))
  exact hskew.inter (hcap.inter hcons)

/--
---
conclusion: Lax342547.RealFlows.feasible_compact
---
-/
theorem feasible_compact {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V) :
    IsCompact {f | Feasible c f s t} := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := fun a b => -c b a) (b := c))
    (feasible_closed c s t)
  intro f hf
  constructor
  · intro a b
    have h := hf.2.1 b a
    rw [hf.1 b a] at h
    linarith
  · exact hf.2.1

/--
---
conclusion: Lax342547.RealFlows.maximal_flow
---
-/
theorem maximal_flow {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hc : ∀ a b, 0 ≤ c a b) :
    ∃ f, Feasible c f s t ∧ ∀ g, Feasible c g s t → divergence g s ≤ divergence f s := by
  have hcont : Continuous (fun f : V → V → ℝ => divergence f s) := by
    unfold divergence
    exact continuous_finsetSum _ (fun b _ => (continuous_apply b).comp (continuous_apply s))
  obtain ⟨f,hf,hmax⟩ := (feasible_compact c s t).exists_isMaxOn
    ⟨fun _ _ => 0, zero_feasible c s t hc⟩ hcont.continuousOn
  exact ⟨f,hf,fun g hg => hmax hg⟩

end Lax342547Proofs.RealFlows
