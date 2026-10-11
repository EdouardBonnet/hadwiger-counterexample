import Lax342547.LeafBlockCaps

/-!
---
title: Exact-pin leaf entropy is invariant under nominal axis reindexing
type: lemma
---
Pull back exact pins along a finite axis equivalence. Relative ranks and specified image events agree exactly, so the original all-rank leaf cap applies to the opposite cross orientation.
-/

namespace Lax342547.PinReindexing

open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

noncomputable def pull {Axis Axis' I N : Type} (e : Axis' ≃ Axis) (P : Pin Axis I N) : Pin Axis' I N :=
  ⟨fun a => P.space (e a), fun a => P.value (e a)⟩

axiom relative_rank_reindex {Axis Axis' I N : Type} [Fintype Axis] [Fintype Axis'] [Fintype I]
    (e : Axis' ≃ Axis) (P : Pin Axis I N) (Q : Pin Axis' I N) :
    (pull e P).relativeRank Q = P.relativeRank (pull e.symm Q)

axiom event_reindex {Ω Axis Axis' I N : Type}
    (e : Axis' ≃ Axis) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (Q : Pin Axis' I N) :
    Q.event (fun ω a => A ω (e a)) = (pull e.symm Q).event A

axiom leaf_cap_reindex {Ω Axis Axis' I N : Type} [Fintype Axis] [Fintype Axis'] [Fintype I]
    (e : Axis' ≃ Axis) (p : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (α : ℝ≥0∞)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q))
    (Q : Pin Axis' I N) (hr : 1 ≤ (pull e P).relativeRank Q) :
    p.toOuterMeasure (Q.event (fun ω a => A ω (e a))) ≤ α ^ ((pull e P).relativeRank Q)

noncomputable def opposite {Comp : Type} : (Comp × Bool) ≃ (Comp × Bool) where
  toFun a := (a.1,!a.2)
  invFun a := (a.1,!a.2)
  left_inv a := by simp
  right_inv a := by simp

end Lax342547.PinReindexing
