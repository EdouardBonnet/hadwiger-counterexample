import Lax342547.PinReindexing
import Lax342547Proofs.LeafBlockCaps

namespace Lax342547Proofs.PinReindexing
open Lax342547.PinReindexing

set_option backward.isDefEq.respectTransparency true
open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

/--
---
conclusion: Lax342547.PinReindexing.relative_rank_reindex
---
-/
theorem relative_rank_reindex {Axis Axis' I N : Type} [Fintype Axis] [Fintype Axis'] [Fintype I]
    (e : Axis' ≃ Axis) (P : Pin Axis I N) (Q : Pin Axis' I N) :
    (pull e P).relativeRank Q = P.relativeRank (pull e.symm Q) := by
  classical
  unfold Pin.relativeRank
  change (∑ a, Module.finrank Binary ((Q.space a).map (P.space (e a)).mkQ)) =
    ∑ b, Module.finrank Binary ((Q.space (e.symm b)).map (P.space b).mkQ)
  have h := Equiv.sum_comp e (fun b => Module.finrank Binary ((Q.space (e.symm b)).map (P.space b).mkQ))
  have hc (a : Axis') : Module.finrank Binary ((Q.space (e.symm (e a))).map (P.space (e a)).mkQ) =
      Module.finrank Binary ((Q.space a).map (P.space (e a)).mkQ) :=
    congrArg (fun z => Module.finrank Binary ((Q.space z).map (P.space (e a)).mkQ)) (e.symm_apply_apply a)
  exact (Finset.sum_congr rfl (fun a _ => (hc a).symm)).trans h

/--
---
conclusion: Lax342547.PinReindexing.event_reindex
---
-/
theorem event_reindex {Ω Axis Axis' I N : Type}
    (e : Axis' ≃ Axis) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (Q : Pin Axis' I N) :
    Q.event (fun ω a => A ω (e a)) = (pull e.symm Q).event A := by
  ext ω
  change (∀ a (v : Q.space a), A ω (e a) v.val = Q.value a v) ↔
    ∀ b (v : Q.space (e.symm b)), A ω b v.val = Q.value (e.symm b) v
  constructor
  · intro h b v
    simpa only [e.apply_symm_apply] using h (e.symm b) v
  · intro h a
    have hv := h (e a)
    exact Eq.mp (congrArg (fun z => ∀ v : Q.space z, A ω (e a) v.val = Q.value z v)
      (e.symm_apply_apply a)) hv

/--
---
conclusion: Lax342547.PinReindexing.leaf_cap_reindex
---
-/
theorem leaf_cap_reindex {Ω Axis Axis' I N : Type} [Fintype Axis] [Fintype Axis'] [Fintype I]
    (e : Axis' ≃ Axis) (p : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (α : ℝ≥0∞)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q))
    (Q : Pin Axis' I N) (hr : 1 ≤ (pull e P).relativeRank Q) :
    p.toOuterMeasure (Q.event (fun ω a => A ω (e a))) ≤ α ^ ((pull e P).relativeRank Q) := by
  rw [event_reindex, relative_rank_reindex]
  apply hcap
  rwa [relative_rank_reindex] at hr

end Lax342547Proofs.PinReindexing
