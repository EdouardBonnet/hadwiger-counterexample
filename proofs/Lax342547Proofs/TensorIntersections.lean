import Lax342547.TensorIntersections
import Lax342547Proofs.RawFrames

namespace Lax342547Proofs.TensorIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ConcreteGeometry
open Lax342547.TensorIntersections

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

omit [Fintype H] [Fintype N] in
theorem rank_mul_injective {J : Type} [Fintype J] (P : Matrix N B Binary)
    (hP : Function.Injective P.mulVec) (w : Matrix B J Binary) : (P * w).rank = w.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective P.mulVecLin hP (LinearMap.range w.mulVecLin)).finrank_eq.symm

/--
---
conclusion: Lax342547.TensorIntersections.sandwich_rank
---
An injective linear map identifies every subspace with its image, so
left multiplication preserves column rank. Transposition gives the
corresponding assertion for right multiplication by the dual frame.
-/
theorem sandwich_rank {E : Matrix B B Binary} (F : Frame B H N E)
    (w : Matrix B B Binary) : (sandwich F.P F.Q w).rank = w.rank := by
  change (F.P * w * F.Q.transpose).rank = w.rank
  rw [← Matrix.rank_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    rank_mul_injective F.Q (RawFrames.dual_injective F), Matrix.rank_transpose,
    rank_mul_injective F.P (RawFrames.primal_injective F)]

theorem range_sandwich_le {E : Matrix B B Binary} (F : Frame B H N E)
    (w : Matrix B B Binary) :
    LinearMap.range (sandwich F.P F.Q w).mulVecLin ≤ LinearMap.range F.P.mulVecLin := by
  change LinearMap.range (F.P * w * F.Q.transpose).mulVecLin ≤ _
  rw [Matrix.mul_assoc, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/--
---
conclusion: Lax342547.TensorIntersections.shared_rank
---
Both tensor descriptions have the same rank, and the shared tensor's
column space is contained in both endpoint spans.
-/
theorem shared_rank {E : Matrix B B Binary} (F G : Frame B H N E)
    (w v : Matrix B B Binary) (h : sandwich F.P F.Q w = sandwich G.P G.Q v) :
    w.rank = v.rank ∧ w.rank ≤ Module.finrank Binary (intersectionSpace F.P G.P) := by
  constructor
  · rw [← sandwich_rank F w, h, sandwich_rank G v]
  · rw [← sandwich_rank F w]
    apply Submodule.finrank_mono
    refine le_inf (range_sandwich_le F w) ?_
    rw [h]
    exact range_sandwich_le G v

/--
---
conclusion: Lax342547.TensorIntersections.shared_total_rank
---
Apply the shared-tensor rank bound independently in every component
and add the resulting nonnegative integer inequalities.
-/
theorem shared_total_rank {Comp : Type} [Fintype Comp] {E : Matrix B B Binary}
    (F G : Comp → Frame B H N E) (w v : Comp → Matrix B B Binary)
    (h : profileMap F w = profileMap G v) :
    (∑ e, (w e).rank) = ∑ e, (v e).rank ∧
      (∑ e, (w e).rank) ≤ ∑ e, Module.finrank Binary (intersectionSpace (F e).P (G e).P) := by
  have he (e : Comp) := shared_rank (F e) (G e) (w e) (v e) (congrFun h e)
  exact ⟨Finset.sum_congr rfl (fun e _ => (he e).1),
    Finset.sum_le_sum (fun e _ => (he e).2)⟩

/--
---
conclusion: Lax342547.TensorIntersections.trace_sandwich
---
Cyclic trace moves the two frame maps together. Their product is the
transpose of the prescribed self-Gram matrix, giving its entrywise
pairing with the coefficient matrix.
-/
theorem trace_sandwich {E : Matrix B B Binary} (F : Frame B H N E)
    (w : Matrix B B Binary) : Matrix.trace (sandwich F.P F.Q w) = matrixPair E w := by
  have hg : F.Q.transpose * F.P = E.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose F.gram
  change Matrix.trace (F.P * w * F.Q.transpose) = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hg]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    matrixPair, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    matrixEntry, LinearMap.coe_mk]
  exact Finset.sum_comm

end Lax342547Proofs.TensorIntersections
