import Lax342547.ReferencePins
import Lax342547Proofs.ExactPins
import Lax342547Proofs.ImageScale

namespace Lax342547Proofs.ReferencePins

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.ProductImages Lax342547.ReferenceImages Lax342547.ExactPins
open Lax342547.ReferencePins
open scoped ENNReal

/--
---
conclusion: Lax342547.ReferencePins.reference_pin_cap
---
Use a basis of each component/sign pin space and its stored exact images.
These coefficient matrices have precisely the pin dimensions as their
nominal ranks. The all-rank image theorem applies to the same event.
-/
theorem reference_pin_cap {Comp B H N : Type}
    [Fintype B] [Fintype H] [Fintype N] [Fintype Comp]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure (P.event observation) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * Fintype.card N)) := by
  let p := PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)
  by_cases hzero : P.rank = 0
  · simp only [hzero, Nat.cast_zero, mul_zero, zero_mul, neg_zero, ENNReal.rpow_zero]
    exact p.toOuterMeasure.mono (Set.subset_univ _) |>.trans_eq
      ((p.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _))
  · have hrank : P.rank = (∑ e : Comp, (P.basisMatrix (e, true)).rank) +
        ∑ e : Comp, (P.basisMatrix (e, false)).rank := by
      simp only [ExactPins.basis_rank, Pin.rank, Fintype.sum_prod_type, Fintype.sum_bool,
        Finset.sum_add_distrib]
    have h := ImageScale.reference_image_cap (E := E) ε hε hN hp hc
      (fun e => P.basisMatrix (e, true)) (fun e => P.basisMatrix (e, false))
      (fun e => P.basisImage (e, true)) (fun e => P.basisImage (e, false))
      (by rw [← hrank]; omega)
    rw [← hrank] at h
    have he : P.event (observation (E := E)) =
        {o | ∀ e, plusImages (P.basisMatrix (e, true)) (fun i => o i e) = P.basisImage (e, true) ∧
          minusImages (P.basisMatrix (e, false)) (fun i => o i e) = P.basisImage (e, false)} := by
      rw [show P.event (observation (E := E)) =
        P.event (fun o a => (observationMatrix (E := E) o a).mulVecLin) from rfl,
        ExactPins.event_basis]
      ext o
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro ho e
        exact ⟨ho (e, true), ho (e, false)⟩
      · intro ho a
        rcases a with ⟨e, b⟩
        cases b
        · exact (ho e).2
        · exact (ho e).1
    rwa [he]

end Lax342547Proofs.ReferencePins
