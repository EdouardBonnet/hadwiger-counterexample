import Lax342547.ConditionalChannels
import Lax342547Proofs.FiniteUniform
import Lax342547.GramColumns

namespace Lax342547Proofs.ConditionalChannels

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ConditionalChannels
open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

/--
---
conclusion: Lax342547.ConditionalChannels.conditional_uniform
---
The concrete completion equivalence identifies each fixed-P,Q fiber with
the Cartesian product of its independently constrained X and Y matrices.
Transporting the uniform law along this bijection gives the product law.
-/
theorem conditional_uniform {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)] :
    (PMF.uniformOfFintype (Fiber (H := H) E P Q)).map channels =
      PMF.uniformOfFintype (PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q) :=
  FiniteUniform.map_equiv (channelEquiv hgram)

/--
---
conclusion: Lax342547.ConditionalChannels.conditional_point
---
The conditional joint mass is the product of the two separate uniform
completion masses, with no unspecified normalization constant.
-/
theorem conditional_point {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)]
    (X : PlusCompletion (H := H) P Q) (Y : MinusCompletion (H := H) P Q) :
    (PMF.uniformOfFintype (Fiber (H := H) E P Q)).map channels (X, Y) =
      PMF.uniformOfFintype (PlusCompletion (H := H) P Q) X *
        PMF.uniformOfFintype (MinusCompletion (H := H) P Q) Y := by
  rw [Lax342547.ConditionalChannels.conditional_uniform hgram]
  simp [PMF.uniformOfFintype_apply, ENNReal.mul_inv]

/--
---
conclusion: Lax342547.ConditionalChannels.raw_conditioning
---
Filtering and renormalizing the actual uniform raw-frame law at fixed
P,Q is uniform on that fiber. Its channel images therefore have exactly
the product completion law proved above.
-/
theorem raw_conditioning {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Frame B H N E)]
    [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)]
    (h : ∃ F ∈ {F : Frame B H N E | F.P = P ∧ F.Q = Q},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.P = P ∧ F.Q = Q} h).map
      (fun F => (F.X, F.Y)) =
    (PMF.uniformOfFintype (PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q)).map
      (fun z => (z.1.val, z.2.val)) := by
  classical
  let : Nonempty {F : Frame B H N E | F.P = P ∧ F.Q = Q} := by
    obtain ⟨F, hF, _⟩ := h
    exact ⟨⟨F, hF⟩⟩
  rw [FiniteUniform.filter_uniform (α := Frame B H N E) {F | F.P = P ∧ F.Q = Q} h]
  rw [← Lax342547.ConditionalChannels.conditional_uniform hgram, PMF.map_comp, PMF.map_comp]
  rfl

/--
---
conclusion: Lax342547.ConditionalChannels.channel_rank_failures
---
The zero-Gram fibers are precisely the independent uniform columns in
the two annihilators. Their failure to extend P and Q injectively is
bounded by 2^(2d+h-N) on each side, before the separate rank conditionings.
-/
theorem channel_rank_failures [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (P Q : Matrix N B Binary) (hP : Function.Injective P.mulVec) (hQ : Function.Injective Q.mulVec)
    [Nonempty (Lax342547.GramColumns.GramFiber Q (0 : Matrix B H Binary))]
    [Nonempty (Lax342547.GramColumns.GramFiber P (0 : Matrix B H Binary))] :
    (PMF.uniformOfFintype (Lax342547.GramColumns.GramFiber Q (0 : Matrix B H Binary))).toOuterMeasure
        {X | ¬ Function.Injective (fun z : (B → Binary) × (H → Binary) =>
          P.mulVec z.1 + X.val.mulVec z.2)} ≤
        (2 : ℝ≥0∞) ^ (2 * Fintype.card B + Fintype.card H) / 2 ^ Fintype.card N ∧
    (PMF.uniformOfFintype (Lax342547.GramColumns.GramFiber P (0 : Matrix B H Binary))).toOuterMeasure
        {Y | ¬ Function.Injective (fun z : (B → Binary) × (H → Binary) =>
          Q.mulVec z.1 + Y.val.mulVec z.2)} ≤
        (2 : ℝ≥0∞) ^ (2 * Fintype.card B + Fintype.card H) / 2 ^ Fintype.card N := by
  constructor
  · simpa only [two_mul] using Lax342547.GramColumns.extension_failure P hP Q hQ (0 : Matrix B H Binary)
  · simpa only [two_mul] using Lax342547.GramColumns.extension_failure Q hQ P hP (0 : Matrix B H Binary)

end Lax342547Proofs.ConditionalChannels
