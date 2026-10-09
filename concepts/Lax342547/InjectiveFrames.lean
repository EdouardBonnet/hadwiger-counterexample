import Lax342547.FrameSymmetry
import Lax342547.GramNormalization

/-!
---
title: Uniform injective frames and channel transpose failure
type: theorem
---
Injectivity of an h-column frame has probability at least one half when
N≥h+1, so conditioning costs at most a factor of two on every event.
The transpose evaluation on any prescribed independent q-tuple is
therefore noninjective with probability at most 2^(q+1-h), as in (4.2).
-/

namespace Lax342547.InjectiveFrames

open Lax342547.MomentSpace Lax342547.FrameSymmetry
open scoped ENNReal

axiom injective_mass_half {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (1 / 2 : ℝ≥0∞) ≤ (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure
      {A | Function.Injective A.mulVec}

axiom injection_event_bound {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (hN : Fintype.card H + 1 ≤ Fintype.card N) (S : Set (Matrix N H Binary)) :
    (PMF.uniformOfFintype (Injection H N)).toOuterMeasure {A | A.val ∈ S} ≤
      2 * (PMF.uniformOfFintype (Matrix N H Binary)).toOuterMeasure S

axiom transpose_uniform {I H N : Type} [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec) :
    (PMF.uniformOfFintype (Matrix N H Binary)).map (fun X => X.transpose * D) =
      PMF.uniformOfFintype (Matrix H I Binary)

axiom transpose_failure {I H N : Type} [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (PMF.uniformOfFintype (Injection H N)).toOuterMeasure
      {X | ¬ Function.Injective (X.val.transpose * D).mulVec} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H

axiom raw_transpose_failures {B I H N : Type}
    [Fintype B] [Fintype I] [Fintype H] [Fintype N]
    [DecidableEq I] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (RawFrames.Frame B H N E)]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (hN : Fintype.card H + 1 ≤ Fintype.card N) :
    (PMF.uniformOfFintype (RawFrames.Frame B H N E)).toOuterMeasure
        {F | ¬ Function.Injective (F.X.transpose * D).mulVec} ≤
        (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H ∧
    (PMF.uniformOfFintype (RawFrames.Frame B H N E)).toOuterMeasure
        {F | ¬ Function.Injective (F.Y.transpose * D).mulVec} ≤
        (2 : ℝ≥0∞) ^ (Fintype.card I + 1) / 2 ^ Fintype.card H

end Lax342547.InjectiveFrames
