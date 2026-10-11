import Lax342547.InjectiveFrames
import Lax342547.ChannelColumns

/-!
---
title: Uniform injective-matrix density
type: definition and theorem
---
Exact raw endpoint channel marginals have density at most two over uniform full matrices.
-/

namespace Lax342547.InjectiveDensity

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped ENNReal

axiom injective_matrix_point_cap {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Injection H N))) Subtype.val Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y

axiom raw_minus_channel_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => F.Y) Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y

axiom raw_plus_channel_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => F.X) Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y

end Lax342547.InjectiveDensity
