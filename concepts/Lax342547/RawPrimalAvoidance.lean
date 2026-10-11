import Lax342547.InjectiveDensity
import Lax342547.PrimalAvoidance
import Lax342547.InjectiveFrames
import Lax342547.ChannelColumns
import Lax342547.PhaseAverages

/-!
---
title: Actual raw primal-span avoidance
type: lemma
---
Uniform raw frames inherit a complete primal-span intersection bound from their combined injective plus matrix.
-/

namespace Lax342547.RawPrimalAvoidance

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.RealCellLaws Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped BigOperators

axiom plus_matrix_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq B] [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (Z : Matrix N (B ⊕ H) Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => (plus F).val) Z ≤
      2*weights (PMF.uniformOfFintype (Matrix N (B ⊕ H) Binary)) Z

axiom raw_primal_span_hit_mass {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq B] [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Frame B H N E)))
      (fun F => ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W) ≤
      2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N)

end Lax342547.RawPrimalAvoidance
