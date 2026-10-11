import Lax342547.RawPrimalAvoidance
import Lax342547.RetainedImages
import Lax342547.FiniteSampling
import Lax342547.PhaseAverages
import Lax342547.ChannelColumns

/-!
---
title: Whole-unit conditioned pin avoidance
type: definition and theorem
---
Pins inside actual primal images inherit raw span avoidance, including the exact conditioning cost for any retained accepted set.
-/

namespace Lax342547.UnitSpanAvoidance

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RawFrames Lax342547.FrameSymmetry Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

axiom pin_intersection_is_primal_hit {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (F : Frame B H N E) (V W : Submodule Binary (N → Binary))
    (hV : V ≤ LinearMap.range F.P.mulVecLin) (hbad : ¬ Disjoint V W) :
    ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W

axiom capped_unit_span_avoidance {A B H N : Type}
    [Fintype A] [Fintype B] [Fintype H] [Fintype N] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (α : A → ℝ) (image : A → Frame B H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (M : ℝ) (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M)
    (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hcap : ∀ F,push α image F ≤ M*weights (PMF.uniformOfFintype (Frame B H N E)) F) :
    cellMass α (fun a => ¬ Disjoint (V a) W) ≤
      M*(2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N))

axiom conditioned_unit_span_avoidance {A B H N : Type}
    [Fintype A] [Fintype B] [Fintype H] [Fintype N] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (α : A → ℝ) (image : A → Frame B H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (C : A → Prop) (M τ : ℝ)
    (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M) (hτ : 0 < τ) (hC : τ ≤ cellMass α C)
    (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hcap : ∀ F,push α image F ≤ M*weights (PMF.uniformOfFintype (Frame B H N E)) F) :
    cellMass (conditionalLaw α C) (fun a => ¬ Disjoint (V a) W) ≤
      (M/τ)*(2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N))

end Lax342547.UnitSpanAvoidance
