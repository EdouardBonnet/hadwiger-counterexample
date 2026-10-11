import Lax342547.UnitSpanAvoidance
import Lax342547.FiniteLinearLaw

/-!
---
title: Reciprocal raw-frame orientation and dual pin avoidance
type: lemma
---
Swapping primal and dual frame data is an exact transpose equivalence, preserves uniform density caps, and supplies the reciprocal conditioned primal-span avoidance bound.
-/

namespace Lax342547.FrameTranspose

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.RealCellLaws
open Lax342547.PushforwardWalsh Lax342547.RetainedImages
open scoped BigOperators

def transposeFrame {P H N : Type} [Fintype P] [Fintype H] [Fintype N]
    {E : Matrix P P Binary} (f : Frame P H N E) : Frame P H N E.transpose where
  P := f.Q
  Q := f.P
  X := f.Y
  Y := f.X
  plus_injective := f.minus_injective
  minus_injective := f.plus_injective
  gram := by simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose f.gram
  plus_annihilator := by simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      (congrArg Matrix.transpose f.minus_annihilator)
  minus_annihilator := by simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using
      (congrArg Matrix.transpose f.plus_annihilator)

def transposeEquiv {P H N : Type} [Fintype P] [Fintype H] [Fintype N] (E : Matrix P P Binary) :
    Frame P H N E ≃ Frame P H N E.transpose where
  toFun := transposeFrame
  invFun := transposeFrame
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

axiom uniform_equiv_push {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (b : B) :
    push (weights (PMF.uniformOfFintype A)) e b = weights (PMF.uniformOfFintype B) b

axiom capped_transpose_frame {A P H N : Type} [Fintype A] [Fintype P] [Fintype H] [Fintype N]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (image : A → Frame P H N E) (M : ℝ)
    (hcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    letI : Nonempty (Frame P H N E.transpose) := ⟨transposeFrame (Classical.choice inferInstance)⟩
    ∀ f,push α (fun a => transposeFrame (image a)) f ≤
      M*weights (PMF.uniformOfFintype (Frame P H N E.transpose)) f

axiom conditioned_dual_span_avoidance {A P H N : Type}
    [Fintype A] [Fintype P] [Fintype H] [Fintype N] [DecidableEq P] [DecidableEq H] [DecidableEq N]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (image : A → Frame P H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (C : A → Prop) (M τ : ℝ)
    (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M) (hτ : 0 < τ) (hC : τ ≤ cellMass α C)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).Q.mulVecLin)
    (hcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    cellMass (Lax342547.RetainedImages.conditionalLaw α C) (fun a => ¬ Disjoint (V a) W) ≤
      (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N))

end Lax342547.FrameTranspose
