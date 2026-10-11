import Lax342547.InjectiveFrames
import Lax342547.FiniteLinearLaw
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Exact images mixing independent injective frames
type: lemma
---
Nominal directions are measured in the direct sum of all source frames.
Before conditioning, every independent tuple has an exactly uniform
ambient image. Conditioning each source frame to be injective costs at
most two per frame, uniformly over every possible tuple rank.
-/

namespace Lax342547.ProductImages

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames
open scoped ENNReal

def jointMatrix {Draw I N : Type} (A : Draw → Matrix N I Binary) : Matrix N (Draw × I) Binary :=
  fun n j => A j.1 n j.2

def jointEquiv {Draw I N : Type} : (Draw → Matrix N I Binary) ≃ Matrix N (Draw × I) Binary where
  toFun := jointMatrix
  invFun M i n j := M n (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

def rightMap {I T N : Type} [Fintype I] (C : Matrix I T Binary) :
    Matrix N I Binary →ₗ[Binary] Matrix N T Binary where
  toFun A := A * C
  map_add' A B := Matrix.add_mul A B C
  map_smul' c A := Matrix.smul_mul c A C

axiom rank_restriction {I T : Type} [Fintype I] [Fintype T]
    (C : Matrix I T Binary) :
    ∃ D : Matrix T (Fin C.rank) Binary, Function.Injective (C * D).mulVec

axiom right_uniform {I T N : Type} [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq I] [DecidableEq T] [DecidableEq N]
    (C : Matrix I T Binary) (hC : Function.Injective C.mulVec) :
    (PMF.uniformOfFintype (Matrix N I Binary)).map (fun A => A * C) =
      PMF.uniformOfFintype (Matrix N T Binary)

axiom joint_uniform {Draw I T N : Type} [Fintype Draw] [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq I] [DecidableEq T] [DecidableEq N]
    (C : Matrix (Draw × I) T Binary) (hC : Function.Injective C.mulVec) :
    (PMF.uniformOfFintype (Draw → Matrix N I Binary)).map (fun A => jointMatrix A * C) =
      PMF.uniformOfFintype (Matrix N T Binary)

axiom injective_image_bound {Draw I T N : Type}
    [Fintype Draw] [Fintype I] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq I] [DecidableEq T] [DecidableEq N]
    [Nonempty (Injection I N)] (hN : Fintype.card I + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × I) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (Draw → Injection I N)).map
      (fun A => jointMatrix (fun i => (A i).val) * C) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T)

axiom raw_plus_image_bound {Draw B H T N : Type}
    [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq T] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : Fintype.card B + Fintype.card H + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec)
    (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o => jointMatrix (fun i => (plus (o i)).val) * C) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T)

end Lax342547.ProductImages
