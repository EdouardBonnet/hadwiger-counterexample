import Lax342547.RawLaw
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
---
title: Ambient symmetries and frame marginals
type: definition and theorem
---
The simultaneous primal and inverse-transpose action preserves all three
raw Gram constraints. Its bijections of completion sets determine the
uniform plus-frame and channel marginals exactly.
-/

namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

structure Change (N : Type) [Fintype N] [DecidableEq N] where
  C : Matrix N N Binary
  D : Matrix N N Binary
  CD : C * D = 1
  DC : D * C = 1

def Change.inv (c : Change N) : Change N := ⟨c.D, c.C, c.DC, c.CD⟩

def Change.dual (c : Change N) : Change N where
  C := c.D.transpose
  D := c.C.transpose
  CD := by simpa using congrArg Matrix.transpose c.CD
  DC := by simpa using congrArg Matrix.transpose c.DC

theorem Change.injective (c : Change N) : Function.Injective c.C.mulVec := by
  intro x y h
  have h' := congrArg c.D.mulVec h
  simpa only [Matrix.mulVec_mulVec, c.DC, Matrix.one_mulVec] using h'

theorem Change.dual_injective (c : Change N) : Function.Injective c.D.transpose.mulVec := by
  have hDC : c.C.transpose * c.D.transpose = 1 := by
    simpa using congrArg Matrix.transpose c.DC
  intro x y h
  have h' := congrArg c.C.transpose.mulVec h
  simpa only [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec] using h'

def transform (c : Change N) {E : Matrix B B Binary} (F : Frame B H N E) :
    Frame B H N E where
  P := c.C * F.P
  Q := c.D.transpose * F.Q
  X := c.C * F.X
  Y := c.D.transpose * F.Y
  plus_injective := by
    intro x y h
    apply F.plus_injective
    apply c.injective
    simpa only [Matrix.mulVec_add, Matrix.mulVec_mulVec] using h
  minus_injective := by
    intro x y h
    apply F.minus_injective
    apply c.dual_injective
    simpa only [Matrix.mulVec_add, Matrix.mulVec_mulVec] using h
  gram := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.gram
  plus_annihilator := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.plus_annihilator
  minus_annihilator := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.minus_annihilator

def frameEquiv (c : Change N) {E : Matrix B B Binary} : Frame B H N E ≃ Frame B H N E where
  toFun := transform c
  invFun := transform c.inv
  left_inv F := by
    apply frameData_injective
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simp [frameData, transform, Change.inv, ← Matrix.mul_assoc, c.DC, hCD]
  right_inv F := by
    apply frameData_injective
    have hDC : c.D.transpose * c.C.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.CD
    simp [frameData, transform, Change.inv, ← Matrix.mul_assoc, c.CD, hDC]

abbrev Injection (I N : Type) [Fintype I] :=
  {A : Matrix N I Binary // Function.Injective A.mulVec}

noncomputable instance {I N : Type} [Fintype I] [Fintype N] :
    Fintype (Injection I N) := by classical exact Subtype.fintype _

def plus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.P F.X, by
    intro x y h
    have h' := F.plus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def minus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.Q F.Y, by
    intro x y h
    have h' := F.minus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def plusChannel {E : Matrix B B Binary} (F : Frame B H N E) : Injection H N :=
  ⟨F.X, by
    intro x y h
    have he := F.plus_injective (a₁ := (0, x)) (a₂ := (0, y)) (by simpa using h)
    exact congrArg Prod.snd he⟩

def minusChannel {E : Matrix B B Binary} (F : Frame B H N E) : Injection H N :=
  ⟨F.Y, by
    intro x y h
    have he := F.minus_injective (a₁ := (0, x)) (a₂ := (0, y)) (by simpa using h)
    exact congrArg Prod.snd he⟩

axiom plus_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection (B ⊕ H) N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map plus =
      PMF.uniformOfFintype (Injection (B ⊕ H) N)

axiom minus_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection (B ⊕ H) N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map minus =
      PMF.uniformOfFintype (Injection (B ⊕ H) N)

axiom plusChannel_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection H N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map plusChannel =
      PMF.uniformOfFintype (Injection H N)

axiom minusChannel_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection H N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map minusChannel =
      PMF.uniformOfFintype (Injection H N)

axiom full_frame_orbit {E : Matrix B B Binary} (F G : Frame B H N E)
    (hchannel : F.X.transpose * F.Y = G.X.transpose * G.Y) :
    ∃ c : Change N, transform c F = G

end Lax342547.FrameSymmetry
