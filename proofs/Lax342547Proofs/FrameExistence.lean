import Lax342547.FrameExistence
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.FrameExistence

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H : Type} [Fintype B] [Fintype H]

noncomputable def canonicalFrame (E : Matrix B B Binary) :
    Frame B H ((B ⊕ H) ⊕ (B ⊕ H)) E := by
  classical
  refine {
    P := Matrix.fromRows (Matrix.fromRows 1 (0 : Matrix H B Binary)) 0
    Q := Matrix.fromRows (Matrix.fromRows E 0) (Matrix.fromRows 1 0)
    X := Matrix.fromRows (Matrix.fromRows (0 : Matrix B H Binary) 1) 0
    Y := Matrix.fromRows 0 (Matrix.fromRows 0 1)
    plus_injective := ?_
    minus_injective := ?_
    gram := ?_
    plus_annihilator := ?_
    minus_annihilator := ?_
  }
  · intro x y h
    apply Prod.ext
    · funext b
      simpa using congrFun h (Sum.inl (Sum.inl b))
    · funext h₀
      simpa using congrFun h (Sum.inl (Sum.inr h₀))
  · intro x y h
    apply Prod.ext
    · funext b
      simpa using congrFun h (Sum.inr (Sum.inl b))
    · funext h₀
      simpa using congrFun h (Sum.inr (Sum.inr h₀))
  · simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  · simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  · simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]

/--
---
conclusion: Lax342547.FrameExistence.frame_nonempty
---
An explicit block-matrix frame: the first half makes the plus columns
independent; the second half makes the minus columns independent. The
only nonzero self-Gram block is the specified matrix E.
-/
theorem frame_nonempty (E : Matrix B B Binary) :
    Nonempty (Frame B H ((B ⊕ H) ⊕ (B ⊕ H)) E) := ⟨canonicalFrame E⟩

def padFrame {N K : Type} [Fintype N] [Fintype K] {E : Matrix B B Binary}
    (F : Frame B H N E) : Frame B H (N ⊕ K) E where
  P := Matrix.fromRows F.P 0
  Q := Matrix.fromRows F.Q 0
  X := Matrix.fromRows F.X 0
  Y := Matrix.fromRows F.Y 0
  plus_injective := by
    intro x y h
    apply F.plus_injective
    exact funext (fun n => congrFun h (Sum.inl n))
  minus_injective := by
    intro x y h
    apply F.minus_injective
    exact funext (fun n => congrFun h (Sum.inl n))
  gram := by simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, F.gram]
  plus_annihilator := by
    simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, F.plus_annihilator]
  minus_annihilator := by
    simp [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, F.minus_annihilator]

def reindexFrame {N N' : Type} [Fintype N] [Fintype N'] {E : Matrix B B Binary}
    (e : N' ≃ N) (F : Frame B H N E) : Frame B H N' E where
  P := F.P.submatrix e id
  Q := F.Q.submatrix e id
  X := F.X.submatrix e id
  Y := F.Y.submatrix e id
  plus_injective := by
    intro x y h
    apply F.plus_injective
    funext n
    simpa [Matrix.mulVec, dotProduct] using congrFun h (e.symm n)
  minus_injective := by
    intro x y h
    apply F.minus_injective
    funext n
    simpa [Matrix.mulVec, dotProduct] using congrFun h (e.symm n)
  gram := by simpa using congrArg (fun M => M.submatrix id id) F.gram
  plus_annihilator := by
    simpa using congrArg (fun M => M.submatrix id id) F.plus_annihilator
  minus_annihilator := by
    simpa using congrArg (fun M => M.submatrix id id) F.minus_annihilator

/--
---
conclusion: Lax342547.FrameExistence.frame_nonempty_of_card_le
---
Pad the explicit doubled frame with zero rows and transport it across a
coordinate equivalence to any ambient space of dimension at least 2(d+h).
-/
theorem frame_nonempty_of_card_le {N : Type} [Fintype N] (E : Matrix B B Binary)
    (hN : 2 * (Fintype.card B + Fintype.card H) ≤ Fintype.card N) :
    Nonempty (Frame B H N E) := by
  classical
  let K := Fin (Fintype.card N - 2 * (Fintype.card B + Fintype.card H))
  have hc : Fintype.card (((B ⊕ H) ⊕ (B ⊕ H)) ⊕ K) = Fintype.card N := by
    simp only [Fintype.card_sum, Fintype.card_fin, K]
    omega
  let e := Fintype.equivOfCardEq hc
  exact ⟨reindexFrame e.symm (padFrame (K := K) (canonicalFrame E))⟩

end Lax342547Proofs.FrameExistence
