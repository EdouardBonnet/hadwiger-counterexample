import Lax342547.ProductImages
import Lax342547.ConditionalMinus

/-!
---
title: Joint minus images after exposing several plus frames
type: definition and theorem
---
After exposing all plus frames, their common annihilator loses at most
one full-frame dimension per draw. Every affine minus column contains
this translation space. Independent nominal tuples mixing all draws
therefore retain the stated number of uniform image bits, at any rank.
-/

namespace Lax342547.ProductMinusImages

open Lax342547.MomentSpace Lax342547.ConditionalMinus Lax342547.ProductImages
open scoped ENNReal

variable {Draw B H T N : Type} [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]

def images {E : Matrix B B Binary} {P : Draw → Matrix N B Binary} {X : Draw → Matrix N H Binary}
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (z : ∀ i, ColumnProduct E (P i) (X i)) : Matrix N T Binary :=
  jointMatrix (fun i => Matrix.fromCols (z i).1.val (z i).2.val) * C

axiom affine_image_bound [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary)
    (hPX : ∀ i, Function.Injective (Matrix.fromCols (P i) (X i)).mulVec)
    [∀ i, Nonempty (ColumnProduct E (P i) (X i))]
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (∀ i, ColumnProduct E (P i) (X i))).map (images C) y ≤
      1 / (2 : ℝ≥0∞) ^ (Fintype.card T *
        (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))

axiom completion_image_bound [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Draw → Matrix N B Binary) (X : Draw → Matrix N H Binary)
    (hPX : ∀ i, Function.Injective (Matrix.fromCols (P i) (X i)).mulVec)
    [∀ i, Nonempty (ColumnProduct E (P i) (X i))] [∀ i, Nonempty (Completion E (P i) (X i))]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec) (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (∀ i, Completion E (P i) (X i))).map
      (fun z => images C (fun i => (z i).val)) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card T *
        (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))

end Lax342547.ProductMinusImages
