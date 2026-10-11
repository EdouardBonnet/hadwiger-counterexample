import Lax342547.ProductMinusImages

/-!
---
title: Joint reference image caps across both signs and all draws
type: lemma
---
Expose the plus frames, then integrate the uniform conditional minus
estimate over the plus prescription. Nominal ranks are taken in the
direct sum over all draws. The finite bound retains every conditioning
factor and the complete common-annihilator dimension loss.
-/

namespace Lax342547.ReferenceImages

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry Lax342547.ProductImages
open scoped ENNReal

variable {Draw B H T U N : Type} [Fintype Draw] [Fintype B] [Fintype H]
  [Fintype T] [Fintype U] [Fintype N]

def plusImages {E : Matrix B B Binary} (C : Matrix (Draw × (B ⊕ H)) T Binary)
    (o : Draw → Frame B H N E) : Matrix N T Binary :=
  jointMatrix (fun i => (plus (o i)).val) * C

def minusImages {E : Matrix B B Binary} (C : Matrix (Draw × (B ⊕ H)) U Binary)
    (o : Draw → Frame B H N E) : Matrix N U Binary :=
  jointMatrix (fun i => (minus (o i)).val) * C

axiom joint_cap [DecidableEq Draw] [DecidableEq B] [DecidableEq H]
    [DecidableEq T] [DecidableEq U] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (D : Matrix (Draw × (B ⊕ H)) U Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (y : Matrix N T Binary) (z : Matrix N U Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure
      {o | plusImages C o = y ∧ minusImages D o = z} ≤
      (4 : ℝ≥0∞) ^ Fintype.card Draw /
        2 ^ (Fintype.card N * Fintype.card T + Fintype.card U *
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))

axiom joint_rank_cap [DecidableEq Draw] [DecidableEq B] [DecidableEq H]
    [DecidableEq T] [DecidableEq U] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (D : Matrix (Draw × (B ⊕ H)) U Binary)
    (y : Matrix N T Binary) (z : Matrix N U Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure
      {o | plusImages C o = y ∧ minusImages D o = z} ≤
      (4 : ℝ≥0∞) ^ Fintype.card Draw /
        2 ^ (Fintype.card N * C.rank + D.rank *
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))

axiom all_components_cap {Comp : Type} [Fintype Comp] [DecidableEq Comp]
    {K L : Comp → Type} [∀ e, Fintype (K e)] [∀ e, Fintype (L e)]
    [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : ∀ e, Matrix (Draw × (B ⊕ H)) (K e) Binary)
    (D : ∀ e, Matrix (Draw × (B ⊕ H)) (L e) Binary)
    (y : ∀ e, Matrix N (K e) Binary) (z : ∀ e, Matrix N (L e) Binary) :
    (PMF.uniformOfFintype (Draw → Comp → Frame B H N E)).toOuterMeasure
      {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧ minusImages (D e) (fun i => o i e) = z e} ≤
      (4 : ℝ≥0∞) ^ (Fintype.card Draw * Fintype.card Comp) /
        2 ^ (Fintype.card N * ∑ e, (C e).rank +
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)) * ∑ e, (D e).rank)

end Lax342547.ReferenceImages
