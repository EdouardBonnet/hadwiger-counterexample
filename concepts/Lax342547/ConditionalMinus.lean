import Lax342547.FrameSymmetry
import Lax342547.GramColumns

/-!
---
title: The affine minus-column law at a fixed plus frame
type: lemma
---
With P,X fixed, the Q columns have prescribed evaluations against [P,X]
and the Y columns have zero evaluations against P. These two independent
affine column families are conditioned only on joint minus injectivity.
The failure probability before that conditioning is at most 2^(2(d+h)-N).
-/

namespace Lax342547.ConditionalMinus

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.GramColumns
open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

abbrev ColumnProduct (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  GramFiber (Matrix.fromCols P X) (Matrix.fromRows E 0) × GramFiber P (0 : Matrix B H Binary)

def Good {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (z : ColumnProduct E P X) : Prop :=
  Function.Injective (fun w : (B → Binary) × (H → Binary) =>
    z.1.val.mulVec w.1 + z.2.val.mulVec w.2)

abbrev Completion (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  {z : ColumnProduct E P X // Good z}

abbrev Fiber (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  {F : Frame B H N E // F.P = P ∧ F.X = X}

noncomputable instance (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Fintype (Completion E P X) := by classical exact Subtype.fintype _

noncomputable instance (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Fintype (Fiber E P X) := by classical exact Subtype.fintype _

omit [Fintype N] in
theorem combined_injective_iff (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Function.Injective (Matrix.fromCols P X).mulVec ↔
      Function.Injective (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2) := by
  constructor
  · intro h z w he
    have h' := h (a₁ := Sum.elim z.1 z.2) (a₂ := Sum.elim w.1 w.2)
      (by simpa only [Matrix.fromCols_mulVec_sumElim] using he)
    exact Prod.ext (funext (fun b => congrFun h' (Sum.inl b)))
      (funext (fun j => congrFun h' (Sum.inr j)))
  · intro h z w he
    have h' := h (a₁ := (z ∘ Sum.inl, z ∘ Sum.inr)) (a₂ := (w ∘ Sum.inl, w ∘ Sum.inr))
      (by simpa only [Matrix.fromCols_mulVec] using he)
    funext j
    cases j with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr j => exact congrFun (congrArg Prod.snd h') j

def columns {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (F : Fiber E P X) : Completion E P X :=
  ⟨(⟨F.val.Q, by
       simp only [← F.property.1, ← F.property.2, Matrix.transpose_fromCols,
         Matrix.fromRows_mul, F.val.gram, F.val.plus_annihilator]⟩,
    ⟨F.val.Y, by simpa only [← F.property.1] using F.val.minus_annihilator⟩), F.val.minus_injective⟩

def assemble {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) (z : Completion E P X) : Fiber E P X :=
  ⟨{ P := P, X := X, Q := z.val.1.val, Y := z.val.2.val,
      plus_injective := (combined_injective_iff P X).mp hPX,
      minus_injective := z.property,
      gram := (Matrix.fromRows_inj (by
        simpa only [Matrix.transpose_fromCols, Matrix.fromRows_mul] using z.val.1.property)).1,
      plus_annihilator := (Matrix.fromRows_inj (by
        simpa only [Matrix.transpose_fromCols, Matrix.fromRows_mul] using z.val.1.property)).2,
      minus_annihilator := z.val.2.property }, rfl, rfl⟩

def completionEquiv {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) : Fiber E P X ≃ Completion E P X where
  toFun := columns
  invFun := assemble hPX
  left_inv F := by
    apply Subtype.ext
    apply frameData_injective
    exact Prod.ext F.property.1.symm (Prod.ext rfl (Prod.ext F.property.2.symm rfl))
  right_inv z := by cases z; rfl

axiom conditional_uniform {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (Fiber E P X)] [Nonempty (Completion E P X)] :
    (PMF.uniformOfFintype (Fiber E P X)).map columns = PMF.uniformOfFintype (Completion E P X)

axiom rank_failure [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary)
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) [Nonempty (ColumnProduct E P X)] :
    (PMF.uniformOfFintype (ColumnProduct E P X)).toOuterMeasure {z | ¬ Good z} ≤
      (2 : ℝ≥0∞) ^ (2 * (Fintype.card B + Fintype.card H)) / 2 ^ Fintype.card N

axiom raw_conditioning {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (Frame B H N E)] [Nonempty (Fiber E P X)] [Nonempty (Completion E P X)]
    (h : ∃ F ∈ {F : Frame B H N E | F.P = P ∧ F.X = X},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.P = P ∧ F.X = X} h).map
      (fun F => (F.Q, F.Y)) =
    (PMF.uniformOfFintype (Completion E P X)).map (fun z => (z.val.1.val, z.val.2.val))

axiom completion_event_bound [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary)
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (ColumnProduct E P X)] [Nonempty (Completion E P X)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (S : Set (ColumnProduct E P X)) :
    (PMF.uniformOfFintype (Completion E P X)).toOuterMeasure {z | z.val ∈ S} ≤
      2 * (PMF.uniformOfFintype (ColumnProduct E P X)).toOuterMeasure S

end Lax342547.ConditionalMinus
