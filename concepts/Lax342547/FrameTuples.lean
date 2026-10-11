import Lax342547.FrameSymmetry

/-!
---
title: Uniform tuple images on prescribed Gram orbits
type: lemma
---
Independent primal coefficient tuples have the uniform law on their
individually injective realizations with prescribed Gram. Tuples using
channels have the analogous law after conditioning on the self-channel
Gram, including singular Gram matrices and arbitrary tuple dimensions.
-/

namespace Lax342547.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

noncomputable instance {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) : Fintype (Orbit N G) := by classical exact Subtype.fintype _

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

def primalTuple {E : Matrix B B Binary} (C : Matrix B I Binary) (D : Matrix B J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (F : Frame B H N E) : Orbit N (C.transpose * E * D) :=
  ⟨(F.P * C, F.Q * D), by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      apply hC
      have he := F.plus_injective (a₁ := (C.mulVec x, 0)) (a₂ := (C.mulVec y, 0))
        (by simpa only [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec] using h)
      exact congrArg Prod.fst he
    · intro x y h
      apply hD
      have he := F.minus_injective (a₁ := (D.mulVec x, 0)) (a₂ := (D.mulVec y, 0))
        (by simpa only [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec] using h)
      exact congrArg Prod.fst he
    · calc
        _ = C.transpose * (F.P.transpose * F.Q) * D := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [F.gram]⟩

def fullGram (E : Matrix B B Binary) (G : Matrix H H Binary) : Matrix (B ⊕ H) (B ⊕ H) Binary :=
  Matrix.fromBlocks E 0 0 G

abbrev ChannelFiber (E : Matrix B B Binary) (G : Matrix H H Binary) :=
  {F : Frame B H N E // F.X.transpose * F.Y = G}

noncomputable instance (E : Matrix B B Binary) (G : Matrix H H Binary) :
    Fintype (ChannelFiber (N := N) E G) := by classical exact Subtype.fintype _

theorem combined_gram {E : Matrix B B Binary} (F : Frame B H N E) :
    (plus F).val.transpose * (minus F).val = fullGram E (F.X.transpose * F.Y) := by
  simp only [plus, minus, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    F.gram, F.plus_annihilator, F.minus_annihilator, fullGram]

def fullTuple {E : Matrix B B Binary} {G : Matrix H H Binary}
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (F : ChannelFiber (N := N) E G) : Orbit N (C.transpose * fullGram E G * D) :=
  ⟨((plus F.val).val * C, (minus F.val).val * D), by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      apply hC
      apply (plus F.val).property
      simpa only [Matrix.mulVec_mulVec] using h
    · intro x y h
      apply hD
      apply (minus F.val).property
      simpa only [Matrix.mulVec_mulVec] using h
    · calc
        _ = C.transpose * ((plus F.val).val.transpose * (minus F.val).val) * D := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [combined_gram, F.property]⟩

axiom primal_uniform [DecidableEq N] {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : Matrix B I Binary) (D : Matrix B J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * E * D))] :
    (PMF.uniformOfFintype (Frame B H N E)).map (primalTuple C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose * E * D))

axiom full_uniform [DecidableEq N] {E : Matrix B B Binary} {G : Matrix H H Binary}
    [Nonempty (ChannelFiber (N := N) E G)]
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * fullGram E G * D))] :
    (PMF.uniformOfFintype (ChannelFiber (N := N) E G)).map (fullTuple C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose * fullGram E G * D))

axiom raw_full_conditioning [DecidableEq N] {E : Matrix B B Binary} {G : Matrix H H Binary}
    [Nonempty (Frame B H N E)] [Nonempty (ChannelFiber (N := N) E G)]
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * fullGram E G * D))]
    (h : ∃ F ∈ {F : Frame B H N E | F.X.transpose * F.Y = G},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.X.transpose * F.Y = G} h).map
      (fun F => ((plus F).val * C, (minus F).val * D)) =
    (PMF.uniformOfFintype (Orbit N (C.transpose * fullGram E G * D))).map Subtype.val

axiom primal_product {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : Draw → Matrix B I Binary) (D : Draw → Matrix B J Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * E * D s))]
    (z : Draw → Matrix N I Binary × Matrix N J Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o s => ((o s).P * C s, (o s).Q * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * E * D s))).map Subtype.val (z s)

axiom primal_family {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {K L : Draw → Type} [∀ s, Fintype (K s)] [∀ s, Fintype (L s)]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : ∀ s, Matrix B (K s) Binary) (D : ∀ s, Matrix B (L s) Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * E * D s))]
    (z : ∀ s, Matrix N (K s) Binary × Matrix N (L s) Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o s => ((o s).P * C s, (o s).Q * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * E * D s))).map Subtype.val (z s)

axiom full_product {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {K L : Draw → Type} [∀ s, Fintype (K s)] [∀ s, Fintype (L s)]
    {E : Matrix B B Binary} (G : Draw → Matrix H H Binary)
    [∀ s, Nonempty (ChannelFiber (N := N) E (G s))]
    (C : ∀ s, Matrix (B ⊕ H) (K s) Binary) (D : ∀ s, Matrix (B ⊕ H) (L s) Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * fullGram E (G s) * D s))]
    (z : ∀ s, Matrix N (K s) Binary × Matrix N (L s) Binary) :
    (PMF.uniformOfFintype (∀ s, ChannelFiber (N := N) E (G s))).map
      (fun o s => ((plus (o s).val).val * C s, (minus (o s).val).val * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * fullGram E (G s) * D s))).map
      Subtype.val (z s)

end Lax342547.FrameTuples
