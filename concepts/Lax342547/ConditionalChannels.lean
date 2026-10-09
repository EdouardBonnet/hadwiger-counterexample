import Lax342547.FrameSymmetry

/-!
---
title: Conditional independence of the two channel frames
type: definition and theorem
---
At fixed primal matrices P,Q, the valid X and Y completions form a
Cartesian product: their annihilator and injectivity conditions are
separate. Uniform conditioning therefore gives independent uniform
channel completions, with the actual finite normalizing factors.
-/

namespace Lax342547.ConditionalChannels

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

abbrev PlusCompletion (P Q : Matrix N B Binary) :=
  {X : Matrix N H Binary // X.transpose * Q = 0 ∧ Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)}

abbrev MinusCompletion (P Q : Matrix N B Binary) :=
  {Y : Matrix N H Binary // P.transpose * Y = 0 ∧ Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)}

abbrev Fiber (E : Matrix B B Binary) (P Q : Matrix N B Binary) :=
  {F : Frame B H N E // F.P = P ∧ F.Q = Q}

noncomputable instance (P Q : Matrix N B Binary) : Fintype (PlusCompletion (H := H) P Q) := by
  classical exact Subtype.fintype _

noncomputable instance (P Q : Matrix N B Binary) : Fintype (MinusCompletion (H := H) P Q) := by
  classical exact Subtype.fintype _

noncomputable instance (E : Matrix B B Binary) (P Q : Matrix N B Binary) :
    Fintype (Fiber (H := H) E P Q) := by classical exact Subtype.fintype _

def channels {E : Matrix B B Binary} {P Q : Matrix N B Binary} (F : Fiber (H := H) E P Q) :
    PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q :=
  (⟨F.val.X, by
      simpa [← F.property.1, ← F.property.2] using
        And.intro F.val.plus_annihilator F.val.plus_injective⟩,
   ⟨F.val.Y, by
      simpa [← F.property.1, ← F.property.2] using
        And.intro F.val.minus_annihilator F.val.minus_injective⟩)

def assemble {E : Matrix B B Binary} {P Q : Matrix N B Binary} (hgram : P.transpose * Q = E)
    (X : PlusCompletion (H := H) P Q) (Y : MinusCompletion (H := H) P Q) :
    Fiber (H := H) E P Q :=
  ⟨{ P := P, Q := Q, X := X.val, Y := Y.val,
     plus_injective := X.property.2, minus_injective := Y.property.2,
     gram := hgram, plus_annihilator := X.property.1, minus_annihilator := Y.property.1 },
    rfl, rfl⟩

def channelEquiv {E : Matrix B B Binary} {P Q : Matrix N B Binary} (hgram : P.transpose * Q = E) :
    Fiber (H := H) E P Q ≃ (PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q) where
  toFun := channels
  invFun z := assemble hgram z.1 z.2
  left_inv F := by
    apply Subtype.ext
    apply frameData_injective
    exact Prod.ext F.property.1.symm (Prod.ext F.property.2.symm rfl)
  right_inv z := by cases z; rfl

axiom conditional_uniform {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)] :
    (PMF.uniformOfFintype (Fiber (H := H) E P Q)).map channels =
      PMF.uniformOfFintype (PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q)

axiom conditional_point {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)]
    (X : PlusCompletion (H := H) P Q) (Y : MinusCompletion (H := H) P Q) :
    (PMF.uniformOfFintype (Fiber (H := H) E P Q)).map channels (X, Y) =
      PMF.uniformOfFintype (PlusCompletion (H := H) P Q) X *
        PMF.uniformOfFintype (MinusCompletion (H := H) P Q) Y

axiom raw_conditioning {E : Matrix B B Binary} {P Q : Matrix N B Binary}
    (hgram : P.transpose * Q = E) [Nonempty (Frame B H N E)]
    [Nonempty (Fiber (H := H) E P Q)]
    [Nonempty (PlusCompletion (H := H) P Q)] [Nonempty (MinusCompletion (H := H) P Q)]
    (h : ∃ F ∈ {F : Frame B H N E | F.P = P ∧ F.Q = Q},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.P = P ∧ F.Q = Q} h).map
      (fun F => (F.X, F.Y)) =
    (PMF.uniformOfFintype (PlusCompletion (H := H) P Q × MinusCompletion (H := H) P Q)).map
      (fun z => (z.1.val, z.2.val))

end Lax342547.ConditionalChannels
