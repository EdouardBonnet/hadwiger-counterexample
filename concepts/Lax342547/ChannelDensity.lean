import Lax342547.FrameSymmetry
import Lax342547.GramNormalization

/-!
---
title: Joint channel law and its independent-column density
type: lemma
---
The raw joint channel law is constant on each individually injective
Gram orbit. Gram normalization bounds its density relative to completely
independent channel columns by 2^(h²+2), independently of the primal
dimension. The bound multiplies over the fixed set of components.
-/

namespace Lax342547.ChannelDensity

open Lax342547.MomentSpace Lax342547.RawFrames
open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def channels {E : Matrix B B Binary} (F : Frame B H N E) :
    Matrix N H Binary × Matrix N H Binary := (F.X, F.Y)

noncomputable def jointLaw (E : Matrix B B Binary) [Nonempty (Frame B H N E)] :
    PMF (Matrix N H Binary × Matrix N H Binary) :=
  (PMF.uniformOfFintype (Frame B H N E)).map channels

axiom same_gram_mass [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (A A' B B' : Matrix N H Binary)
    (hA : Function.Injective A.mulVec) (hA' : Function.Injective A'.mulVec)
    (hB : Function.Injective B.mulVec) (hB' : Function.Injective B'.mulVec)
    (hG : A.transpose * B = A'.transpose * B') :
    jointLaw E (A, B) = jointLaw E (A', B')

axiom point_density [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (z : Matrix N H Binary × Matrix N H Binary) :
    jointLaw E z ≤ (2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) *
      PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary) z

axiom event_density [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (S : Set (Matrix N H Binary × Matrix N H Binary)) :
    (jointLaw E).toOuterMeasure S ≤
      (2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) *
        (PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary)).toOuterMeasure S

axiom all_components_density {Comp : Type} [Fintype Comp] [DecidableEq Comp]
    [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (z : Comp → Matrix N H Binary × Matrix N H Binary) :
    (RawLaw.uniformLaw E).map (fun o e => channels (o e)) z ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * (Fintype.card H * Fintype.card H + 2)) *
        PMF.uniformOfFintype (Comp → Matrix N H Binary × Matrix N H Binary) z

end Lax342547.ChannelDensity
