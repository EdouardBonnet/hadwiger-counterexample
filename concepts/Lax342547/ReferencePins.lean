import Lax342547.ExactPins
import Lax342547.ImageScale

/-!
---
title: The full reference cap for exact pin events
type: lemma
---
Component/sign pins use the direct sum of both endpoints' primal and
channel coefficients. Their stored basis images form precisely the
arbitrary-rank tuples covered by the reference image theorem.
-/

namespace Lax342547.ReferencePins

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.ProductImages Lax342547.ExactPins
open scoped ENNReal

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def observationMatrix {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary :=
  if a.2 then jointMatrix (fun i => (plus (o i a.1)).val)
  else jointMatrix (fun i => (minus (o i a.1)).val)

def observation {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary) :=
  (observationMatrix o a).mulVecLin

axiom reference_pin_cap [Fintype Comp]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure (P.event observation) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * Fintype.card N))

end Lax342547.ReferencePins
