import Lax342547.RawFrames
import Mathlib.Probability.Distributions.Uniform

/-!
---
title: The finite uniform raw-vertex law
type: definition and theorem
---
A raw vertex chooses one valid frame in every component. The reference
law is uniform on this finite product. Counting all matrix quadruples
gives $|\Omega|\le 2^{2|\mathcal E|N(d+h)}$, the bound behind (2.14).
-/

namespace Lax342547.RawLaw

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N Comp : Type} [Fintype B] [Fintype H] [Fintype N] [Fintype Comp]
variable [DecidableEq Comp]

noncomputable def uniformLaw (E : Matrix B B Binary) [Nonempty (Frame B H N E)] :
    PMF (Comp → Frame B H N E) := PMF.uniformOfFintype _

axiom raw_card_bound (E : Matrix B B Binary) :
    Fintype.card (Comp → Frame B H N E) ≤
      2 ^ (2 * Fintype.card Comp * Fintype.card N * (Fintype.card B + Fintype.card H))

axiom uniformLaw_product (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (o : Comp → Frame B H N E) :
    uniformLaw E o = ∏ e, PMF.uniformOfFintype (Frame B H N E) (o e)

end Lax342547.RawLaw
