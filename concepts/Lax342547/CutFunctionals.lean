import Lax342547.CutProfiles
import Mathlib.Algebra.Ring.Parity

/-!
---
title: Well-defined cut functionals
type: theorem
---
A tester vanishing on the common kernel gives a well-defined sum over
all representative values. For an odd number of tags, summing any
tester over all tags except a fixed one is also well-defined. These
are precisely the two descent arguments for $a_t,a,b_t$ in (2.7).
-/

namespace Lax342547.CutFunctionals

open Lax342547.MomentSpace Lax342547.CutProfiles

axiom representative_sums_eq {Tag V : Type} [Fintype Tag] [DecidableEq Tag]
    [Nonempty Tag] [AddCommGroup V] [Module Binary V]
    (W : Tag → Submodule Binary V) (ηO ηS : V →ₗ[Binary] Binary)
    (hO : ∀ c ∈ ⨅ t, W t, ηO c = 0) (hodd : Odd (Fintype.card Tag))
    (w v : Tag → V) (hw : ∀ t, w t ∈ W t) (hv : ∀ t, v t ∈ W t)
    (heq : cutMap w = cutMap v) :
    (∑ t, ηO (w t)) = (∑ t, ηO (v t)) ∧
      ∀ t, (∑ l ∈ Finset.univ.erase t, ηS (w l)) =
        ∑ l ∈ Finset.univ.erase t, ηS (v l)

end Lax342547.CutFunctionals
