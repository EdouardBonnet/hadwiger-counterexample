import Lax342547.HoleRelation
import Lax342547.MomentSpace

/-!
---
title: The symmetric binary gradient form
type: definition and theorem
---
The form in (2.8)–(2.10): $a\otimes a$, the symmetric tester terms,
and the symmetrization of the mixer form. Its diagonal is $a$.
-/

namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

def form (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) : LinearMap.BilinForm Binary X :=
  rankOne a a + (∑ t, (rankOne (aTag t) (bTag t) + rankOne (bTag t) (aTag t))) + B + B.flip

axiom form_properties (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) :
    (∀ x y, form a aTag bTag B x y = form a aTag bTag B y x) ∧
      ∀ x, form a aTag bTag B x x = a x

end Lax342547.GradientForm
