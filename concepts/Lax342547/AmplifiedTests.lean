import Lax342547.FiniteSampling

/-!
---
title: Finite amplified-test averaging
type: lemma
---
Finite Fubini transfers a pointwise amplified-test upper bound to an exception bound for arbitrary whole-unit predicates.
-/

namespace Lax342547.AmplifiedTests

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

axiom test_fubini {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (T : A → B → Prop) :
    (∑ b,β b*cellMass α (fun a => T a b)) =
      ∑ a,α a*cellMass β (T a)

axiom amplified_bad_mass {A B : Type} [Fintype A] [Fintype B]
    (α : A → ℝ) (β : B → ℝ) (T : A → B → Prop) (bad : B → Prop) (c U : ℝ)
    (hα : Probability α) (hβ : ∀ b,0 ≤ β b) (hc : 0 < c)
    (hlower : ∀ b,bad b → c ≤ cellMass α (fun a => T a b))
    (hupper : ∀ a,cellMass β (T a) ≤ U) : cellMass β bad ≤ U/c

end Lax342547.AmplifiedTests
