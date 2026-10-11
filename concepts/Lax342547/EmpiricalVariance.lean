import Lax342547.FiniteSampling

/-!
---
title: Finite empirical variance from a two-coefficient comparison
type: lemma
---
The affine-slice second-moment step keeps the independent coefficient draws
and the actual bad-pair probability. This finite estimate is also valid for
arbitrary bounded common tests, without polynomial assumptions on them.
-/

namespace Lax342547.EmpiricalVariance
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

axiom empirical_variance {Ω A : Type} [Fintype Ω] [Fintype A]
    (ρ : Ω → ℝ) (κ : A → ℝ) (F : Ω → A → ℝ) (good : A → A → Prop)
    (m ε δ : ℝ) (hρ : Probability ρ) (hκ : Probability κ)
    (hf : ∀ ω a,|F ω a| ≤ 1) (hm : |m| ≤ 1) (hε : 0 ≤ ε)
    (hmean : ∀ a b,good a b → (∑ ω,ρ ω*F ω a) = m ∧ (∑ ω,ρ ω*F ω b) = m)
    (hpair : ∀ a b,good a b → |(∑ ω,ρ ω*F ω a*F ω b)-m^2| ≤ ε)
    (hbad : cellMass (fun ab : A × A => κ ab.1*κ ab.2) (fun ab => ¬ good ab.1 ab.2) ≤ δ) :
    (∑ ω,ρ ω*((∑ a,κ a*F ω a)-m)^2) ≤ ε+4*δ

end Lax342547.EmpiricalVariance
