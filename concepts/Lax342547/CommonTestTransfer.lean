import Lax342547.EmpiricalVariance

/-!
---
title: Marginal transfer of common affine-slice tests
type: lemma
---
A bounded marginal density transfers raw empirical variance to a quantitative
comparison with the common reference mean. Near-certain empirical success
therefore forces near-certain reference success, with the original density
cost retained. This is the probability transfer used in Lemma 9.5.
-/

namespace Lax342547.CommonTestTransfer
open Lax342547.RelativeEntropy
open scoped BigOperators

axiom mean_comparison {Ω : Type} [Fintype Ω] (ρ σ F : Ω → ℝ)
    (hσ : Probability σ) (L ε m : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ o,σ o ≤ L*ρ o)
    (hvar : (∑ o,ρ o*(F o-m)^2) ≤ ε) :
    |(∑ o,σ o*F o)-m| ≤ Real.sqrt (L*ε)

axiom success_transfer {Ω : Type} [Fintype Ω] (ρ σ F : Ω → ℝ)
    (hσ : Probability σ) (L ε m η : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ o,σ o ≤ L*ρ o)
    (hvar : (∑ o,ρ o*(F o-m)^2) ≤ ε)
    (hsuccess : 1-η ≤ ∑ o,σ o*F o) :
    1-η-Real.sqrt (L*ε) ≤ m

end Lax342547.CommonTestTransfer
