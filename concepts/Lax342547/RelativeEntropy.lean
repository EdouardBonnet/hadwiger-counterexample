import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.StdSimplex
import Lax342547.RetainedImages

/-!
---
title: Finite relative entropy and support costs
type: lemma
---
Finite probability weights have nonnegative relative entropy on their common support. Continuous entropy has compact minimizers, pointwise density caps give an upper budget, and support restriction costs the negative logarithm of its mass.
-/

namespace Lax342547.RelativeEntropy

open scoped BigOperators

noncomputable def entropy {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) : ℝ :=
  ∑ x, (ρ x * Real.log (ρ x) - ρ x * Real.log (q x))

def Probability {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∑ x, ρ x = 1

axiom entropy_nonneg {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ)
    (hρ : Probability ρ) (hq : Probability q) (hsupport : ∀ x, 0 < ρ x → 0 < q x) :
    0 ≤ entropy ρ q

axiom entropy_density_bound {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) (cap : ℝ)
    (hρ : Probability ρ) (hq : ∀ x, 0 < q x) (_hcap : 0 < cap)
    (hbound : ∀ x, ρ x ≤ cap*q x) : entropy ρ q ≤ Real.log cap

axiom continuous_entropy {Ω : Type} [Fintype Ω] (q : Ω → ℝ) : Continuous (fun ρ : Ω → ℝ => entropy ρ q)

axiom compact_entropy_minimizer {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q : Ω → ℝ) (hP : IsCompact P) (hne : P.Nonempty) :
    ∃ ρ ∈ P, ∀ ρ' ∈ P, entropy ρ q ≤ entropy ρ' q

axiom entropy_decomposition {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (_hsupport : ∀ x, 0 < ρ' x → 0 < ρ x)
    (_hρ : ∀ x, 0 ≤ ρ x) (_hρ' : ∀ x, 0 ≤ ρ' x) :
    entropy ρ' q - entropy ρ q = entropy ρ' ρ +
      ∑ x, (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x))

axiom probability_compact {Ω : Type} [Fintype Ω] : IsCompact {ρ : Ω → ℝ | Probability ρ}

axiom probability_convex {Ω : Type} [Fintype Ω] : Convex ℝ {ρ : Ω → ℝ | Probability ρ}

axiom entropy_support_cost {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) (S : Ω → Prop)
    (hρ : Probability ρ) (hq : Probability q)
    (hsupport : ∀ x, 0 < ρ x → 0 < q x) (hS : ∀ x, ¬ S x → ρ x = 0)
    (hmass : 0 < Lax342547.RetainedImages.cellMass q S) :
    -Real.log (Lax342547.RetainedImages.cellMass q S) ≤ entropy ρ q

end Lax342547.RelativeEntropy
