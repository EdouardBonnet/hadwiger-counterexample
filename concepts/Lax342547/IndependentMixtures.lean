import Lax342547.PairRecovery
import Lax342547.MixtureRecovery

/-!
---
title: Independent leaf mixtures preserve actual pair-event masses
type: lemma
---
The product of two actual finite leaf mixtures is exactly the mixture of their independent leaf-pair laws, weighted by the original mass product. The same identity holds for every pair event.
-/

namespace Lax342547.IndependentMixtures

open Lax342547.PairRecovery
open scoped ENNReal

axiom independent_pair_mixture {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (ab : ΩA × ΩB) :
    independentPair p₀ q₀ ab = ∑ jk : J × K, (w jk.1 * v jk.2) * independentPair (p jk.1) (q jk.2) ab

axiom independent_mixture_event {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (H : Set (ΩA × ΩB)) :
    (independentPair p₀ q₀).toOuterMeasure H =
      ∑ jk : J × K, (w jk.1 * v jk.2) * (independentPair (p jk.1) (q jk.2)).toOuterMeasure H

end Lax342547.IndependentMixtures
