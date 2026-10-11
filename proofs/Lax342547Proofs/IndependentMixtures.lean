import Lax342547.IndependentMixtures
import Lax342547.MixtureRecovery
import Lax342547.PairRecovery

namespace Lax342547Proofs.IndependentMixtures
open Lax342547.IndependentMixtures

set_option backward.isDefEq.respectTransparency false
open Lax342547.PairRecovery
open scoped ENNReal

/--
---
conclusion: Lax342547.IndependentMixtures.independent_pair_mixture
---
-/
theorem independent_pair_mixture {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (ab : ΩA × ΩB) :
    independentPair p₀ q₀ ab = ∑ jk : J × K, (w jk.1 * v jk.2) * independentPair (p jk.1) (q jk.2) ab := by
  rw [Lax342547.PairRecovery.independent_pair_apply, hp, hq, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum, Lax342547.PairRecovery.independent_pair_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ac_rfl

/--
---
conclusion: Lax342547.IndependentMixtures.independent_mixture_event
---
-/
theorem independent_mixture_event {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (H : Set (ΩA × ΩB)) :
    (independentPair p₀ q₀).toOuterMeasure H =
      ∑ jk : J × K, (w jk.1 * v jk.2) * (independentPair (p jk.1) (q jk.2)).toOuterMeasure H := by
  exact Lax342547.MixtureRecovery.mixture_event
    (fun jk : J × K => independentPair (p jk.1) (q jk.2))
    (independentPair p₀ q₀) (fun jk => w jk.1 * v jk.2)
    (Lax342547.IndependentMixtures.independent_pair_mixture p q p₀ q₀ w v hp hq) H

end Lax342547Proofs.IndependentMixtures
