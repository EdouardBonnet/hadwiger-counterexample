import Lax342547.TinyCompatibility
import Lax342547Proofs.HadamardRank
import Lax342547Proofs.PairPositions

namespace Lax342547Proofs.TinyCompatibility
open Lax342547.TinyCompatibility

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.CellAveraging

/--
---
conclusion: Lax342547.TinyCompatibility.tiny_compatible_mass
---
-/
theorem tiny_compatible_mass {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) :
    1/(((1+F.rank)^2+1 : ℕ) : ℝ)^2 ≤ pairEventMass μ μ (fun a b => F a b = 0 ∧ F b a = 0) := by
  have hh := Lax342547Proofs.PairPositions.inevitable_pair_mass (ι := Fin ((1+F.rank)^2+1)) μ
    (fun a b => F a b = 0 ∧ F b a = 0) hμ (fun x =>
      Lax342547Proofs.HadamardRank.compatible_pair_in_tuple F x hdiag (by simp))
  simp only [Fintype.card_fin] at hh
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using hh

/--
---
conclusion: Lax342547.TinyCompatibility.tiny_compatible_mass_rank_bound
---
-/
theorem tiny_compatible_mass_rank_bound {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (F : Matrix Ω Ω Binary) (d N : ℕ)
    (hμ : Probability μ) (hdiag : ∀ a, F a a = 0) (hrank : F.rank ≤ d*N) :
    1/(4*(1+(d : ℝ)*N)^4) ≤ pairEventMass μ μ (fun a b => F a b = 0 ∧ F b a = 0) := by
  have hh := tiny_compatible_mass μ F hμ hdiag
  have hR : ((1+F.rank)^2+1 : ℕ) ≤ 2*(1+d*N)^2 := by
    have ha : (1+F.rank)^2 ≤ (1+d*N)^2 := Nat.pow_le_pow_left (by omega) 2
    have hb : 1 ≤ (1+d*N)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hreal : ((((1+F.rank)^2+1 : ℕ) : ℝ)^2) ≤ 4*(1+(d : ℝ)*N)^4 := by
    have ht : (((1+F.rank)^2+1 : ℕ) : ℝ) ≤ 2*(1+(d : ℝ)*N)^2 := by exact_mod_cast hR
    have hs := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (((1+F.rank)^2+1 : ℕ) : ℝ)) ht
    nlinarith [sq_nonneg (1+(d : ℝ)*N)]
  exact (one_div_le_one_div_of_le (by positivity) hreal).trans hh

end Lax342547Proofs.TinyCompatibility
