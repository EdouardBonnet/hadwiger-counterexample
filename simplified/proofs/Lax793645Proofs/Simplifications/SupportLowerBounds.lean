import Lax793645Proofs.Simplifications.OneSurrogateProductBounds

/-! Bounded indicators of positive probabilities and one-sided errors for products. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def supportLower (θ a : ℝ) : ℝ:=θ*ind (0<a)

theorem support_lower_bounds (θ a : ℝ) (hθ : 0≤θ ∧ θ≤1) :
    0≤supportLower θ a ∧ supportLower θ a≤1 :=
  ⟨mul_nonneg hθ.1 (ind_nonneg _),
    (mul_le_mul hθ.2 (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)⟩

theorem support_lower_domination (θ a : ℝ) (ha : 0≤a)
    (hgap : 0<a→θ≤a) : supportLower θ a≤a := by
  unfold supportLower
  by_cases hp : 0<a
  · rw [ind_one hp,mul_one]
    exact hgap hp
  · rw [ind_zero hp,mul_zero]
    exact ha

theorem support_lower_covers (θ a : ℝ) (hθ : 0≤θ) (ha : 0≤a ∧ a≤1) :
    θ*a≤supportLower θ a := by
  unfold supportLower
  by_cases hp : 0<a
  · rw [ind_one hp,mul_one]
    exact mul_le_of_le_one_right hθ ha.2
  · have hz : a=0:=le_antisymm (not_lt.mp hp) ha.1
    simp only [hz,ind_zero (lt_irrefl (0:ℝ)),mul_zero]
    exact le_refl 0

theorem product_domination_error {I : Type} [Fintype I]
    (a b : I→ℝ) (ha : ∀ i,0≤a i ∧ a i≤1) (hb : ∀ i,0≤b i ∧ b i≤1)
    (ε : ℝ) (hε : 0≤ε) (h : ∀ i,b i-a i≤ε) :
    (∏ i,b i)-(∏ i,a i)≤num I*ε := by
  let c (i : I):=min (a i) (b i)
  have hc i : |c i|≤1:=by
    rw [abs_of_nonneg (le_min (ha i).1 (hb i).1)]
    exact (min_le_left ..).trans (ha i).2
  have hc' i : |b i|≤1:=by rw [abs_of_nonneg (hb i).1]; exact (hb i).2
  have hd i : |c i-b i|≤ε := by
    rw [abs_of_nonpos (sub_nonpos.mpr (min_le_right ..))]
    dsimp only [c]
    by_cases he : a i≤b i
    · rw [min_eq_left he]
      linarith only [h i]
    · rw [min_eq_right (le_of_not_ge he)]
      simpa using hε
  have hh:=cottonError univ c b ε hc hc' hd
  have hp : (∏ i,c i)≤∏ i,a i:=
    Finset.prod_le_prod (fun i _=>le_min (ha i).1 (hb i).1) (fun i _=>min_le_left ..)
  have hi : (∏ i,b i)-(∏ i,c i)≤num I*ε:=by
    rw [abs_sub_comm] at hh
    exact (le_abs_self _).trans hh
  linarith only [hp,hi]

end
end Lax793645Proofs.Simplifications
