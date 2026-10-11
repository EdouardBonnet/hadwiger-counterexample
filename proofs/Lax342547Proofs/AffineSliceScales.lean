import Lax342547.AffineSliceScales
import Lax342547.InjectionAsymptotics
import Lax342547.RawFrameComparison

namespace Lax342547Proofs.AffineSliceScales
noncomputable section
open Lax342547.AffineSliceScales
open Lax342547.RawFrameComparison

/--
---
conclusion: Lax342547.AffineSliceScales.budget_decay
---
-/
theorem budget_decay (S D : Type) [Fintype S] [Fintype D] (N n : ℕ) (β : ℝ) (hn : n ≤ N) :
    budget S D N n β ≤ Lax342547.AffineSliceScales.scale S D β/(2 : ℝ)^(n/2) := by
  have hsq : (2 : ℝ)^(n/2) ≤ Real.sqrt ((2 : ℝ)^N) := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc : errorBound N (Option D) (Option D) (Option D) (Option D) ≤
      Lax342547.RawFrameComparison.scale (Option D) (Option D) (Option D) (Option D)/(2 : ℝ)^(n/2) :=
    (Lax342547.RawFrameComparison.errorBound_half_decay N _ _ _ _).trans
      (div_le_div_of_nonneg_left (by unfold Lax342547.RawFrameComparison.scale; positivity)
        (by positivity) hsq)
  have hp : (2 : ℝ)^(n/2) ≤ (2 : ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : (4*((2 : ℝ)^(2*Fintype.card D+1)/β^2))/(2 : ℝ)^n ≤
      (4*((2 : ℝ)^(2*Fintype.card D+1)/β^2))/(2 : ℝ)^(n/2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  unfold budget Lax342547.AffineSliceScales.scale
  calc
    _ = (Fintype.card S : ℝ)*errorBound N (Option D) (Option D) (Option D) (Option D)+
        (4*((2 : ℝ)^(2*Fintype.card D+1)/β^2))/(2 : ℝ)^n := by ring
    _ ≤ (Fintype.card S : ℝ)*(Lax342547.RawFrameComparison.scale (Option D) (Option D) (Option D) (Option D)/(2 : ℝ)^(n/2))+
        (4*((2 : ℝ)^(2*Fintype.card D+1)/β^2))/(2 : ℝ)^(n/2) :=
      add_le_add (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) hd
    _ = _ := by ring

/--
---
conclusion: Lax342547.AffineSliceScales.uniform_threshold
---
-/
theorem uniform_threshold (S D : Type) [Fintype S] [Fintype D] (β ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ,∀ n ≥ n₀,∀ N ≥ n,
      Fintype.card (Option D)+Fintype.card (Option D)+1 ≤ N ∧
      ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))*
          ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))/Real.sqrt ((2 : ℝ)^N) ≤
        1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option D) (Option D) (Option D) (Option D))+1) ∧
      budget S D N n β ≤ ε := by
  obtain ⟨N₀,hN₀⟩ := Lax342547.RawFrameComparison.eventually_valid (Option D) (Option D) (Option D) (Option D)
  have ht := (Lax342547.InjectionAsymptotics.polynomial_dyadic_floor_tends_zero 0 2 (by omega)).const_mul (Lax342547.AffineSliceScales.scale S D β)
  have ht' : Filter.Tendsto (fun n : ℕ => Lax342547.AffineSliceScales.scale S D β/(2 : ℝ)^(n/2)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero,one_div,mul_zero,div_eq_mul_inv,one_mul] using ht
  obtain ⟨n₁,hn₁⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 ht').2 ε hε)
  refine ⟨max N₀ n₁,?_⟩
  intro n hn N hN
  have hvalid := hN₀ N (by omega)
  exact ⟨hvalid.1,hvalid.2.2,(Lax342547.AffineSliceScales.budget_decay S D N n β hN).trans (hn₁ n (by omega)).le⟩

end
end Lax342547Proofs.AffineSliceScales
