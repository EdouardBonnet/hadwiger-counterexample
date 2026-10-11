import Lax342547.ImageScale
import Lax342547.ReferenceImages

namespace Lax342547Proofs.ImageScale

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ReferenceImages
open scoped ENNReal

/--
---
conclusion: Lax342547.ImageScale.cost_bound
---
Half of the epsilon budget pays the common-annihilator dimension loss
for every minus rank. The other half pays the fixed 16^c prefactor,
using only that the total nominal rank is at least one.
-/
theorem cost_bound (c p N a b : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * p ≤ N) (ht : 1 ≤ a + b)
    (hp : (4 : ℝ) * p ≤ ε * N) (hc : (8 : ℝ) * c ≤ ε * N) :
    (4 : ℝ≥0∞) ^ (2 * c) / 2 ^ (N * a + (N - 2 * p) * b) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * (a + b : ℕ) * N)) := by
  have ht' : (1 : ℝ) ≤ (a + b : ℕ) := by exact_mod_cast ht
  have hεN : 0 ≤ ε * (N : ℝ) / 2 := by positivity
  have h1 : (4 : ℝ) * c ≤ ε * N / 2 * (a + b : ℕ) := by
    calc
      _ ≤ ε * N / 2 := by linarith
      _ = (ε * N / 2) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ht' hεN
  have h2 : (2 : ℝ) * p * b ≤ ε * N / 2 * (a + b : ℕ) := by
    calc
      _ ≤ (ε * N / 2) * b :=
        mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) * p ≤ ε * N / 2) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_add_left b a)) hεN
  have hcost : (4 : ℝ) * c + 2 * p * b ≤ ε * N * (a + b : ℕ) := by linarith
  have hsub : ((N - 2 * p : ℕ) : ℝ) = (N : ℝ) - 2 * p := by
    rw [Nat.cast_sub hN]
    norm_num
  have hexp : ((4 * c : ℕ) : ℝ) - (N * a + (N - 2 * p) * b : ℕ) ≤
      -((1 - ε) * (a + b : ℕ) * N) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hsub] at *
    nlinarith
  have hnum : (4 : ℝ≥0∞) ^ (2 * c) = 2 ^ (4 * c) := by
    rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [hnum]
  calc
    _ = (2 : ℝ≥0∞) ^ (((4 * c : ℕ) : ℝ) - (N * a + (N - 2 * p) * b : ℕ)) := by
      rw [ENNReal.rpow_sub _ _ (by norm_num) (by norm_num), ENNReal.rpow_natCast, ENNReal.rpow_natCast]
    _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/--
---
conclusion: Lax342547.ImageScale.exists_scale
---
For a full-frame size bounded by a*n+b, one fixed ambient multiplier
pays both dimension and normalization costs at every positive n.
This choice is independent of the nominal ranks and of the unit law.
-/
theorem exists_scale (a b c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (a * n + b) + 1 ≤ M * n ∧
      (4 : ℝ) * (a * n + b : ℕ) ≤ ε * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ ε * (M * n : ℕ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (((4 : ℝ) * (a + b : ℕ) + 8 * c) / ε)
  let M := max m (2 * (a + b) + 1)
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Nat.le_max_left m (2 * (a + b) + 1))
  have hMdim : 2 * (a + b) + 1 ≤ M := Nat.le_max_right _ _
  have hM : (4 : ℝ) * (a + b : ℕ) + 8 * c ≤ ε * M := by
    have h := (div_lt_iff₀ hε).mp hm
    nlinarith
  refine ⟨M, fun n hn => ?_⟩
  have hp : a * n + b ≤ (a + b) * n := by nlinarith
  have hp' : (a * n + b : ℕ) ≤ ((a + b : ℕ) : ℝ) * n := by exact_mod_cast hp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : (4 : ℝ) * (a + b : ℕ) ≤ ε * M := by linarith [show (0 : ℝ) ≤ c by positivity]
  have hC : (8 : ℝ) * c ≤ ε * M := by linarith [show (0 : ℝ) ≤ (a + b : ℕ) by positivity]
  refine ⟨by nlinarith, ?_, ?_⟩
  · have hs := mul_le_mul_of_nonneg_right hA (show (0 : ℝ) ≤ n by positivity)
    push_cast at hp' hs ⊢
    nlinarith
  · calc
      _ ≤ ε * M := hC
      _ = (ε * M) * 1 := (mul_one _).symm
      _ ≤ ε * M * n := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by push_cast; ring

/--
---
conclusion: Lax342547.ImageScale.exists_paper_scale
---
Substitute the actual coefficient count d=pStar*(1+(g²+3)n) and the
fixed channel dimension h. One M₀ pays every reference-image cost at
all positive n, independently of the unit law and the tested ranks.
-/
theorem exists_paper_scale (pStar g h c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (pStar * (1 + (g * g + 3) * n) + h) + 1 ≤ M * n ∧
      (4 : ℝ) * (pStar * (1 + (g * g + 3) * n) + h : ℕ) ≤ ε * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ ε * (M * n : ℕ) := by
  obtain ⟨M, hM⟩ := Lax342547.ImageScale.exists_scale (pStar * (g * g + 3)) (pStar + h) c ε hε
  refine ⟨M, fun n hn => ?_⟩
  have he : pStar * (g * g + 3) * n + (pStar + h) = pStar * (1 + (g * g + 3) * n) + h := by ring
  simpa only [he] using hM n hn

/--
---
conclusion: Lax342547.ImageScale.reference_image_cap
---
Combine the full two-endpoint, all-component raw image estimate with the
uniform cost payment. This is the cap 2^(-(1-epsilon)tN) of Lemma 4.3(c),
where t is the actual summed nominal rank. Dependent tuples and ranks
growing with n are included; only t≥1 is required.
-/
theorem reference_image_cap {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {K L : Comp → Type} [∀ e, Fintype (K e)] [∀ e, Fintype (L e)]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (ε : ℝ) (hε : 0 < ε)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (C : ∀ e, Matrix (Fin 2 × (B ⊕ H)) (K e) Binary)
    (D : ∀ e, Matrix (Fin 2 × (B ⊕ H)) (L e) Binary)
    (y : ∀ e, Matrix N (K e) Binary) (z : ∀ e, Matrix N (L e) Binary)
    (ht : 1 ≤ (∑ e, (C e).rank) + ∑ e, (D e).rank) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure
      {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧ minusImages (D e) (fun i => o i e) = z e} ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * ((∑ e, (C e).rank) + ∑ e, (D e).rank : ℕ) * Fintype.card N)) := by
  have hb := Lax342547.ReferenceImages.all_components_cap (E := E) hN C D y z
  simp only [Fintype.card_fin] at hb
  exact hb.trans (Lax342547.ImageScale.cost_bound (Fintype.card Comp) (Fintype.card B + Fintype.card H)
    (Fintype.card N) (∑ e, (C e).rank) (∑ e, (D e).rank) ε hε (by omega) ht hp hc)

end Lax342547Proofs.ImageScale
