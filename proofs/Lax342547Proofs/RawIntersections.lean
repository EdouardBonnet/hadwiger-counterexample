import Lax342547.RawIntersections
import Lax342547Proofs.FiniteProbability
import Lax342547.ImageScale
import Lax342547.KernelWitness

namespace Lax342547Proofs.RawIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.ProductImages Lax342547.ReferenceImages Lax342547.TensorIntersections
open Lax342547.RawIntersections
open scoped ENNReal

theorem joint_pair_apply {I N : Type} [Fintype I] (A : Fin 2 → Matrix N I Binary)
    (z : Fin 2 × I → Binary) :
    (jointMatrix A).mulVec z = (A 0).mulVec (fun j => z (0, j)) + (A 1).mulVec (fun j => z (1, j)) := by
  funext n
  simp only [Matrix.mulVec, dotProduct, jointMatrix, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.add_apply]

theorem intersection_le_kernel {I N : Type} [Fintype I] [Fintype N]
    (A : Fin 2 → Matrix N I Binary) :
    Module.finrank Binary (intersectionSpace (A 0) (A 1)) ≤
      Module.finrank Binary (LinearMap.ker (jointMatrix A).mulVecLin) := by
  classical
  let S := LinearMap.ker (jointMatrix A).mulVecLin
  let f : S →ₗ[Binary] (N → Binary) := (A 0).mulVecLin.comp
    ((LinearMap.pi (fun j : I => LinearMap.proj ((0 : Fin 2), j))).comp S.subtype)
  have hrange : intersectionSpace (A 0) (A 1) ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨a, ha⟩ := hv.1
    obtain ⟨b, hb⟩ := hv.2
    change (A 0).mulVec a = v at ha
    change (A 1).mulVec b = v at hb
    let z : Fin 2 × I → Binary := fun p => if p.1 = 0 then a p.2 else b p.2
    have hz : z ∈ S := by
      change (jointMatrix A).mulVec z = 0
      rw [joint_pair_apply]
      simp only [z, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
      change (A 0).mulVec a + (A 1).mulVec b = 0
      rw [ha, hb]
      exact ZModModule.add_self v
    refine ⟨⟨z, hz⟩, ?_⟩
    change (A 0).mulVec (fun j => z (0, j)) = v
    simpa [z] using ha
  exact (Submodule.finrank_mono hrange).trans f.finrank_range_le

theorem primal_range_le_plus {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (F : Frame B H N E) :
    LinearMap.range F.P.mulVecLin ≤ LinearMap.range (plus F).val.mulVecLin := by
  rintro v ⟨a, rfl⟩
  refine ⟨Sum.elim a 0, ?_⟩
  change (Matrix.fromCols F.P F.X).mulVec (Sum.elim a 0) = F.P.mulVec a
  rw [Matrix.fromCols_mulVec]
  change F.P.mulVec a + F.X.mulVec (0 : H → Binary) = F.P.mulVec a
  simp

/--
---
conclusion: Lax342547.RawIntersections.intersection_kernel_bound
---
Common primal images also lie in the two full plus spans. Each common
image lifts to a zero-image relation between the endpoints, so its
intersection dimension is bounded by the nominal relation-kernel dimension.
-/
theorem intersection_kernel_bound {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E) :
    intersectionDimension o ≤ ∑ e, Module.finrank Binary (LinearMap.ker (jointPlus o e).mulVecLin) := by
  apply Finset.sum_le_sum
  intro e _
  have hi : intersectionSpace (o 0 e).P (o 1 e).P ≤
      intersectionSpace (plus (o 0 e)).val (plus (o 1 e)).val :=
    inf_le_inf (primal_range_le_plus (o 0 e)) (primal_range_le_plus (o 1 e))
  exact (Submodule.finrank_mono hi).trans (intersection_le_kernel (fun i => (plus (o i e)).val))

/--
---
conclusion: Lax342547.RawIntersections.reference_kernel_bound
---
Every large primal intersection has a bounded-column kernel certificate.
Apply the all-rank reference image cap to each fixed certificate, with
zero minus tuple, and pay the exact number of coefficient descriptions.
-/
theorem reference_kernel_bound {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (q : ℕ) (hq : 1 ≤ q)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ (1 / 4 : ℝ) * Fintype.card N) :
    (PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)).toOuterMeasure
      {o | q ≤ intersectionDimension o} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * (2 * (Fintype.card B + Fintype.card H)) * q) *
        (2 : ℝ≥0∞) ^ (-((3 / 4 : ℝ) * q * Fintype.card N)) := by
  let p := PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)
  have hcap (C : Comp → Matrix (Fin 2 × (B ⊕ H)) (Fin q) Binary)
      (hrank : q ≤ ∑ e, (C e).rank) :
      p.toOuterMeasure {o | ∀ e, jointPlus o e * C e = 0} ≤
        (2 : ℝ≥0∞) ^ (-((3 / 4 : ℝ) * q * Fintype.card N)) := by
    have h := Lax342547.ImageScale.reference_image_cap (E := E) (1 / 4) (by norm_num) hN hp hc C
      (fun _ => (0 : Matrix (Fin 2 × (B ⊕ H)) (Fin 0) Binary))
      (fun _ => 0) (fun _ => 0) (by simpa using hq.trans hrank)
    have he : {o : Fin 2 → Comp → Frame B H N E | ∀ e, jointPlus o e * C e = 0} =
        {o | ∀ e, plusImages (C e) (fun i => o i e) = 0 ∧
          minusImages (0 : Matrix (Fin 2 × (B ⊕ H)) (Fin 0) Binary) (fun i => o i e) = 0} := by
      ext o
      simp [plusImages, minusImages, jointPlus]
    rw [← he] at h
    simp only [Matrix.rank_zero, Finset.sum_const_zero, Nat.add_zero] at h
    apply h.trans
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have hrank' : (q : ℝ) ≤ (∑ e, (C e).rank : ℕ) := by exact_mod_cast hrank
    have hn : (0 : ℝ) ≤ Fintype.card N := by positivity
    nlinarith
  calc
    _ ≤ p.toOuterMeasure {o | q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (jointPlus o e).mulVecLin)} :=
      p.toOuterMeasure.mono (fun o ho => ho.trans (Lax342547.RawIntersections.intersection_kernel_bound o))
    _ ≤ _ := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum] using
        Lax342547.KernelWitness.kernel_event_bound p jointPlus q _ hcap

theorem density_exponent_bound (D N a : ℕ) (ha : (a : ℝ) ≤ (D : ℝ) * N / 4) :
    (2 : ℝ≥0∞) ^ (D * N) *
      ((2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ (-((3 / 4 : ℝ) * (2 * D : ℕ) * N))) ≤
        (2 : ℝ≥0∞) ^ (-((D : ℝ) * N / 4)) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
    ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

/--
---
conclusion: Lax342547.RawIntersections.capped_intersection_bound
---
Multiply the reference certificate union bound by the allowed joint
density. A quarter of DN pays the coefficient count, leaving at least
a quarter of DN of exponential decay after the rank-2D image cost.
-/
theorem capped_intersection_bound {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (D : ℕ) (hD : 1 ≤ D)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ (1 / 4 : ℝ) * Fintype.card N)
    (hcount : (Fintype.card Comp * (2 * (Fintype.card B + Fintype.card H)) * (2 * D) : ℕ) ≤
      (D : ℝ) * Fintype.card N / 4)
    (σ : PMF (Fin 2 → Comp → Frame B H N E))
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) * PMF.uniformOfFintype _ o) :
    σ.toOuterMeasure {o | 2 * D < intersectionDimension o} ≤
      (2 : ℝ≥0∞) ^ (-((D : ℝ) * Fintype.card N / 4)) := by
  let p := PMF.uniformOfFintype (Fin 2 → Comp → Frame B H N E)
  calc
    _ ≤ σ.toOuterMeasure {o | 2 * D ≤ intersectionDimension o} :=
      σ.toOuterMeasure.mono (fun _ h => Nat.le_of_lt h)
    _ ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) * p.toOuterMeasure {o | 2 * D ≤ intersectionDimension o} :=
      FiniteProbability.event_density σ p _ hσ _
    _ ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) *
        ((2 : ℝ≥0∞) ^ (Fintype.card Comp * (2 * (Fintype.card B + Fintype.card H)) * (2 * D)) *
          (2 : ℝ≥0∞) ^ (-((3 / 4 : ℝ) * (2 * D : ℕ) * Fintype.card N))) :=
      mul_le_mul_of_nonneg_left (Lax342547.RawIntersections.reference_kernel_bound (2 * D) (by omega) hN hp hc) zero_le
    _ ≤ _ := density_exponent_bound D _ _ hcount

/--
---
conclusion: Lax342547.RawIntersections.exists_intersection_scale
---
Choose one ambient multiplier larger than every fixed linear coefficient
in the image and description costs. Multiplication by n then pays all
four inequalities simultaneously, for every positive n and every D.
-/
theorem exists_intersection_scale (a b c : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (a * n + b) + 1 ≤ M * n ∧
      (4 : ℝ) * (a * n + b : ℕ) ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      ∀ D : ℕ, (c * (2 * (a * n + b)) * (2 * D) : ℕ) ≤ (D : ℝ) * (M * n : ℕ) / 4 := by
  let M := 2 * (a + b) + 1 + 16 * (a + b) + 32 * c + 16 * c * (a + b)
  have hM₁ : 2 * (a + b) + 1 ≤ M := by omega
  have hM₂ : 16 * (a + b) ≤ M := by omega
  have hM₃ : 32 * c ≤ M := by omega
  have hM₄ : 16 * c * (a + b) ≤ M := by omega
  refine ⟨M, fun n hn => ?_⟩
  have hp : a * n + b ≤ (a + b) * n := by nlinarith
  have hnM : M ≤ M * n := by nlinarith
  have h₁ := Nat.mul_le_mul_right n hM₁
  have h₂ := (Nat.mul_le_mul_left 16 hp).trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right n hM₂)
  have h₃ := hM₃.trans hnM
  have h₄ := (Nat.mul_le_mul_left (16 * c) hp).trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right n hM₄)
  have h₂' : (16 : ℝ) * (a * n + b : ℕ) ≤ (M * n : ℕ) := by exact_mod_cast h₂
  have h₃' : (32 : ℝ) * c ≤ (M * n : ℕ) := by exact_mod_cast h₃
  have h₄' : (16 : ℝ) * c * (a * n + b : ℕ) ≤ (M * n : ℕ) := by exact_mod_cast h₄
  refine ⟨by nlinarith, by linarith, by linarith, fun D => ?_⟩
  have hD := mul_le_mul_of_nonneg_left h₄' (show (0 : ℝ) ≤ D by positivity)
  push_cast at hD ⊢
  nlinarith

/--
---
conclusion: Lax342547.RawIntersections.exists_paper_intersection_scale
---
The concrete primal-plus-channel dimension is linear in n. Substituting
its exact coefficients gives a scale independent of n and of the unit law.
-/
theorem exists_paper_intersection_scale (pStar g h c : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (pStar * (1 + (g * g + 3) * n) + h) + 1 ≤ M * n ∧
      (4 : ℝ) * (pStar * (1 + (g * g + 3) * n) + h : ℕ) ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      (8 : ℝ) * c ≤ (1 / 4 : ℝ) * (M * n : ℕ) ∧
      ∀ D : ℕ, (c * (2 * (pStar * (1 + (g * g + 3) * n) + h)) * (2 * D) : ℕ) ≤
        (D : ℝ) * (M * n : ℕ) / 4 := by
  obtain ⟨M, hM⟩ := Lax342547.RawIntersections.exists_intersection_scale (pStar * (g * g + 3)) (pStar + h) c
  refine ⟨M, fun n hn => ?_⟩
  have he : pStar * (g * g + 3) * n + (pStar + h) = pStar * (1 + (g * g + 3) * n) + h := by ring
  simpa only [he] using hM n hn

end Lax342547Proofs.RawIntersections
