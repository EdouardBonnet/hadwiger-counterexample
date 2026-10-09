import Lax342547.SparseIntersections
import Lax342547Proofs.RawIntersections
import Lax342547Proofs.SparseRepresentatives
import Lax342547Proofs.FrameExistence
import Lax342547Proofs.CoordinateCounts

namespace Lax342547Proofs.SparseIntersections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut
open Lax342547.RawFrames Lax342547.RawIntersections Lax342547.SparseRepresentatives
open scoped ENNReal

/--
---
conclusion: Lax342547.SparseIntersections.paper_sparse_parameters
---
The paper's early constants satisfy the strict-majority condition and
specialize the per-representation support bound to 16000 tags.
-/
theorem paper_sparse_parameters :
    let g := 10 ^ 9 + 1
    let D := 4000 * g
    1 ≤ D ∧ 8 * D < g * g ∧ 4 * D / g = 16000 := by norm_num

/--
---
conclusion: Lax342547.SparseIntersections.exists_concrete_scale
---
Use the checked exact count of selector/base coordinates to specialize
the linear-size scale choice to the paper's actual coefficient space.
This single ambient scale works for every positive n and every unit law.
-/
theorem exists_concrete_scale (k b degree h : ℕ) :
    ∃ M₀ : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (Fintype.card (Coordinate k n b degree) + h) + 1 ≤ M₀ * n ∧
      (4 : ℝ) * (Fintype.card (Coordinate k n b degree) + h : ℕ) ≤ (1 / 4 : ℝ) * (M₀ * n : ℕ) ∧
      (8 : ℝ) * Fintype.card (Component (Tag k)) ≤ (1 / 4 : ℝ) * (M₀ * n : ℕ) ∧
      ∀ D : ℕ, (Fintype.card (Component (Tag k)) * (2 * (Fintype.card (Coordinate k n b degree) + h)) * (2 * D) : ℕ) ≤
        (D : ℝ) * (M₀ * n : ℕ) / 4 := by
  obtain ⟨M₀, hM⟩ := RawIntersections.exists_paper_intersection_scale
    (∑ j ∈ Finset.range (degree + 1), b.choose j) (2 * k + 1) h (Fintype.card (Component (Tag k)))
  refine ⟨M₀, fun n hn => ?_⟩
  rw [(CoordinateCounts.coordinate_dimensions k n b degree).2.2]
  simpa only [pow_two] using hM n hn

theorem normalized_unique {k n b degree : ℕ} (x : Profile k n b degree)
    (w v : Representation k n b degree) (hw : Normalized x w) (hv : Normalized x v) : w = v := by
  apply Subtype.ext
  exact CutSparsity.majority_unique w.val v.val (hw.1.trans hv.1.symm)
    (by simpa only [Tag, ZMod.card] using hw.2) (by simpa only [Tag, ZMod.card] using hv.2)

/--
---
conclusion: Lax342547.SparseIntersections.raw_intersections
---
The coefficient-count union estimate bounds the actual joint-capped law's
intersection exception. Outside it, injective tensor rank preservation,
cyclic majority normalization, and the concrete trace identity give all
the rank, support, uniqueness, and chiStar assertions of Lemma 4.4.
-/
theorem raw_intersections {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (D : ℕ) (hD : 1 ≤ D) (hsmall : 8 * D < (2 * k + 1) * (2 * k + 1))
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) + 1 ≤ N)
    (hp : (4 : ℝ) * (Fintype.card (Coordinate k n b degree) + h : ℕ) ≤ (1 / 4 : ℝ) * N)
    (hc : (8 : ℝ) * Fintype.card (Component (Tag k)) ≤ (1 / 4 : ℝ) * N)
    (hcount : (Fintype.card (Component (Tag k)) * (2 * (Fintype.card (Coordinate k n b degree) + h)) * (2 * D) : ℕ) ≤
      (D : ℝ) * N / 4)
    (σ : PMF (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)))
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * N) / Fintype.card (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))) :
    σ.toOuterMeasure {o | 2 * D < intersectionDimension o} ≤ (2 : ℝ≥0∞) ^ (-((D : ℝ) * N / 4)) ∧
      ∀ o : Fin 2 → Component (Tag k) →
        Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M),
        intersectionDimension o ≤ 2 * D →
        ∀ x y : Profile k n b degree, profileMap (o 0) x.val = profileMap (o 1) y.val →
          (∑ e, (x.val e).rank) ≤ 2 * D ∧ (∑ e, (y.val e).rank) ≤ 2 * D ∧
          ∃ w v : Representation k n b degree, Normalized x w ∧ Normalized y v ∧
            supportSize w.val ≤ 4 * D / (2 * k + 1) ∧ supportSize v.val ≤ 4 * D / (2 * k + 1) ∧
            chiStar hr w = chiStar hr v ∧
            (∀ u : Representation k n b degree, Normalized x u → u = w) ∧
            (∀ u : Representation k n b degree, Normalized y u → u = v) := by
  classical
  let : Nonempty (Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)) :=
    FrameExistence.frame_nonempty_of_card_le _ (by simpa using Nat.le_of_succ_le hN)
  constructor
  · have hdensity (o) : σ o ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card (Fin N)) * PMF.uniformOfFintype _ o := by
      simpa only [Fintype.card_fin, PMF.uniformOfFintype_apply, div_eq_mul_inv] using hσ o
    simpa only [Fintype.card_fin] using RawIntersections.capped_intersection_bound D hD
      (by simpa only [Fintype.card_fin] using hN) (by simpa only [Fintype.card_fin] using hp)
      (by simpa only [Fintype.card_fin] using hc) (by simpa only [Fintype.card_fin] using hcount) σ hdensity
  · intro o ho x y hxy
    have hsmall' : 4 * (2 * D) < (2 * k + 1) * (2 * k + 1) := by omega
    have hrank := TensorIntersections.shared_total_rank (o 0) (o 1) x.val y.val hxy
    have hx : (∑ e, (x.val e).rank) ≤ 2 * D := hrank.2.trans ho
    have hy : (∑ e, (y.val e).rank) ≤ 2 * D := by rw [← hrank.1]; exact hx
    obtain ⟨w, v, hw, hv, hsw, hsv, hchi⟩ := SparseRepresentatives.shared_sparse_profiles
      hr hd M (o 0) (o 1) (2 * D) hsmall' ho x y hxy
    refine ⟨hx, hy, w, v, hw, hv, ?_, ?_, hchi,
      fun u hu => normalized_unique x u w hu hw, fun u hu => normalized_unique y u v hu hv⟩
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)).mpr
      nlinarith
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)).mpr
      nlinarith

end Lax342547Proofs.SparseIntersections
