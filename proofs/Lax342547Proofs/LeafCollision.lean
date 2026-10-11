import Lax342547.LeafCollision
import Lax342547.CellAveraging
import Lax342547.CollisionCosts
import Lax342547.IndependentMixtures
import Lax342547.PairRecovery
import Lax342547.ParameterCellAveraging
import Lax342547.RealCellLaws

namespace Lax342547Proofs.LeafCollision
open Lax342547.LeafCollision

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealCellLaws Lax342547.PairRecovery Lax342547.ParameterCellAveraging
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafCollision.mixture_real_weights
---
-/
theorem mixture_real_weights {Ω J : Type} [Fintype J]
    (p : J → PMF Ω) (p₀ : PMF Ω) (w : J → ℝ≥0∞)
    (hw : ∀ j, w j ≠ ⊤) (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (a : Ω) :
    weights p₀ a = ∑ j, (w j).toReal * weights (p j) a := by
  unfold weights
  rw [hp, ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (hw j) ((p j).apply_ne_top a))]
  simp only [ENNReal.toReal_mul]

/--
---
conclusion: Lax342547.LeafCollision.real_pair_mixture
---
-/
theorem real_pair_mixture {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hw : ∀ j, w j ≠ ⊤) (hv : ∀ k, v k ≠ ⊤)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (H : ΩA → ΩB → Prop) :
    pairMass (weights p₀) (weights q₀) H =
      average (fun j => (w j).toReal) (fun k => (v k).toReal)
        (fun j k => pairMass (weights (p j)) (weights (q k)) H) := by
  classical
  rw [Lax342547.PairRecovery.pair_mass_pmf_event,
    Lax342547.IndependentMixtures.independent_mixture_event p q p₀ q₀ w v hp hq]
  have hfin (jk : J × K) :
      (w jk.1 * v jk.2) * (independentPair (p jk.1) (q jk.2)).toOuterMeasure {ab | H ab.1 ab.2} ≠ ⊤ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (hw jk.1) (hv jk.2))
    rw [PMF.toOuterMeasure_apply]
    exact (independentPair (p jk.1) (q jk.2)).tsum_coe_indicator_ne_top _
  rw [ENNReal.toReal_sum (fun jk _ => hfin jk)]
  unfold average
  rw [Fintype.sum_prod_type]
  simp only [ENNReal.toReal_mul, ← Lax342547.PairRecovery.pair_mass_pmf_event]

/--
---
conclusion: Lax342547.LeafCollision.weighted_collision_lower
---
-/
theorem weighted_collision_lower {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hw : ∀ j, w j ≠ ⊤) (hv : ∀ k, v k ≠ ⊤)
    (hwsum : ∑ j, (w j).toReal = 1) (hvsum : ∑ k, (v k).toReal = 1)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (H : ΩA → ΩB → Prop) (overlap : J → K → ℝ) (keys error agreement : ℝ)
    (hbound : ∀ j k, agreement*(overlap j k-error)/keys ≤
      pairMass (weights (p j)) (weights (q k)) H) :
    agreement*(average (fun j => (w j).toReal) (fun k => (v k).toReal) overlap-error)/keys ≤
      pairMass (weights p₀) (weights q₀) H := by
  have h := Lax342547.ParameterCellAveraging.average_mono
    (fun j => (w j).toReal) (fun k => (v k).toReal) _ _
    (fun j => ENNReal.toReal_nonneg) (fun k => ENNReal.toReal_nonneg) hbound
  rw [← Lax342547.LeafCollision.real_pair_mixture p q p₀ q₀ w v hw hv hp hq H] at h
  have he : average (fun j => (w j).toReal) (fun k => (v k).toReal)
      (fun j k => agreement*(overlap j k-error)/keys) =
      agreement*(average (fun j => (w j).toReal) (fun k => (v k).toReal) overlap-error)/keys := by
    unfold average
    have hi (j : J) (k : K) :
        (w j).toReal*(v k).toReal*(agreement*(overlap j k-error)/keys) =
        (agreement*((w j).toReal*(v k).toReal*overlap j k) -
         agreement*error*((w j).toReal*(v k).toReal))/keys := by ring
    simp_rw [hi]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [hwsum, hvsum, mul_one]
    ring
  rwa [he] at h

/--
---
conclusion: Lax342547.LeafCollision.skipped_collision_bound
---
-/
theorem skipped_collision_bound {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (H : ΩA → ΩB → Prop)
    (use : Prop) (overlap keys error agreement : ℝ)
    (hkeys : 0 < keys) (herror : 0 ≤ error) (hagreement : 0 ≤ agreement)
    (hbound : use → agreement*(overlap-error)/keys ≤ pairMass (weights p) (weights q) H) : by
    classical
    exact agreement*((if use then overlap else 0)-error)/keys ≤ pairMass (weights p) (weights q) H := by
  classical
  by_cases hu : use
  · simpa [hu] using hbound hu
  · simp only [hu, if_false, zero_sub]
    have hn : agreement*(-error)/keys ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hagreement (neg_nonpos.mpr herror)) hkeys.le
    exact hn.trans (Lax342547.CellAveraging.pair_event_mass_nonneg
      (weights p) (weights q) H (Lax342547.RealCellLaws.weights_nonneg p)
      (Lax342547.RealCellLaws.weights_nonneg q))

/--
---
conclusion: Lax342547.LeafCollision.original_law_exponential_collision
---
-/
theorem original_law_exponential_collision {Ω J : Type} [Fintype Ω] [Fintype J]
    (σ : PMF Ω) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ σ.support)
    (p : J → PMF Ω) (w : J → ℝ≥0∞) (hw : ∀ j, w j ≠ ⊤)
    (hwsum : ∑ j, (w j).toReal = 1)
    (hp : ∀ a, (σ.filter S hS) a = ∑ j, w j * p j a)
    (H : Ω → Ω → Prop) (overlap : J → J → ℝ) (k η N keys error agreement : ℝ)
    (hkeys : 0 < keys) (hkeybound : keys ≤ (2:ℝ)^(k*N))
    (hoverlap : (2:ℝ)^(-η*N) ≤ average (fun j => (w j).toReal) (fun j => (w j).toReal) overlap)
    (herror : error ≤ (2:ℝ)^(-N/200)) (hscale : 1 ≤ (1/200-η)*N)
    (hagreement : (2:ℝ)^(-N/50) ≤ agreement)
    (hmass : (2:ℝ)^(-η*N) ≤ (σ.toOuterMeasure S).toReal)
    (hbound : ∀ j l, agreement*(overlap j l-error)/keys ≤ pairMass (weights (p j)) (weights (p l)) H) :
    (2:ℝ)^(-((k+1/50+3*η)*N)-1) ≤
      ((independentPair σ σ).toOuterMeasure {ab | H ab.1 ab.2}).toReal := by
  have havg := Lax342547.LeafCollision.weighted_collision_lower p p (σ.filter S hS) (σ.filter S hS)
    w w hw hw hwsum hwsum hp hp H overlap keys error agreement hbound
  have hrestricted := Lax342547.CollisionCosts.collision_exponential_lower
    k η N keys _ error agreement _ hkeys hkeybound hoverlap herror hscale hagreement havg
  have hrecovery := Lax342547.PairRecovery.restriction_pair_recovery σ S hS H
  have horiginal := Lax342547.CollisionCosts.restriction_exponential_lower
    k η N _ _ _ hmass hrestricted hrecovery
  rwa [Lax342547.PairRecovery.pair_mass_pmf_event] at horiginal

end Lax342547Proofs.LeafCollision
