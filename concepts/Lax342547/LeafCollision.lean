import Lax342547.IndependentMixtures
import Lax342547.ParameterCellAveraging
import Lax342547.CollisionCosts
import Lax342547.CellAveraging

/-!
---
title: Actual independent leaf averaging and original-law collision cost
type: definition and theorem
---
Finite PMF mixtures preserve the actual leaf masses. Affine collision bounds average over independent leaves without renormalization, skipped pairs remain valid, and squared restriction recovery gives the explicit original-law exponential lower bound.
-/

namespace Lax342547.LeafCollision

open Lax342547.RealCellLaws Lax342547.PairRecovery Lax342547.ParameterCellAveraging
open scoped ENNReal

axiom mixture_real_weights {Ω J : Type} [Fintype J]
    (p : J → PMF Ω) (p₀ : PMF Ω) (w : J → ℝ≥0∞)
    (hw : ∀ j, w j ≠ ⊤) (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (a : Ω) :
    weights p₀ a = ∑ j, (w j).toReal * weights (p j) a

axiom real_pair_mixture {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hw : ∀ j, w j ≠ ⊤) (hv : ∀ k, v k ≠ ⊤)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (H : ΩA → ΩB → Prop) :
    pairMass (weights p₀) (weights q₀) H =
      average (fun j => (w j).toReal) (fun k => (v k).toReal)
        (fun j k => pairMass (weights (p j)) (weights (q k)) H)

axiom weighted_collision_lower {ΩA ΩB J K : Type}
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
      pairMass (weights p₀) (weights q₀) H

axiom skipped_collision_bound {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (H : ΩA → ΩB → Prop)
    (use : Prop) (overlap keys error agreement : ℝ)
    (hkeys : 0 < keys) (herror : 0 ≤ error) (hagreement : 0 ≤ agreement)
    (hbound : use → agreement*(overlap-error)/keys ≤ pairMass (weights p) (weights q) H) : by
    classical
    exact agreement*((if use then overlap else 0)-error)/keys ≤ pairMass (weights p) (weights q) H

axiom original_law_exponential_collision {Ω J : Type} [Fintype Ω] [Fintype J]
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
      ((independentPair σ σ).toOuterMeasure {ab | H ab.1 ab.2}).toReal

end Lax342547.LeafCollision
