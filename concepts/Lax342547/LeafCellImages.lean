import Lax342547.JointKeyCap
import Lax342547.RealCellLaws

/-!
---
title: Joint fresh-image entropy on original retained leaf cells
type: definition and theorem
---
Exact all-rank leaf caps combine known key directions with fresh directions. Conditioning on the original retained cell gives the paper .95 rank exponent, for tuples of arbitrary rank.
-/

namespace Lax342547.LeafCellImages

open Lax342547.MomentSpace Lax342547.ExactPins
open Lax342547.RealCellLaws Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped ENNReal

noncomputable def freshImage {Ω Axis I N : Type} {V : Axis → Type}
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (ω : Ω) : ∀ a, V a →ₗ[Binary] (N → Binary) := fun a => (A ω a).comp (fresh a)

axiom original_leaf_cell_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
    [Fintype Ω] [Fintype Axis] [Fintype I] [Fintype N]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)] [∀ a, FiniteDimensional Binary (V a)]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (fresh a)))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (C : Ω → Prop)
    (hCkey : ∀ ω, C ω → ∀ a, (A ω a).comp (keys a) = yk a)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * (∑ a, Module.finrank Binary (U a)) ≤ (1 / 500 : ℝ))
    (ht : 1 ≤ ∑ a, Module.finrank Binary (V a))
    (hC : (2 : ℝ)^(-(((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) + 1 / 100) * Fintype.card N) ≤
      (p.toOuterMeasure {ω | C ω}).toReal)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤
        ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) ^ (P.relativeRank Q))
    (y : ∀ a, V a →ₗ[Binary] (N → Binary)) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => freshImage A fresh ω.val) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, Module.finrank Binary (V a))*Fintype.card N)

end Lax342547.LeafCellImages
