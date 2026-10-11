import Lax342547.LeafCellImages
import Lax342547.ComponentCharacters
import Lax342547.PairedFrames

/-!
---
title: Joint matrix-image caps for retained leaf laws
type: lemma
---
Joint fresh linear images flatten to the rank-factor matrix tuples used by Walsh characters. Exact leaf caps give all-rank component image bounds on original retained cells, including the rank-zero normalization case.
-/

namespace Lax342547.LeafBlockCaps

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.PushforwardWalsh
open Lax342547.RealCellLaws Lax342547.LeafCellImages Lax342547.ComponentCharacters
open Lax342547.CoefficientPhase
open scoped ENNReal

noncomputable def decodedImages {Axis N : Type} {R : Axis → Type} [∀ _a, Fintype (R _a)]
    (y : ((Σ a, R a) × N) → Binary) : ∀ a, (R a → Binary) →ₗ[Binary] (N → Binary) :=
  fun a => Matrix.mulVecLin (fun n i => y (⟨a,i⟩,n))

axiom block_image_fiber {Axis I N : Type} {R : Axis → Type}
    [Fintype I] [Fintype N] [∀ _a, Fintype (R _a)]
    (F : ∀ a, Matrix I (R a) Binary) (X : ∀ _a, Matrix N I Binary)
    (y : ((Σ a, R a) × N) → Binary) : by
      classical
      exact blockImage F X = y ↔ ∀ a, (X a).mulVecLin.comp (F a).mulVecLin = decodedImages y a

axiom block_image_push {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Ω] [Fintype I] [Fintype N] [∀ _a, Fintype (R _a)]
    (ρ : Ω → ℝ) (F : ∀ a, Matrix I (R a) Binary) (X : Ω → ∀ _a, Matrix N I Binary)
    (y : ((Σ a, R a) × N) → Binary) : by
      classical
      exact push ρ (fun ω => blockImage F (X ω)) y =
        push ρ (freshImage (fun ω a => (X ω a).mulVecLin) (fun a => (F a).mulVecLin))
          (decodedImages y)

axiom original_leaf_block_cap {Ω Axis I N : Type} {U : Axis → Type}
    [Fintype Ω] [Fintype Axis] [Fintype I] [Fintype N]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (p : PMF Ω) (X : Ω → Axis → Matrix N I Binary)
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (r : Axis → ℕ) (F : ∀ a, Matrix I (Fin (r a)) Binary)
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (F a).mulVecLin))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (C : Ω → Prop)
    (hCkey : ∀ ω, C ω → ∀ a, (X ω a).mulVecLin.comp (keys a) = yk a)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * (∑ a, Module.finrank Binary (U a)) ≤ (1 / 500 : ℝ))
    (ht : 1 ≤ ∑ a, r a)
    (hC : (2 : ℝ)^(-(((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) + 1 / 100) * Fintype.card N) ≤
      (p.toOuterMeasure {ω | C ω}).toReal)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event (fun ω a => (X ω a).mulVecLin)) ≤
        ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) ^ (P.relativeRank Q))
    (y : ((Σ a, Fin (r a)) × N) → Binary) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => blockImage F (X ω.val)) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, r a)*Fintype.card N)

axiom original_leaf_all_rank_block_cap {Ω Axis I N : Type} {U : Axis → Type}
    [Fintype Ω] [Fintype Axis] [Fintype I] [Fintype N]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    (p : PMF Ω) (X : Ω → Axis → Matrix N I Binary)
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (r : Axis → ℕ) (F : ∀ a, Matrix I (Fin (r a)) Binary)
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (F a).mulVecLin))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (C : Ω → Prop)
    (hCkey : ∀ ω, C ω → ∀ a, (X ω a).mulVecLin.comp (keys a) = yk a)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * (∑ a, Module.finrank Binary (U a)) ≤ (1 / 500 : ℝ))
    (hC : (2 : ℝ)^(-(((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) + 1 / 100) * Fintype.card N) ≤
      (p.toOuterMeasure {ω | C ω}).toReal)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event (fun ω a => (X ω a).mulVecLin)) ≤
        ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) ^ (P.relativeRank Q))
    (y : ((Σ a, Fin (r a)) × N) → Binary) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => blockImage F (X ω.val)) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, r a)*Fintype.card N)

end Lax342547.LeafBlockCaps
