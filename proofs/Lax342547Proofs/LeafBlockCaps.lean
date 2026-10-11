import Lax342547.LeafBlockCaps
import Lax342547Proofs.PairedFrames
import Lax342547.LeafCellImages
import Lax342547.RealCellLaws

namespace Lax342547Proofs.LeafBlockCaps
open Lax342547.LeafBlockCaps

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.PushforwardWalsh
open Lax342547.RealCellLaws Lax342547.LeafCellImages Lax342547.ComponentCharacters
open Lax342547.CoefficientPhase
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafBlockCaps.block_image_fiber
---
-/
theorem block_image_fiber {Axis I N : Type} {R : Axis → Type}
    [Fintype I] [Fintype N] [∀ _a, Fintype (R _a)]
    (F : ∀ a, Matrix I (R a) Binary) (X : ∀ _a, Matrix N I Binary)
    (y : ((Σ a, R a) × N) → Binary) : by
      classical
      exact blockImage F X = y ↔ ∀ a, (X a).mulVecLin.comp (F a).mulVecLin = decodedImages y a := by
  classical
  constructor
  · intro h a
    rw [← Matrix.mulVecLin_mul]
    unfold decodedImages
    apply congrArg Matrix.mulVecLin
    ext n i
    exact congrFun h (⟨a,i⟩,n)
  · intro h
    funext v
    have ht := congrArg LinearMap.toMatrix' (h v.1.1)
    rw [← Matrix.mulVecLin_mul,
      Lax342547Proofs.PairedFrames.toMatrix_mulVecLin] at ht
    unfold decodedImages at ht
    rw [Lax342547Proofs.PairedFrames.toMatrix_mulVecLin] at ht
    exact congrFun (congrFun ht v.2) v.1.2

/--
---
conclusion: Lax342547.LeafBlockCaps.block_image_push
---
-/
theorem block_image_push {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Ω] [Fintype I] [Fintype N] [∀ _a, Fintype (R _a)]
    (ρ : Ω → ℝ) (F : ∀ a, Matrix I (R a) Binary) (X : Ω → ∀ _a, Matrix N I Binary)
    (y : ((Σ a, R a) × N) → Binary) : by
      classical
      exact push ρ (fun ω => blockImage F (X ω)) y =
        push ρ (freshImage (fun ω a => (X ω a).mulVecLin) (fun a => (F a).mulVecLin))
          (decodedImages y) := by
  classical
  unfold push
  apply Finset.sum_congr rfl
  intro ω _
  have he : blockImage F (X ω) = y ↔
      freshImage (fun ω a => (X ω a).mulVecLin) (fun a => (F a).mulVecLin) ω = decodedImages y := by
    rw [Lax342547.LeafBlockCaps.block_image_fiber]
    exact funext_iff.symm
  simp only [he]

/--
---
conclusion: Lax342547.LeafBlockCaps.original_leaf_block_cap
---
-/
theorem original_leaf_block_cap {Ω Axis I N : Type} {U : Axis → Type}
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
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, r a)*Fintype.card N) := by
  classical
  rw [Lax342547.LeafBlockCaps.block_image_push]
  have hrank : ∀ a, Module.finrank Binary (Fin (r a) → Binary) = r a := by
    intro a
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  have h := Lax342547.LeafCellImages.original_leaf_cell_image_cap p
    (fun ω a => (X ω a).mulVecLin) P keys (fun a => (F a).mulVecLin)
    hkeys hfresh yk C hCkey ζ hζ hζsmall hk
    (by simpa only [hrank] using ht) hC hcap (decodedImages y)
  simp only [hrank] at h
  unfold freshImage at h ⊢
  exact h

/--
---
conclusion: Lax342547.LeafBlockCaps.original_leaf_all_rank_block_cap
---
-/
theorem original_leaf_all_rank_block_cap {Ω Axis I N : Type} {U : Axis → Type}
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
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, r a)*Fintype.card N) := by
  classical
  by_cases hz : (∑ a, r a) = 0
  · have hm : 0 < Lax342547.RetainedImages.cellMass (weights p) C := by
      rw [Lax342547.RealCellLaws.event_mass]
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hC
    have h : push (subtypeWeights (weights p) C) (fun ω => blockImage F (X ω.val)) y ≤
        ∑ ω, subtypeWeights (weights p) C ω := by
      unfold push
      apply Finset.sum_le_sum
      intro ω _
      split_ifs
      · exact le_rfl
      · exact Lax342547.RealCellLaws.subtype_weights_nonneg (weights p) C
          (Lax342547.RealCellLaws.weights_nonneg p) hm ω
    rw [Lax342547.RealCellLaws.subtype_weights_total (weights p) C hm] at h
    simpa only [hz, Nat.cast_zero, mul_zero, zero_mul, Real.rpow_zero] using h
  · exact Lax342547.LeafBlockCaps.original_leaf_block_cap p X P keys r F hkeys hfresh yk C hCkey ζ hζ hζsmall hk
      (Nat.one_le_iff_ne_zero.mpr hz) hC hcap y

end Lax342547Proofs.LeafBlockCaps
