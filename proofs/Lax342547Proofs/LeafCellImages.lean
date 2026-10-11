import Lax342547.LeafCellImages
import Lax342547.JointKeyCap
import Lax342547.RealCellLaws

namespace Lax342547Proofs.LeafCellImages
open Lax342547.LeafCellImages

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ExactPins
open Lax342547.RealCellLaws Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafCellImages.original_leaf_cell_image_cap
---
-/
theorem original_leaf_cell_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
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
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, Module.finrank Binary (V a))*Fintype.card N) := by
  classical
  apply Lax342547.RealCellLaws.pmf_paper_subtype_cap p C (freshImage A fresh)
    (fun ω => ∀ a, (A ω a).comp (keys a) = yk a) ζ
    ((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) ((∑ a, Module.finrank Binary (V a) : ℕ) : ℝ) (Fintype.card N)
    hζ hζsmall hk (by exact_mod_cast ht) (by positivity) hC hCkey
  intro z
  have h := Lax342547.JointKeyCap.leaf_key_fresh_image_cap p A P keys fresh hkeys hfresh yk z
    ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) hcap (by omega)
  have hm : p.toOuterMeasure {ω | (∀ a, (A ω a).comp (keys a) = yk a) ∧ freshImage A fresh ω = z} ≤
      p.toOuterMeasure {ω | ∀ a, (A ω a).comp (keys a) = yk a ∧ (A ω a).comp (fresh a) = z a} := by
    apply p.toOuterMeasure.mono
    intro ω hω a
    exact ⟨hω.1 a, congrFun hω.2 a⟩
  apply hm.trans
  have he : ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) ^
      ((∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a)) =
      (2 : ℝ≥0∞)^(-(1 - 2 * ζ) *
        (((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) + ((∑ a, Module.finrank Binary (V a) : ℕ) : ℝ)) * Fintype.card N) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_add]
    congr 1
    ring
  rw [he] at h
  exact h

end Lax342547Proofs.LeafCellImages
