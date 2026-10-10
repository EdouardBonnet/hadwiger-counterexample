import Lax342547.JointKeyCap
import Lax342547Proofs.JointDirections

namespace Lax342547Proofs.JointKeyCap
open Lax342547.JointKeyCap

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

/--
---
conclusion: Lax342547.JointKeyCap.leaf_key_fresh_image_cap
---
-/
theorem leaf_key_fresh_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)] [∀ a, FiniteDimensional Binary (V a)]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (fresh a)))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (yf : ∀ a, V a →ₗ[Binary] (N → Binary))
    (α : ℝ≥0∞)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q))
    (hr : 1 ≤ (∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a)) :
    p.toOuterMeasure {ω | ∀ a, (A ω a).comp (keys a) = yk a ∧ (A ω a).comp (fresh a) = yf a} ≤
      α ^ ((∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a)) := by
  have he : {ω | ∀ a, (A ω a).comp (keys a) = yk a ∧ (A ω a).comp (fresh a) = yf a} =
      {ω | ∀ a, (A ω a).comp ((keys a).coprod (fresh a)) = (yk a).coprod (yf a)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, LinearMap.comp_coprod, LinearMap.prod_ext_iff,
      LinearMap.coprod_inl, LinearMap.coprod_inr]
  rw [he]
  have h := Lax342547Proofs.LeafImages.leaf_tuple_image_cap p A P
    (fun a => (keys a).coprod (fresh a))
    (fun a => Lax342547Proofs.JointDirections.appended_quotient_injective (P.space a) (keys a) (fresh a) (hkeys a) (hfresh a))
    (fun a => (yk a).coprod (yf a)) α hcap
    (by simpa only [Module.finrank_prod, Finset.sum_add_distrib] using hr)
  simpa only [Module.finrank_prod, Finset.sum_add_distrib] using h

end Lax342547Proofs.JointKeyCap
