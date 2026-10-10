import Lax342547.JointDirections

/-!
---
title: Exact leaf entropy bounds joint key and additional images
type: definition and theorem
---
The full key plus additional tuple has the sum of the two ranks. Applying the actual old-pin leaf cap before any cell conditioning bounds every specified joint image event.
-/

namespace Lax342547.JointKeyCap

open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

axiom leaf_key_fresh_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
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
      α ^ ((∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a))

end Lax342547.JointKeyCap
