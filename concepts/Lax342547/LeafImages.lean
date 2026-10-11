import Lax342547.ExactPins
import Lax342547.LeafExtraction

/-!
---
title: All-rank tuple image caps from exact-pin leaf entropy
type: lemma
---
A tuple independent modulo the actual old pin defines an exact image pin of its full relative rank. The checked leaf cap therefore bounds any specified joint tuple image, uniformly over every tuple rank.
-/

namespace Lax342547.LeafImages

open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

noncomputable def imagePin {Ω Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (S : Axis → Submodule Binary (I → Binary)) (o : Ω) : Pin Axis I N :=
  ⟨S, fun a => (A o a).comp (S a).subtype⟩

axiom image_pin_event {Ω Axis I N : Type} {R : Axis → Type}
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (f : ∀ a, R a →ₗ[Binary] (I → Binary)) (o : Ω) :
    (imagePin A (fun a => LinearMap.range (f a)) o).event A =
      {ω | ∀ a, (A ω a).comp (f a) = (A o a).comp (f a)}

axiom image_pin_relative_rank {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)] [∀ a, FiniteDimensional Binary (R a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (f : ∀ a, R a →ₗ[Binary] (I → Binary))
    (hf : ∀ a, Function.Injective ((P.space a).mkQ.comp (f a))) (o : Ω) :
    P.relativeRank (imagePin A (fun a => LinearMap.range (f a)) o) =
      ∑ a, Module.finrank Binary (R a)

axiom leaf_tuple_image_cap {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)] [∀ a, FiniteDimensional Binary (R a)]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (f : ∀ a, R a →ₗ[Binary] (I → Binary))
    (hf : ∀ a, Function.Injective ((P.space a).mkQ.comp (f a)))
    (y : ∀ a, R a →ₗ[Binary] (N → Binary)) (α : ℝ≥0∞)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q))
    (hr : 1 ≤ ∑ a, Module.finrank Binary (R a)) :
    p.toOuterMeasure {ω | ∀ a, (A ω a).comp (f a) = y a} ≤
      α ^ (∑ a, Module.finrank Binary (R a))

end Lax342547.LeafImages
