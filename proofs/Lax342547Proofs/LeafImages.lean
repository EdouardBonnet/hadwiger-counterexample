import Lax342547.LeafImages
import Lax342547Proofs.ExactPins
import Lax342547Proofs.LeafExtraction

namespace Lax342547Proofs.LeafImages
open Lax342547.LeafImages

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafImages.image_pin_event
---
-/
theorem image_pin_event {Ω Axis I N : Type} {R : Axis → Type}
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (f : ∀ a, R a →ₗ[Binary] (I → Binary)) (o : Ω) :
    (imagePin A (fun a => LinearMap.range (f a)) o).event A =
      {ω | ∀ a, (A ω a).comp (f a) = (A o a).comp (f a)} := by
  ext ω
  constructor
  · intro h a
    apply LinearMap.ext
    intro v
    exact h a ⟨f a v, LinearMap.mem_range_self _ _⟩
  · intro h a v
    obtain ⟨u, hu⟩ := v.property
    change A ω a v.val = A o a v.val
    rw [← hu]
    exact LinearMap.congr_fun (h a) u

/--
---
conclusion: Lax342547.LeafImages.image_pin_relative_rank
---
-/
theorem image_pin_relative_rank {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)] [∀ a, FiniteDimensional Binary (R a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (f : ∀ a, R a →ₗ[Binary] (I → Binary))
    (hf : ∀ a, Function.Injective ((P.space a).mkQ.comp (f a))) (o : Ω) :
    P.relativeRank (imagePin A (fun a => LinearMap.range (f a)) o) =
      ∑ a, Module.finrank Binary (R a) := by
  unfold Pin.relativeRank imagePin Pin.space
  apply Finset.sum_congr rfl
  intro a _
  rw [← LinearMap.range_comp]
  exact LinearMap.finrank_range_of_inj (hf a)

/--
---
conclusion: Lax342547.LeafImages.leaf_tuple_image_cap
---
-/
theorem leaf_tuple_image_cap {Ω Axis I N : Type} {R : Axis → Type}
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
      α ^ (∑ a, Module.finrank Binary (R a)) := by
  classical
  by_cases he : ∃ o, ∀ a, (A o a).comp (f a) = y a
  · obtain ⟨o, ho⟩ := he
    have hs : {ω | ∀ a, (A ω a).comp (f a) = y a} =
        (imagePin A (fun a => LinearMap.range (f a)) o).event A := by
      rw [image_pin_event]
      simp only [ho]
    rw [hs]
    have hrank := image_pin_relative_rank A P f hf o
    have h := hcap (imagePin A (fun a => LinearMap.range (f a)) o) (by rw [hrank]; exact hr)
    rwa [hrank] at h
  · have hs : {ω | ∀ a, (A ω a).comp (f a) = y a} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => he ⟨ω, h⟩
    rw [hs]
    simp

end Lax342547Proofs.LeafImages
