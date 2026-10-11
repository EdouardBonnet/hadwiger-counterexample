import Lax342547.QuotientExtractors
import Lax342547.PinLabelExclusions

namespace Lax342547Proofs.QuotientExtractors

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.PinLabelExclusions Lax342547.QuotientExtractors

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.QuotientExtractors.quotient_factor
---
Choose a linear section onto the image of the quotient composite. The
kernel condition makes the prescribed output independent of that section.
Extend from the image to the whole quotient vector space.
-/
theorem quotient_factor {C V W : Type}
    [AddCommGroup C] [Module Binary C] [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] (D : Submodule Binary V)
    (f : C →ₗ[Binary] V) (g : C →ₗ[Binary] W)
    (h : ∀ c, f c ∈ D → g c = 0) :
    ∃ q : (V ⧸ D) →ₗ[Binary] W, q.comp (D.mkQ.comp f) = g := by
  let fbar := D.mkQ.comp f
  obtain ⟨lift, hlift⟩ := fbar.rangeRestrict.exists_rightInverse_of_surjective
    fbar.range_rangeRestrict
  obtain ⟨q, hq⟩ := (g.comp lift).exists_extend
  refine ⟨q, LinearMap.ext fun c => ?_⟩
  have he : fbar (lift (fbar.rangeRestrict c)) = fbar c :=
    congrArg Subtype.val (LinearMap.congr_fun hlift (fbar.rangeRestrict c))
  have hmem : f (lift (fbar.rangeRestrict c) - c) ∈ D := by
    apply (Submodule.Quotient.mk_eq_zero D).mp
    change fbar (lift (fbar.rangeRestrict c) - c) = 0
    rw [map_sub, he, sub_self]
  have hg := h (lift (fbar.rangeRestrict c) - c) hmem
  rw [map_sub, sub_eq_zero] at hg
  have hqc := LinearMap.congr_fun hq (fbar.rangeRestrict c)
  exact hqc.trans hg

/--
---
conclusion: Lax342547.QuotientExtractors.pin_extractor
---
On the finite label-coefficient space, a sum lying in the pin has zero
coefficient at the fresh label. Factor its coordinate projection through
the pin quotient and evaluate it on coefficient vectors supported at one label.
-/
theorem pin_extractor {Base Comp H N : Type} {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R + 14) (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i) :
    ∃ q : ((SelectorCoordinates b degree × Option Base → Binary) ⧸ projected P i a) →ₗ[Binary]
        (Option Base → Binary),
      ∀ t ∈ L, ∀ v : Option Base → Binary,
        q ((projected P i a).mkQ (Lax342547.SparsePins.labelTensor
          (selectorEval (degree := degree)) t v)) = if t = s then v else 0 := by
  classical
  let f : (L → Option Base → Binary) →ₗ[Binary]
      (SelectorCoordinates b degree × Option Base → Binary) :=
    ∑ t : L, (Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t.val).comp
      (LinearMap.proj t)
  have hker (c : L → Option Base → Binary) (hc : f c ∈ projected P i a) : c ⟨s, hs⟩ = 0 := by
    let v := Function.extend Subtype.val c 0
    have hv (t : L) : v t.val = c t := Subtype.val_injective.extend_apply c 0 t
    have hm : (∑ t ∈ L, Lax342547.SparsePins.labelTensor
        (selectorEval (degree := degree)) t (v t)) ∈ projected P i a := by
      rw [← Finset.sum_coe_sort L]
      simpa only [f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, hv] using hc
    have hz := Lax342547.PinLabelExclusions.fresh_coefficient P A hA i a L v hL hm s hs hfresh
    simpa only [hv ⟨s, hs⟩] using hz
  obtain ⟨q, hq⟩ := Lax342547.QuotientExtractors.quotient_factor (projected P i a) f (LinearMap.proj (⟨s, hs⟩ : L)) hker
  refine ⟨q, ?_⟩
  intro t ht v
  have he : f (Pi.single ⟨t, ht⟩ v) =
      Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t v := by
    simp only [f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single (⟨t, ht⟩ : L)]
    · simp
    · intro u _ hut
      rw [Pi.single_eq_of_ne hut, map_zero]
    · simp
  have hqv := LinearMap.congr_fun hq (Pi.single ⟨t, ht⟩ v)
  simpa only [LinearMap.comp_apply, he, LinearMap.proj_apply,
    Pi.single_apply, Subtype.ext_iff, eq_comm] using hqv

/--
---
conclusion: Lax342547.QuotientExtractors.key_extractor
---
The pin extractor sends each selected key to zero or to the selected
base ray. Quotient its output by that ray, so it kills both the pin and
the full key span and descends through their sum.
-/
theorem key_extractor {Base Comp H N I : Type} {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R + 14) (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i)
    (label : I → Fin b → Binary) (base : I → Option Base → Binary)
    (hlabels : ∀ j, label j ∈ L) (Ray : Submodule Binary (Option Base → Binary))
    (hmatch : ∀ j, label j = s → base j ∈ Ray) :
    ∃ q : ((SelectorCoordinates b degree × Option Base → Binary) ⧸
        (projected P i a ⊔ Submodule.span Binary
          (Set.range (fun j => Lax342547.SparsePins.labelTensor
            (selectorEval (degree := degree)) (label j) (base j))))) →ₗ[Binary]
        ((Option Base → Binary) ⧸ Ray),
      ∀ t ∈ L, ∀ v : Option Base → Binary,
        q (Submodule.Quotient.mk (Lax342547.SparsePins.labelTensor
          (selectorEval (degree := degree)) t v)) = if t = s then Ray.mkQ v else 0 := by
  classical
  obtain ⟨qpin, hqpin⟩ := Lax342547.QuotientExtractors.pin_extractor P A hA i a L hL s hs hfresh
  let f := (Ray.mkQ.comp qpin).comp (projected P i a).mkQ
  have hker : projected P i a ⊔ Submodule.span Binary
      (Set.range (fun j => Lax342547.SparsePins.labelTensor
        (selectorEval (degree := degree)) (label j) (base j))) ≤ LinearMap.ker f := by
    apply sup_le
    · intro v hv
      change Ray.mkQ (qpin ((projected P i a).mkQ v)) = 0
      have hz : (projected P i a).mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
      rw [hz, map_zero, map_zero]
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change Ray.mkQ (qpin ((projected P i a).mkQ
        (Lax342547.SparsePins.labelTensor (selectorEval (degree := degree))
          (label j) (base j)))) = 0
      rw [hqpin (label j) (hlabels j)]
      by_cases hj : label j = s
      · rw [if_pos hj]
        exact (Submodule.Quotient.mk_eq_zero Ray).mpr (hmatch j hj)
      · rw [if_neg hj, map_zero]
  refine ⟨(projected P i a ⊔ Submodule.span Binary
    (Set.range (fun j => Lax342547.SparsePins.labelTensor
      (selectorEval (degree := degree)) (label j) (base j)))).liftQ f hker, ?_⟩
  intro t ht v
  change Ray.mkQ (qpin ((projected P i a).mkQ
    (Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t v))) = _
  rw [hqpin t ht]
  by_cases hts : t = s <;> simp [hts]

end Lax342547Proofs.QuotientExtractors
