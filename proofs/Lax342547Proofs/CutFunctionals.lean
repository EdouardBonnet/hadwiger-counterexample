import Lax342547.CutFunctionals
import Lax342547Proofs.CutProfiles
import Mathlib.LinearAlgebra.Isomorphisms
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.CutFunctionals

open Lax342547.MomentSpace Lax342547.CutProfiles

variable {Tag V : Type} [Fintype Tag] [DecidableEq Tag] [Nonempty Tag]
variable [AddCommGroup V] [Module Binary V]

theorem eq_of_add_eq_zero {x y : Binary} (h : x + y = 0) : x = y := by
  have : x = -y := eq_neg_of_add_eq_zero_left h
  simpa [ZModModule.neg_eq_self] using this

/--
---
conclusion: Lax342547.CutFunctionals.representative_sums_eq
---
The difference of the representatives is a common kernel constant.
The ordinary tester kills it. The other tester contributes an even
number of equal binary values after omitting one of the odd number of tags.
-/
theorem representative_sums_eq
    (W : Tag → Submodule Binary V) (ηO ηS : V →ₗ[Binary] Binary)
    (hO : ∀ c ∈ ⨅ t, W t, ηO c = 0) (hodd : Odd (Fintype.card Tag))
    (w v : Tag → V) (hw : ∀ t, w t ∈ W t) (hv : ∀ t, v t ∈ W t)
    (heq : cutMap w = cutMap v) :
    (∑ t, ηO (w t)) = (∑ t, ηO (v t)) ∧
      ∀ t, (∑ l ∈ Finset.univ.erase t, ηS (w l)) =
        ∑ l ∈ Finset.univ.erase t, ηS (v l) := by
  obtain ⟨c, hc, hconst⟩ := (CutProfiles.same_cut_iff W w v hw hv).mp heq
  constructor
  · apply Finset.sum_congr rfl
    intro t _
    apply eq_of_add_eq_zero
    rw [← map_add, hconst t, hO c hc]
  · intro t
    apply eq_of_add_eq_zero
    rw [← Finset.sum_add_distrib]
    simp_rw [← map_add, hconst]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ]
    obtain ⟨k, hk⟩ := hodd
    rw [show Fintype.card Tag - 1 = 2 * k from by omega, mul_nsmul, two_nsmul,
      ZModModule.add_self, nsmul_zero]

/-- A linear functional annihilating a map's kernel descends to its actual image. -/
noncomputable def descend {R X Y : Type} [Field R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (a : X →ₗ[R] R)
    (h : LinearMap.ker f ≤ LinearMap.ker a) : LinearMap.range f →ₗ[R] R :=
  ((LinearMap.ker f).liftQ a h).comp f.quotKerEquivRange.symm.toLinearMap

theorem descend_apply {R X Y : Type} [Field R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (a : X →ₗ[R] R)
    (h : LinearMap.ker f ≤ LinearMap.ker a) (x : X) :
    descend f a h (f.rangeRestrict x) = a x := by
  change (LinearMap.ker f).liftQ a h
    (f.quotKerEquivRange.symm ⟨f x, LinearMap.mem_range_self f x⟩) = a x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Lax342547Proofs.CutFunctionals
