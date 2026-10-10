import Lax342547.FrozenBaselines

namespace Lax342547Proofs.FrozenBaselines

open Lax342547.MomentSpace Lax342547.FrozenBaselines

variable {V W : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W]

/--
---
conclusion: Lax342547.FrozenBaselines.splitting_exists
---
The sum map from the table space and key space is injective, so choose a
linear left inverse. Within the table choose a retraction to the stored
pins. Their composite supplies the frozen part; subtracting it from the
table retraction supplies the complementary part.
-/
theorem splitting_exists (J D Keys : Submodule Binary V) (hD : D ≤ J)
    (hKeys : Disjoint J Keys) : Nonempty (Splitting J D Keys) := by
  let incl : J × Keys →ₗ[Binary] V := J.subtype.coprod Keys.subtype
  have hker : LinearMap.ker incl = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range]
    · simp
    · simpa only [Submodule.range_subtype] using hKeys
  obtain ⟨r, hr⟩ := incl.exists_leftInverse_of_injective hker
  obtain ⟨d, hd⟩ := (Submodule.inclusion hD).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective hD))
  let j : V →ₗ[Binary] J := (LinearMap.fst Binary J Keys).comp r
  let q : V →ₗ[Binary] Keys := (LinearMap.snd Binary J Keys).comp r
  have hrJ (v : J) : r v.val = (v, 0) := by
    simpa [incl] using DFunLike.congr_fun hr (v, 0)
  have hrK (v : Keys) : r v.val = (0, v) := by
    simpa [incl] using DFunLike.congr_fun hr (0, v)
  have hdD (v : D) : d (Submodule.inclusion hD v) = v := DFunLike.congr_fun hd v
  let f : V →ₗ[Binary] V := (D.subtype.comp d).comp j + Keys.subtype.comp q
  let c : V →ₗ[Binary] J := j - ((Submodule.inclusion hD).comp d).comp j
  have hfD (v : D) : f v.val = v.val := by
    simp only [f, LinearMap.add_apply, LinearMap.comp_apply, j, q, hrJ ⟨v.val, hD v.property⟩,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, add_zero]
    change (d (Submodule.inclusion hD v)).val = v.val
    rw [hdD]
  have hcD (v : D) : c v.val = 0 := by
    simp only [c, LinearMap.sub_apply, LinearMap.comp_apply, j, hrJ ⟨v.val, hD v.property⟩,
      LinearMap.fst_apply]
    change Submodule.inclusion hD v - Submodule.inclusion hD (d (Submodule.inclusion hD v)) = 0
    rw [hdD, sub_self]
  have hfK (v : Keys) : f v.val = v.val := by simp [f, j, q, hrK]
  have hcK (v : Keys) : c v.val = 0 := by simp [c, j, hrK]
  refine ⟨⟨f, c, ?_, ?_, ?_, ?_⟩⟩
  · intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfD ⟨x, hx⟩, hfK ⟨y, hy⟩]
  · intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hcD ⟨x, hx⟩, hcK ⟨y, hy⟩, add_zero]
  · intro v
    simp [f, j, q, hrJ]
  · intro v
    simp [f, c, j, q, hrJ]

theorem baseline_apply {J D Keys : Submodule Binary V} {J' D' Keys' : Submodule Binary W}
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (v : V) (w : W) :
    baseline S S' A T v w = A (S.frozen v) w + A v (S'.frozen w) -
      A (S.frozen v) (S'.frozen w) + T (S.table v) (S'.table w) := rfl

/--
---
conclusion: Lax342547.FrozenBaselines.baseline_properties
---
In a frozen row or column the complementary table part vanishes and the
two repeated actual terms cancel. On the table product, expand each
argument into its pin and complementary parts. Compatibility identifies
every term containing a pin with its actual value.
-/
theorem baseline_properties (J D Keys : Submodule Binary V) (J' D' Keys' : Submodule Binary W)
    (hD : D ≤ J) (hD' : D' ≤ J')
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (h : Compatible J D J' D' A T) :
    ExtendsFrozen D Keys D' Keys' A (baseline S S' A T) ∧
      ∀ v : J, ∀ w : J', baseline S S' A T v.val w.val = T v w := by
  constructor
  · intro v w hvw
    rcases hvw with hv | hw
    · rw [baseline_apply, S.frozen_fixed v hv, S.table_zero v hv]
      simp
    · rw [baseline_apply, S'.frozen_fixed w hw, S'.table_zero w hw]
      simp
  · intro v w
    let dv : J := ⟨S.frozen v.val, hD (S.frozen_table v)⟩
    let dw : J' := ⟨S'.frozen w.val, hD' (S'.frozen_table w)⟩
    have hv : dv + S.table v.val = v := Subtype.ext (S.table_sum v)
    have hw : dw + S'.table w.val = w := Subtype.ext (S'.table_sum w)
    have hfirst : T dv w = A (S.frozen v.val) w.val := h dv w (Or.inl (S.frozen_table v))
    have hsecond : T (S.table v.val) dw = A (S.table v.val).val (S'.frozen w.val) :=
      h (S.table v.val) dw (Or.inr (S'.frozen_table w))
    have hT : T v w = A (S.frozen v.val) w.val +
        A (S.table v.val).val (S'.frozen w.val) + T (S.table v.val) (S'.table w.val) := by
      calc
        _ = T (dv + S.table v.val) w := congrArg (fun t => T t w) hv.symm
        _ = T dv w + T (S.table v.val) w := by rw [map_add, LinearMap.add_apply]
        _ = A (S.frozen v.val) w.val +
            (T (S.table v.val) dw + T (S.table v.val) (S'.table w.val)) := by
          rw [hfirst, ← (T (S.table v.val)).map_add, hw]
        _ = _ := by rw [hsecond]; abel
    have hA : A v.val (S'.frozen w.val) = A (S.frozen v.val) (S'.frozen w.val) +
        A (S.table v.val).val (S'.frozen w.val) := by
      calc
        _ = A (S.frozen v.val + (S.table v.val).val) (S'.frozen w.val) :=
          congrArg (fun t => A t (S'.frozen w.val)) (S.table_sum v).symm
        _ = _ := by rw [map_add, LinearMap.add_apply]
    rw [baseline_apply, hT, hA]
    abel

end Lax342547Proofs.FrozenBaselines
