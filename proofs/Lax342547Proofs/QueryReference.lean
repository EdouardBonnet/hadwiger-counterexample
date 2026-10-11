import Lax342547.QueryReference
import Lax342547.QuerySlots
import Lax342547.ReferenceKeys

namespace Lax342547Proofs.QueryReference
open Lax342547.QueryReference

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.QuerySlots Lax342547.ReferenceKeys
open Lax342547.ConcreteGeometry
open scoped ENNReal

/--
---
conclusion: Lax342547.QueryReference.tuple_equality_matched_keys
---
-/
theorem tuple_equality_matched_keys {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (oA oB : Unit (H := H) (N := N) (E := E))
    (h : leftTuple W oA = rightTuple W oB) : MatchedKeys W oA oB := by
  intro i z t e he
  let p : ComponentPosition W e := ⟨⟨i, z, t⟩, he⟩
  constructor
  · funext n
    exact congrFun (congrFun (congrArg Prod.fst (congrFun h e)) n) p
  · funext n
    exact congrFun (congrFun (congrArg Prod.snd (congrFun h e)) n) p

/--
---
conclusion: Lax342547.QueryReference.component_position_budget
---
-/
theorem component_position_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) : by
      classical
      exact Fintype.card (ComponentPosition W e) ≤ 28 := by
  classical
  exact (Fintype.card_subtype_le _).trans (Lax342547.QuerySlots.position_budget W)

/--
---
conclusion: Lax342547.QueryReference.grouped_slot_count
---
-/
theorem grouped_slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (Slot W) = 2 * ∑ e, Fintype.card (ComponentPosition W e) := by
  classical
  rw [Fintype.card_congr (groupedSlots W), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_bool, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact Nat.mul_comm _ _

/--
---
conclusion: Lax342547.QueryReference.key_space_size
---
-/
theorem key_space_size {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type} [Fintype N]
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (space (ComponentPosition W) N (gram W)) ≤
        2 ^ (Fintype.card (Slot W) * Fintype.card N) := by
  classical
  rw [Lax342547.QueryReference.grouped_slot_count]
  calc
    _ ≤ Fintype.card (Tuples (Component (Tag k)) (ComponentPosition W) N) := Fintype.card_subtype_le _
    _ = _ := by
      have hc (e : Component (Tag k)) : Fintype.card (Matrix N (ComponentPosition W e) Binary) =
          2 ^ (Fintype.card N * Fintype.card (ComponentPosition W e)) := by
        simp [Matrix, ZMod.card, ← pow_mul, Nat.mul_comm]
      change Fintype.card (∀ e : Component (Tag k), Matrix N (ComponentPosition W e) Binary ×
        Matrix N (ComponentPosition W e) Binary) = _
      rw [Fintype.card_pi]
      simp only [Fintype.card_prod, hc, ← pow_add]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring

/--
---
conclusion: Lax342547.QueryReference.key_space_density
---
-/
theorem key_space_density {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type} [Fintype N]
    (W : Lists k n b degree r hr) (hN : 57 ≤ Fintype.card N) : by
      classical
      exact (∏ e, 1 / (2 : ℝ≥0∞)^
        (Fintype.card (ComponentPosition W e) * Fintype.card (ComponentPosition W e) + 2)) ≤
        (PMF.uniformOfFintype (Tuples (Component (Tag k)) (ComponentPosition W) N)).toOuterMeasure
          (space (ComponentPosition W) N (gram W)) := by
  classical
  apply Lax342547.ReferenceKeys.reference_density_lower
  intro e
  have h := Lax342547.QueryReference.component_position_budget W e
  omega

end Lax342547Proofs.QueryReference
