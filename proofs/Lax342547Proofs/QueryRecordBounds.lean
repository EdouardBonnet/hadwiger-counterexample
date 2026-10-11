import Lax342547.QueryRecordBounds
import Lax342547.JoinedRecords
import Lax342547.RawQueryImages

namespace Lax342547Proofs.QueryRecordBounds
open Lax342547.QueryRecordBounds

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.JoinedRecords Lax342547.PairedKeys Lax342547.KeySpans

/--
---
conclusion: Lax342547.QueryRecordBounds.key_map_range
---
-/
theorem key_map_range {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Lax342547.CutProfiles.Component (Tag k)) :
    LinearMap.range (keyMap (H := H) W e) = keys (H := H) W e := by
  classical
  apply le_antisymm
  · rintro v ⟨c,rfl⟩
    change (∑ p : ComponentPosition W e, c p • ray (H := H) (labels W) (bases W) p.val) ∈ keys W e
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    have he : ray (H := H) (labels W) (bases W) p.val = direction W e p.val := by
      simp only [direction, if_pos p.property]
    rw [he]
    exact Submodule.subset_span (Set.mem_range_self p.val)
  · apply Submodule.span_le.mpr
    rintro v ⟨p,rfl⟩
    by_cases hp : (W.left p.1 p.2.1 p.2.2).tag ∈ e.val
    · refine ⟨Pi.single ⟨p,hp⟩ 1, ?_⟩
      rw [Lax342547.RawQueryImages.key_map_coordinate]
      simp only [direction, if_pos hp]
      rfl
    · simp only [direction, if_neg hp]
      exact Submodule.zero_mem _

/--
---
conclusion: Lax342547.QueryRecordBounds.record_linear_bound
---
-/
theorem record_linear_bound {Axis I Status : Type}
    [Fintype Axis] [Fintype I] [Fintype Status]
    (dims : Axis → ℕ) (columnCoef n K k s : ℕ)
    (hcolumns : Fintype.card I ≤ columnCoef*n) (hdims : (∑ a, dims a) ≤ K+k)
    (hstatus : Fintype.card Status ≤ 2^(s*n)) : by
      classical
      exact Fintype.card (RecordType Axis I dims Status) ≤ 2^((columnCoef*(K+k)+s)*n) := by
  classical
  rw [Lax342547.JoinedRecords.joined_record_count]
  have h := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < 2)
    (Nat.mul_le_mul hcolumns hdims)) hstatus
  apply h.trans
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  nlinarith

/--
---
conclusion: Lax342547.QueryRecordBounds.actual_nominal_column_linear_bound
---
-/
theorem actual_nominal_column_linear_bound {H : Type} [Fintype H]
    (k n b degree hcoef : ℕ) (hn : 1 ≤ n) (hH : Fintype.card H ≤ hcoef*n) :
    Fintype.card (Fin 2 × (Coordinate k n b degree ⊕ H)) ≤
      (2 * (Fintype.card (SelectorCoordinates b degree) * (Fintype.card (Tag k)^2+4) + hcoef)) * n := by
  rw [Lax342547.JoinedRecords.nominal_column_count]
  have hcoord := Lax342547.JoinedRecords.coordinate_linear_budget k n b degree hn
  nlinarith

/--
---
conclusion: Lax342547.QueryRecordBounds.actual_joined_rank_budget
---
-/
theorem actual_joined_rank_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N) : by
      classical
      exact (∑ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
        Module.finrank Binary (joined P (fun a => keyMap (H := H) W a.1) a)) ≤
          P.rank + Fintype.card (Lax342547.QuerySlots.Slot W) := by
  classical
  have h := Lax342547.JoinedRecords.joined_rank_budget P (fun a => keyMap (H := H) W a.1)
  rwa [Lax342547.RawQueryImages.key_dimension] at h

end Lax342547Proofs.QueryRecordBounds
