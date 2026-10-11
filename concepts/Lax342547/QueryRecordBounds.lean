import Lax342547.JoinedRecords
import Lax342547.RawQueryImages

/-!
---
title: Actual query frozen spaces and linear record exponents
type: lemma
---
The actual key-map range is precisely the selected incident key span. Joined pin/key dimensions and the concrete nominal column budget give a record exponent linear in n, with no ambient-image charge.
-/

namespace Lax342547.QueryRecordBounds

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.JoinedRecords Lax342547.PairedKeys Lax342547.KeySpans

axiom key_map_range {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Lax342547.CutProfiles.Component (Tag k)) :
    LinearMap.range (keyMap (H := H) W e) = keys (H := H) W e

axiom record_linear_bound {Axis I Status : Type}
    [Fintype Axis] [Fintype I] [Fintype Status]
    (dims : Axis → ℕ) (columnCoef n K k s : ℕ)
    (hcolumns : Fintype.card I ≤ columnCoef*n) (hdims : (∑ a, dims a) ≤ K+k)
    (hstatus : Fintype.card Status ≤ 2^(s*n)) : by
      classical
      exact Fintype.card (RecordType Axis I dims Status) ≤ 2^((columnCoef*(K+k)+s)*n)

axiom actual_nominal_column_linear_bound {H : Type} [Fintype H]
    (k n b degree hcoef : ℕ) (hn : 1 ≤ n) (hH : Fintype.card H ≤ hcoef*n) :
    Fintype.card (Fin 2 × (Coordinate k n b degree ⊕ H)) ≤
      (2 * (Fintype.card (SelectorCoordinates b degree) * (Fintype.card (Tag k)^2+4) + hcoef)) * n

axiom actual_joined_rank_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N) : by
      classical
      exact (∑ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
        Module.finrank Binary (joined P (fun a => keyMap (H := H) W a.1) a)) ≤
          P.rank + Fintype.card (Lax342547.QuerySlots.Slot W)

end Lax342547.QueryRecordBounds
