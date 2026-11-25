import Lax793645Proofs.Simplifications.ExactSupportPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RelationMismatchBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

/-- A fixed positive support gap makes threshold availability exact.
The statement applies to all labels retained for the scalar system. -/
def HasStatusSupportGap (u : Terrain p r) (s : Gazette p r d)
    (t : Gazette p r e) (η : ℝ) : Prop :=
  ∀ (x : Zodiac p),x.common→∀ i y,
    circlet u s t x i y=0 ∨ η≤circlet u s t x i y

theorem HasStatusSupportGap.mono {θ : ℝ} (h : HasStatusSupportGap u s t η)
    (hθ : θ≤η) : HasStatusSupportGap u s t θ := by
  intro x hx i y
  exact (h x hx i y).imp_right (fun hy=>hθ.trans hy)

/-- A dual equation on available generators holds on every possible
status pair. There is no discarded probability mass. -/
theorem dual_supported_eq (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η)
    (A B : Stalls p) (S : Straps (Label p.b)) (z : DualCoefficients d e)
    (hz : z.law (chapter (stellar u s t η A B) S))
    (x : Zodiac p) (i : Grid) (hx : x.common)
    (ha : x.s true∉outstraps A S true i.1)
    (hb : x.s false∉outstraps B S false i.2)
    (y : Touch p d e i) (hy : 0<circlet u s t x i y) :
    (leftChime z i).soot (x.aspect true) y.1=
      (rightChime z i).soot (x.aspect false) y.2 := by
  classical
  have hbound : η≤circlet u s t x i y:=(hgap x hx i y).resolve_left hy.ne'
  have hcarried:=(circlet_state u s t hu hs ht x hx i).2
  have hfit : (x.aspect true).fitsink y.1 ∧ (x.aspect false).fitsink y.2 :=
    not_not.mp (fun h=>hy.ne' (hcarried y h))
  let C:=stellar u s t η A B
  have hzone : (C i).zone S (x,y) :=
    ⟨⟨fun h=>ha (mem_union_left _ h),fun h=>hb (mem_union_left _ h),
      hx,hfit.1,hfit.2,hbound⟩,
      fun side=>by
        cases side
        · exact fun h=>hb (mem_union_right _ h)
        · exact fun h=>ha (mem_union_right _ h)⟩
  exact dual_eq z (chapter C S) hz i ((C i).writes (x,y))
    ((C i).band_write S hzone)

/-- In particular, every cell of positive reference mass is a complete
rectangle of mutually compatible unary parity values. -/
theorem dual_cell_support_eq (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η)
    (A B : Stalls p) (S : Straps (Label p.b)) (z : DualCoefficients d e)
    (hz : z.law (chapter (stellar u s t η A B) S))
    (x : Zodiac p) (i : Grid) (hx : x.common)
    (ha : x.s true∉outstraps A S true i.1)
    (hb : x.s false∉outstraps B S false i.2)
    (c : Fin r) (hc : 0<u x.l x.q c)
    (v : Magazine p (d i.1)) (w : Magazine p (e i.2))
    (hv : 0<s i.1 (x.aspect true) c v)
    (hw : 0<t i.2 (x.aspect false) c w) :
    (leftChime z i).soot (x.aspect true) v=
      (rightChime z i).soot (x.aspect false) w := by
  apply dual_supported_eq hu hs ht hgap A B S z hz x i hx ha hb (v,w)
  have hnonneg (j : Fin r) :
      0≤u x.l x.q j*(s i.1 (x.aspect true) j v*t i.2 (x.aspect false) j w) :=
    mul_nonneg ((hu.1 _ _).nz j) (mul_nonneg ((hs.law _ _ (hx true) j).nz v)
      ((ht.law _ _ (hx false) j).nz w))
  exact (mul_pos hc (mul_pos hv hw)).trans_le (weight_le_tot hnonneg c)

/-- The previous mismatch bound becomes exactly zero when positive
overlaps have the fixed support gap. -/
theorem dual_support_charge_zero (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η)
    (A B : Stalls p) (S : Straps (Label p.b)) (z : DualCoefficients d e)
    (hz : z.law (chapter (stellar u s t η A B) S))
    (x : Zodiac p) (i : Grid) (hx : x.common)
    (ha : x.s true∉outstraps A S true i.1)
    (hb : x.s false∉outstraps B S false i.2) :
    charge u x s t i (leftChime z i) (rightChime z i)=0 := by
  classical
  unfold charge pr avg
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : circlet u s t x i y=0
  · rw [hy,zero_mul]
  have hp : 0<circlet u s t x i y:=
    lt_of_le_of_ne ((circlet_state u s t hu hs ht x hx i).1.nz y) (Ne.symm hy)
  change circlet u s t x i y*ind ((leftChime z i).soot (x.aspect true) y.1≠
    (rightChime z i).soot (x.aspect false) y.2)=0
  rw [ind_zero (not_not.mpr (dual_supported_eq hu hs ht hgap A B S z hz x i hx ha hb y hp)),mul_zero]

end
end Lax793645Proofs.Simplifications
