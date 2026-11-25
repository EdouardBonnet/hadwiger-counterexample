import Lax793645Proofs.Simplifications.OneUniformHitBounds
import Lax793645Proofs.Simplifications.OneQueryCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def oneQueryCoordinateEquiv (t : Tagging p I) (N : ℕ) :
    KeyCoordinates (KeySlots p t) N ≃ OneKeys t N :=
  (rackCoordinates (KeySlots p t) N).toEquiv.trans (oneScatter t N).symm

theorem one_query_coordinate_inverse (v : Template p I) (o : OneUnit p n N)
    (x : Inputs p n I) :
    oneTemplateCoordinates v o x=(oneQueryCoordinateEquiv v.t N).symm (oneResultKey v o x) := rfl

theorem one_coordinate_uniform_event (t : Tagging p I)
    [DecidableEq (KeySlots p t)]
    (S : KeyCoordinates (KeySlots p t) N→Prop) :
    pr unif (fun x=>S ((oneQueryCoordinateEquiv t N).symm x))=pr unif S := by
  have h:=mapW_avg (unif : Wgt (OneKeys t N)) (oneQueryCoordinateEquiv t N).symm
    (fun x=>ind (S x))
  rw [unif_equiv] at h
  exact h.symm

theorem one_coordinate_query_event (v : Template p I) (o : OneUnit p n N)
    [DecidableEq (KeySlots p v.t)]
    (w : I→Wgt (Knobs p.g n)) (S : KeyCoordinates (KeySlots p v.t) N→Prop) :
    pr (oneHeatMap v o w) (fun x=>S ((oneQueryCoordinateEquiv v.t N).symm x))=
      pr (mapW (prodW w) (oneTemplateCoordinates v o)) S := by
  unfold oneHeatMap pr
  simp only [mapW_avg,one_query_coordinate_inverse]

/-- The repeated-hit estimate in the linear coordinates used by the
new partitions. Its input law may retain the prescribed unary testers. -/
theorem one_coordinate_hit_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    [DecidableEq (KeySlots p v.t)]
    (c : ℝ) :
    ∃ B α : ℝ,2≤B ∧ 0<α ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ S : KeyCoordinates (KeySlots p v.t) (M*n)→Prop,
      bp (-α*n)≤pr unif S →
      pr π (fun o=>B*pr unif S<pr (mapW (prodW w) (oneTemplateCoordinates v o)) S)
        ≤bp (-10*n) := by
  obtain ⟨B,α,hB,hα,_,hcal⟩:=one_uniform_hit_calendar v M hM (max c 0) (le_max_right ..)
  refine ⟨B,α,hB,hα,?_⟩
  filter_upwards [hcal] with n hn m hN π hπ hcap w hw hz S hS
  have hcap' o : π o≤bp (max c 0*(M*n:ℕ))*oneUnitRaw m (M*n) o := by
    refine (hcap o).trans (mul_le_mul_of_nonneg_right (bp_le ?_) ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)
    · exact (one_unit_raw_law m (by omega)).nz o
  have hh:=hn m hN π hπ hcap' w hw hz
    (fun x=>S ((oneQueryCoordinateEquiv v.t (M*n)).symm x))
  rw [one_coordinate_uniform_event] at hh
  simpa only [one_coordinate_query_event] using hh hS

end
end Lax793645Proofs.Simplifications
