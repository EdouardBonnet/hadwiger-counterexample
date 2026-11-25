import Lax793645Proofs.Simplifications.UniformHitBounds
import Lax793645Proofs.Simplifications.AffineQueryCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def queryCoordinateEquiv (t : Tagging p I) (N : ℕ) :
    KeyCoordinates (KeySlots p t) N ≃ Keys (p:=p) t N :=
  (rackCoordinates (KeySlots p t) N).toEquiv.trans (scatter t N).symm

theorem query_coordinate_inverse (v : Template p I) (o : UnitType p n N)
    (x : Inputs p n I) :
    templateKeyCoordinates v o x=(queryCoordinateEquiv v.t N).symm (v.resultKey o x) := rfl

theorem coordinate_uniform_event (t : Tagging p I)
    [DecidableEq (KeySlots p t)]
    (S : KeyCoordinates (KeySlots p t) N→Prop) :
    pr unif (fun x=>S ((queryCoordinateEquiv t N).symm x))=pr unif S := by
  have h:=mapW_avg (unif : Wgt (Keys (p:=p) t N)) (queryCoordinateEquiv t N).symm
    (fun x=>ind (S x))
  rw [unif_equiv] at h
  exact h.symm

theorem coordinate_query_event (v : Template p I) (o : UnitType p n N)
    [DecidableEq (KeySlots p v.t)]
    (w : I→Wgt (Knobs p.g n)) (S : KeyCoordinates (KeySlots p v.t) N→Prop) :
    pr (v.heatMap o w) (fun x=>S ((queryCoordinateEquiv v.t N).symm x))=
      pr (mapW (prodW w) (templateKeyCoordinates v o)) S := by
  unfold Template.heatMap pr
  simp only [mapW_avg,query_coordinate_inverse]

/-- The repeated-hit estimate in the linear coordinates used by the
new partitions. Its input law may retain the prescribed unary testers. -/
theorem coordinate_hit_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    [DecidableEq (KeySlots p v.t)]
    (c : ℝ) :
    ∃ B α : ℝ,2≤B ∧ 0<α ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ S : KeyCoordinates (KeySlots p v.t) (M*n)→Prop,
      bp (-α*n)≤pr unif S →
      pr π (fun o=>B*pr unif S<pr (mapW (prodW w) (templateKeyCoordinates v o)) S)
        ≤bp (-10*n) := by
  obtain ⟨B,α,hB,hα,_,hcal⟩:=uniform_hit_calendar v M hM (max c 0) (le_max_right ..)
  refine ⟨B,α,hB,hα,?_⟩
  filter_upwards [hcal] with n hn m hN π hπ hcap w hw hz S hS
  have hcap' o : π o≤bp (max c 0*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o := by
    refine (hcap o).trans (mul_le_mul_of_nonneg_right (bp_le ?_) ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)
    · exact (pairW_law (raw_law m hN) (raw_law m hN)).nz o
  have hh:=hn m hN π hπ hcap' w hw hz
    (fun x=>S ((queryCoordinateEquiv v.t (M*n)).symm x))
  rw [coordinate_uniform_event] at hh
  simpa only [coordinate_query_event] using hh hS

end
end Lax793645Proofs.Simplifications
