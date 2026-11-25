import Lax793645Proofs.Simplifications.OneQueryCellPullback
import Lax793645Proofs.Simplifications.OneQueryRankDeficit
import Lax793645Proofs.Simplifications.LinearCellBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset Matrix Filter
open scoped Classical BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N r : ℕ}

def oneCellMap (t : Tagging p I)
    (P : Mat (Fin r) (Fin N×Bool×KeySlots p t)) :
    OneSlotKeys t N→ₗ[F]Vec (Fin r):=
  P.mulVecLin.comp (oneSlotCoordinates t N).toLinearMap

def oneCellRows (t : Tagging p I) [DecidableEq (KeySlots p t)]
    (P : Mat (Fin r) (Fin N×Bool×KeySlots p t)) :=
  onePartitionRows t (oneCellMap t P)

theorem one_cell_row_dimension (t : Tagging p I)
    (P : Mat (Fin r) (Fin N×Bool×KeySlots p t)) :
    dim (Module.Dual F (oneCellMap t P).range)≤r := by
  rw [dim,Subspace.dual_finrank_eq]
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_fin] using
    Submodule.finrank_le (oneCellMap t P).range

theorem one_coordinate_cell_cap (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (o : OneUnit p n N) (P : Mat (Fin r) (Fin N×Bool×KeySlots p v.t))
    (d : ℕ) (hd : dim (((oneTupleFreeRows v o).comp (oneCellRows v.t P)).ker)≤d)
    (κ : Wgt (Inputs p n I)) (L : ℝ) (hL : 0≤L) (hκ : ∀ x,κ x≤L*unif x)
    (a : Vec (Fin r)) :
    pr κ (fun x=>P*ᵥoneTemplateCoordinates v o x=a)≤
      (L*bp (d:ℝ))*mapW unif P.mulVec a := by
  have h:=one_uniform_query_cell v o (oneCellMap v.t P) d hd a
  have he : mapW unif (oneCellMap v.t P) a=mapW unif P.mulVec a := by
    exact probability_equiv (oneSlotCoordinates v.t N).toEquiv (fun x=>P*ᵥx=a)
  have hx (x : Inputs p n I) : oneCellMap v.t P (oneSlotValues v o x)=
      P*ᵥoneTemplateCoordinates v o x := by
    change P*ᵥ(oneSlotCoordinates v.t N (oneSlotValues v o x))=_
    rw [one_slot_values_coordinates]
  simp only [hx,he] at h
  exact (pr_cap hκ _).trans ((mul_le_mul_of_nonneg_left h hL).trans_eq (mul_assoc _ _ _).symm)

/-- The height precedes the number of equations. The only input-law
assumption used here is its fixed density bound relative to uniform inputs. -/
theorem one_linear_cell_cap_calendar (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L : ℝ) (hL : 0<L) :
    ∃ B : ℝ,2≤B ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+1≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (κ : Wgt (Inputs p n I)),(∀ x,κ x≤L*unif x) →
      ∀ (r : ℕ),r≤R → ∀ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
      ∀ a : Vec (Fin r),pr π (fun o=>B*mapW unif P.mulVec a<
        pr κ (fun x=>P*ᵥoneTemplateCoordinates v o x=a))≤bp (-10*n) := by
  cases isEmpty_or_nonempty (KeySlots p v.t) with
  | inl hEmpty =>
    letI:=hEmpty
    refine ⟨2+L,by linarith,fun R=>Filter.Eventually.of_forall ?_⟩
    intro n m hroom π hπ hcap κ hκ r hr P a
    have hz : dim (OneSlotKeys v.t (M*n))=0:=by
      simp only [dim,OneSlotKeys,Module.finrank_pi_fintype,Finset.univ_eq_empty,Finset.sum_empty]
    have hd : dim (Module.Dual F (oneCellMap v.t P).range)=0 := by
      rw [dim,Subspace.dual_finrank_eq]
      have hh:=(oneCellMap v.t P).finrank_range_le
      change _≤dim (OneSlotKeys v.t (M*n)) at hh
      omega
    have hb (o : OneUnit p n (M*n)) : pr κ (fun x=>P*ᵥoneTemplateCoordinates v o x=a)≤
        (2+L)*mapW unif P.mulVec a := by
      have hk : dim (((oneTupleFreeRows v o).comp (oneCellRows v.t P)).ker)≤0:=by
        have hh:=Submodule.finrank_le ((oneTupleFreeRows v o).comp (oneCellRows v.t P)).ker
        change _≤dim (Module.Dual F (oneCellMap v.t P).range) at hh
        simpa only [hd] using hh
      have hh:=one_coordinate_cell_cap v o P 0 hk κ L hL.le hκ a
      simp only [Nat.cast_zero,bp_zero,mul_one] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (map_nz unif_law.nz _ _))
    have he (o : OneUnit p n (M*n)) : ¬(2+L)*mapW unif P.mulVec a<
        pr κ (fun x=>P*ᵥoneTemplateCoordinates v o x=a):=not_lt.mpr (hb o)
    have hf : (fun o : OneUnit p n (M*n)=>(2+L)*mapW unif P.mulVec a<
        pr κ (fun x=>P*ᵥoneTemplateCoordinates v o x=a))=(fun _=>False):=by
      funext o
      exact propext (iff_false_intro (he o))
    rw [hf,pr_false]
    exact (bp_pos _).le
  | inr hNonempty =>
    letI:=hNonempty
    obtain ⟨d,hd,hcal⟩:=one_tuple_deficit_calendar v M hM c
    let k:=Fintype.card (KeySlots p v.t)*d
    let B:=2+L*bp (k:ℝ)
    refine ⟨B,le_add_of_nonneg_right (mul_nonneg hL.le (bp_pos _).le),fun R=>?_⟩
    filter_upwards [hcal R] with n hn m hroom π hπ hcap κ hκ r hr P a
    let T:=oneCellRows v.t P
    have hex:=hn m hroom π hcap (Module.Dual F (oneCellMap v.t P).range)
      ((one_cell_row_dimension v.t P).trans hr) T
      (one_partition_rows_injective v.t (oneCellMap v.t P))
    refine (pr_mono hπ.nz (fun o ho=>?_)).trans hex
    by_contra hbad
    have hk : dim (((oneTupleFreeRows v o).comp T).ker)≤k:=by
      dsimp only [k]
      omega
    have hh:=one_coordinate_cell_cap v o P k hk κ L hL.le hκ a
    have hb : L*bp (k:ℝ)≤B:=by dsimp only [B]; linarith
    exact (not_lt_of_ge (hh.trans (mul_le_mul_of_nonneg_right hb (map_nz unif_law.nz _ _)))) ho

end
end Lax793645Proofs.Simplifications
