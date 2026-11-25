import Lax793645Proofs.Simplifications.TensorConfinement
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixQuotients

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
noncomputable section

variable {S T I : Type} [Fintype S] [Fintype T] [Fintype I]

theorem finrank_finite_sup (H : I → Space (Vec S)) :
    dim (⨆ i, H i : Space (Vec S)) ≤ ∑ i, dim (H i) := by
  classical
  let f (x : Σ i, Fin (dim (H i))) : Vec S := (pack (H x.1)).col x.2
  have he : (⨆ i, H i)=Submodule.span F (Set.range f) := by
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [← colSp_pack (H i),colSp,Matrix.range_mulVecLin]
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Submodule.subset_span ⟨⟨i,j⟩,rfl⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact (le_iSup H i) (by rw [← colSp_pack (H i)]; exact colSp_mem j)
  rw [he]
  have h := finrank_range_le_card (R:=F) f
  simpa only [Set.finrank,dim,Fintype.card_sigma,Fintype.card_fin] using h

/-- Choose a bounded selector space from low-rank pin vectors. Its dimension
depends on the pin dimension and the rank cutoff, not the selector dimension. -/
theorem low_rank_pin_protection (P : Space (Mat S T)) (q : ℕ) :
    ∃ U : Space (Vec S), dim U ≤ q*dim P ∧
      ∀ M ∈ P, M.rank ≤ q → colSp M ≤ U := by
  classical
  let K : Set (Mat S T) := {M | M ∈ P ∧ M.rank ≤ q}
  obtain ⟨L,hL,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn F K
  let U : Space (Vec S) := ⨆ M : L, colSp M.val
  have hspanP : Submodule.span F K ≤ P := Submodule.span_le.mpr (fun _ h => h.1)
  have hcardP : L.card ≤ dim P := by
    rw [hcard]
    exact Submodule.finrank_mono hspanP
  have hcolumns : Submodule.span F (L : Set (Mat S T)) ≤ box U ⊤ := by
    apply Submodule.span_le.mpr
    intro M hM
    exact (box_mem M U ⊤).mpr ⟨le_iSup (fun M : L => colSp M.val) ⟨M,hM⟩,le_top⟩
  refine ⟨U,?_,?_⟩
  · calc
      dim U ≤ ∑ M : L, dim (colSp M.val) := finrank_finite_sup _
      _ ≤ ∑ _M : L, q := Finset.sum_le_sum (fun M _ => (hL M.property).2)
      _ = q*L.card := by simp [Nat.mul_comm]
      _ ≤ q*dim P := Nat.mul_le_mul_left q hcardP
  intro M hM hq
  apply ((box_mem M U ⊤).mp (hcolumns ?_)).1
  rw [hspan]
  exact Submodule.subset_span ⟨hM,hq⟩

def transposeLinear : Mat S T →ₗ[F] Mat T S where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' _ _ := rfl

/-- All base factors of the pins fit in a space whose dimension is bounded
by selector dimension times pin dimension. -/
theorem pin_base_protection (P : Space (Mat S T)) :
    ∃ V : Space (Vec T), dim V ≤ Fintype.card S*dim P ∧
      ∀ M ∈ P, colSp Mᵀ ≤ V := by
  obtain ⟨V,hV,hMV⟩ := low_rank_pin_protection (P.map transposeLinear) (Fintype.card S)
  refine ⟨V,hV.trans (Nat.mul_le_mul_left _ (Submodule.finrank_map_le _ _)),?_⟩
  intro M hM
  exact hMV Mᵀ ⟨M,hM,rfl⟩ (Matrix.rank_le_card_width _)

/-- Common protected spaces across all projected pins. Low-rank pin vectors
lie in the rectangle U tensor V; every pin vector lies in S tensor V. -/
theorem common_pin_protection (P : I → Space (Mat S T)) (q : ℕ) :
    ∃ (U : Space (Vec S)) (V : Space (Vec T)),
      dim U ≤ q*(∑ i, dim (P i)) ∧
      dim V ≤ Fintype.card S*(∑ i, dim (P i)) ∧
      (∀ i M, M ∈ P i → colSp Mᵀ ≤ V) ∧
      (∀ i M, M ∈ P i → M.rank ≤ q → M ∈ box U V) := by
  choose U hU hMU using fun i => low_rank_pin_protection (P i) q
  choose V hV hMV using fun i => pin_base_protection (P i)
  refine ⟨⨆ i, U i,⨆ i, V i,?_,?_,?_,?_⟩
  · exact (finrank_finite_sup U).trans ((Finset.sum_le_sum (fun i _ => hU i)).trans_eq
      (Finset.mul_sum ..).symm)
  · exact (finrank_finite_sup V).trans ((Finset.sum_le_sum (fun i _ => hV i)).trans_eq
      (Finset.mul_sum ..).symm)
  · intro i M hM
    exact (hMV i M hM).trans (le_iSup V i)
  intro i M hM hq
  rw [box_mem]
  exact ⟨(hMU i M hM hq).trans (le_iSup U i),(hMV i M hM).trans (le_iSup V i)⟩

end
end Lax793645Proofs.Simplifications
