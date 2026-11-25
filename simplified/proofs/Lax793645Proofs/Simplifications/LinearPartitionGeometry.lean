import Lax793645Proofs.Simplifications.LinearProjectionFourier
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

theorem frequency_space_dimension (P : Mat J I) :
    dim (frequencySpace P)≤Fintype.card J := by
  change Pᵀ.rank≤Fintype.card J
  rw [Matrix.rank_transpose]
  exact Matrix.rank_le_card_height P

theorem frequency_space_matrix (H : Space (Vec I)) :
    frequencySpace (pack H)ᵀ=H := by
  unfold frequencySpace
  rw [Matrix.transpose_transpose]
  exact colSp_pack H

theorem frequency_space_rows (P : Mat J I) (Q : Mat K I) :
    frequencySpace (Matrix.fromRows P Q)=frequencySpace P⊔frequencySpace Q := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    change (Matrix.fromRows P Q)ᵀ*ᵥz∈_
    rw [Matrix.transpose_fromRows,Matrix.fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_,rfl⟩ ⟨_,rfl⟩
  · apply sup_le
    · rintro x ⟨z,rfl⟩
      refine ⟨Sum.elim z 0,?_⟩
      change (Matrix.fromRows P Q)ᵀ*ᵥ(Sum.elim z 0)=_
      rw [Matrix.transpose_fromRows,Matrix.fromCols_mulVec_sumElim,Matrix.mulVec_zero,add_zero]
      rfl
    · rintro x ⟨z,rfl⟩
      refine ⟨Sum.elim 0 z,?_⟩
      change (Matrix.fromRows P Q)ᵀ*ᵥ(Sum.elim 0 z)=_
      rw [Matrix.transpose_fromRows,Matrix.fromCols_mulVec_sumElim,Matrix.mulVec_zero,zero_add]
      rfl

theorem rows_refine_left (P : Mat J I) (Q : Mat K I) :
    (fun x : Vec (J⊕K)=>x∘Sum.inl)∘(Matrix.fromRows P Q).mulVec=P.mulVec := by
  ext x i
  simp only [Function.comp_apply,Matrix.fromRows_mulVec,Sum.elim_inl]

theorem rows_refine_right (P : Mat J I) (Q : Mat K I) :
    (fun x : Vec (J⊕K)=>x∘Sum.inr)∘(Matrix.fromRows P Q).mulVec=Q.mulVec := by
  ext x i
  simp only [Function.comp_apply,Matrix.fromRows_mulVec,Sum.elim_inr]

/-- Choose common equations before choosing either side's adaptive
filter. The exceptional probability concerns independent leaf draws. -/
theorem common_linear_matrices {Λ : Type} [Fintype Λ]
    (μ : Wgt Λ) (hμ : IsLaw μ) (r : Λ→ℕ) (P : ∀ l,Mat (Fin (r l)) I)
    (R : ℕ) (hR : ∀ l,r l≤R) (η : ℝ) (hη : 0<η) :
    ∃ s : ℕ,(s:ℝ)≤R*bp R/η ∧ ∃ C : Mat (Fin s) I,
      pr (pairW μ μ) (fun l=>
        frequencySpace (Matrix.fromRows (P l.1) C)⊓
          frequencySpace (Matrix.fromRows (P l.2) C)≠frequencySpace C)≤η := by
  obtain ⟨H,hH,hrare⟩:=common_linear_intersections μ hμ
    (fun l=>frequencySpace (P l)) R
    (fun l=>(frequency_space_dimension (P l)).trans (by simpa only [Fintype.card_fin] using hR l)) η hη
  refine ⟨dim H,hH,(pack H)ᵀ,?_⟩
  simpa only [frequency_space_rows,frequency_space_matrix] using hrare

end
end Lax793645Proofs.Simplifications
