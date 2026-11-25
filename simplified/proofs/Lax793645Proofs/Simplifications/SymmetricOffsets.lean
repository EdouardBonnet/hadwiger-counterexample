import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.OffsetLifting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]

theorem projected_box_injective {S V : Space (Vec I)} (h : Disjoint S V)
    {A B : Mat I I} (hA : A∈box V V) (hB : B∈box V V)
    (he : liftM (chop S) (chop S) A=liftM (chop S) (chop S) B) : A=B := by
  obtain ⟨A,rfl⟩:=hA
  obtain ⟨B,rfl⟩:=hB
  have hi:=chop_inj_pack (S:=S) (pack_inj V) (by rw [colSp_pack]; exact h)
  rw [liftM_comp,liftM_comp] at he
  rw [liftM_inj hi hi he]

theorem projected_frame_lift {S V : Space (Vec I)} {A : Mat I J}
    (h : colSp A≤chopSpace S V) :
    ∃ P : Mat I J,colSp P≤V ∧chop S*P=A := by
  have he : chopSpace S V=colSp (chop S*pack V) := by
    rw [chopSpace,colSp,Matrix.mulVecLin_mul,LinearMap.range_comp,
      show LinearMap.range (pack V).mulVecLin=_ from colSp_pack V]
  obtain ⟨R,hR⟩:=pull_cols (chop S*pack V) A (he ▸ h)
  exact ⟨pack V*R,(col_follow ..).trans_eq (colSp_pack V),by rw [←Matrix.mul_assoc,hR]⟩

/-- Lift a prescribed symmetric rank factor through a quotient while
keeping its nonsingular middle matrix unchanged. -/
theorem symmetric_frame_lift (M : Mat I I) (S V : Space (Vec I))
    (A : Mat I J) (G : Mat J J) (hM : M∈box V V) (hSV : Disjoint S V)
    (hA : Injective A.mulVec) (hG : Injective G.mulVec)
    (he : liftM (chop S) (chop S) M=A*G*Aᵀ) :
    ∃ P : Mat I J,Injective P.mulVec ∧colSp P≤V ∧chop S*P=A ∧P*G*Pᵀ=M := by
  classical
  have hc:=((box_mem ..).mp (he ▸ lift_mem_box (chop S) (chop S) hM)).1
  rw [col_retain (transpose_surj_iff.mpr hA),
    col_retain (Finite.surjective_of_injective hG)] at hc
  obtain ⟨P,hP,hPA⟩:=projected_frame_lift hc
  have hi : Injective P.mulVec:=fun x y h=>hA (by
    rw [←hPA,←mulVec_mulVec,←mulVec_mulVec,h])
  refine ⟨P,hi,hP,hPA,?_⟩
  have hbox : P*G*Pᵀ∈box V V := by
    apply (box_mem ..).mpr
    refine ⟨(col_follow ..).trans ((col_follow ..).trans hP),?_⟩
    rw [transpose_mul,transpose_mul,transpose_transpose]
    exact (col_follow ..).trans hP
  apply projected_box_injective hSV hbox hM
  rw [he,liftM_def,←hPA,transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Two symmetric matrices that agree after quotienting by a cover
have rank factors with the same middle form and the same quotient. -/
theorem symmetric_common_factors (M : Bool→Mat I I) (S : Space (Vec I))
    (V : Bool→Space (Vec I)) (hsym : ∀ i,(M i)ᵀ=M i)
    (hM : ∀ i,M i∈box (V i) (V i)) (hSV : ∀ i,Disjoint S (V i))
    (hz : vanish S S (M true+M false)) :
    ∃ (P : Bool→Mat I (Fin (M true).rank))
      (G : Mat (Fin (M true).rank) (Fin (M true).rank)),
      Gᵀ=G ∧Injective G.mulVec ∧
      (∀ i,Injective (P i).mulVec ∧colSp (P i)≤V i ∧P i*G*(P i)ᵀ=M i) ∧
      chop S*P true=chop S*P false := by
  classical
  obtain ⟨A,G,hA,hG,hi,hprod⟩:=rank_symmetric (M true) (hsym true)
  have hc : colSp A≤V true := by
    have hh:=((box_mem ..).mp (hM true)).1
    rw [←hprod,col_retain (transpose_surj_iff.mpr hA),
      col_retain (Finite.surjective_of_injective hi)] at hh
    exact hh
  have hinj:=chop_inj_pack hA (Disjoint.mono_right hc (hSV true))
  have he : liftM (chop S) (chop S) (M false)=(chop S*A)*G*(chop S*A)ᵀ := by
    have hh:liftM (chop S) (chop S) (M false)=liftM (chop S) (chop S) (M true) := by
      have hv:=(vanish_chop _).mp hz
      rw [map_add] at hv
      exact add_left_cancel (hv.trans (char_two _).symm)
    rw [hh]
    calc
      liftM (chop S) (chop S) (M true)=liftM (chop S) (chop S) (A*G*Aᵀ):=
        congrArg (liftM (chop S) (chop S)) hprod.symm
      _ = _ := by
        rw [liftM_def,transpose_mul]
        simp only [Matrix.mul_assoc]
  obtain ⟨B,hB,hBV,hBA,hBM⟩:=symmetric_frame_lift (M false) S (V false)
    (chop S*A) G (hM false) (hSV false) hinj hi he
  refine ⟨onSide (A,B),G,hG,hi,?_,hBA.symm⟩
  intro i
  cases i
  · exact ⟨hB,hBV,hBM⟩
  exact ⟨hA,hc,hprod⟩

theorem difference_frame_in_cover (P : Bool→Mat I J) (S : Space (Vec I))
    (he : chop S*P true=chop S*P false) :
    ∃ (k : ℕ) (T : Mat I (Fin k)) (E : Mat (Fin k) J),
      k≤Fintype.card J ∧Injective T.mulVec ∧colSp T≤S ∧Surjective E.mulVec ∧
      P true+P false=T*E := by
  classical
  obtain ⟨T,E,hT,hE,hprod⟩:=rank_product (P true+P false)
  have hc : colSp (P true+P false)≤S := by
    rintro x ⟨v,rfl⟩
    apply (chop_ker ..).mp
    rw [mulVecLin_apply,mulVec_mulVec,Matrix.mul_add,he,char_two,Matrix.zero_mulVec]
  refine ⟨_,T,E,(P true+P false).rank_le_card_width,hT,?_,hE,hprod.symm⟩
  rw [←col_retain hE,hprod]
  exact hc

/-- Symmetric offsets have one companion family. The quadratic action
on its cover, together with the values on the cover itself, determines
the phase. There is no second primal mode. -/
theorem symmetric_offsets (M : Bool→Mat I I) (S : Space (Vec I))
    (V : Bool→Space (Vec I)) (hsym : ∀ i,(M i)ᵀ=M i)
    (hM : ∀ i,M i∈box (V i) (V i)) (hSV : ∀ i,Disjoint S (V i))
    (hz : vanish S S (M true+M false)) :
    ∃ (k : ℕ) (T : Mat I (Fin k)) (H : Mat (Fin k) (Fin k)),
      k≤(M true).rank ∧Injective T.mulVec ∧colSp T≤S ∧Hᵀ=H ∧
      ∀ i,∃ Z : Mat I (Fin k),Injective Z.mulVec ∧colSp Z≤V i ∧
        M true+M false=T*Zᵀ+Z*Tᵀ+T*H*Tᵀ := by
  classical
  obtain ⟨P,G,hG,hi,hP,hquot⟩:=symmetric_common_factors M S V hsym hM hSV hz
  obtain ⟨k,T,E,hk,hT,hTS,hE,hdiff⟩:=difference_frame_in_cover P S hquot
  refine ⟨k,T,E*G*Eᵀ,by simpa using hk,hT,hTS,?_,?_⟩
  · rw [transpose_mul,transpose_mul,transpose_transpose,hG,Matrix.mul_assoc]
  intro i
  refine ⟨P i*G*Eᵀ,inj_comp_mat _ _ (inj_comp_mat _ _ (hP i).1 hi)
    (transpose_surj_iff.mp (by simpa using hE)),
    (col_follow ..).trans ((col_follow ..).trans (hP i).2.1),?_⟩
  have hp : P (!i)=P i+T*E := by
    rw [←hdiff]
    cases i
    · rw [add_left_comm,char_two,add_zero]; rfl
    · rw [←add_assoc,char_two,zero_add]; rfl
  have he : M true+M false=M i+M (!i) := by cases i <;> simp [add_comm]
  rw [he,←(hP i).2.2,←(hP (!i)).2.2,hp]
  simp only [transpose_add,transpose_mul,transpose_transpose,hG,
    Matrix.add_mul,Matrix.mul_add,Matrix.mul_assoc]
  have hc : P i*(G*(P i)ᵀ)+P i*(G*(P i)ᵀ)=0:=char_two _
  ext a b
  have hh:=congrFun (congrFun hc a) b
  simp only [Matrix.add_apply,Matrix.zero_apply] at hh ⊢
  linear_combination hh

end
end Lax793645Proofs.Simplifications
