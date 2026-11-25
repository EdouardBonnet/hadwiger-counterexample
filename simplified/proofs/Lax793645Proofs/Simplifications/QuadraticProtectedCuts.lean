import Lax793645Proofs.Simplifications.JointQuadraticBlocks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Isolate the selected atoms while retaining a protected residual. No
assumption is made on the intersection of the projected kernel with pins. -/
theorem quadratic_cut_protected_residual
    (l : I→Tag p.g) (s : I→Label p.b) (z : I→Base p.g n)
    (hz : ∀ i,allows (l i) (z i))
    (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n)))
    (hs : LinearIndependent F (U.mkQ∘fun i=>selV p.j (s i)))
    (ht : LinearIndependent F (V.mkQ∘fun i=>baseV (z i)))
    (P K : Comp p.g→Space (Ray p n))
    (hPL : ∀ e,P e≤tensorCross U V)
    (hK : ∀ e,K e≤P e⊔selectedAtComponent l s z e)
    (R : ℕ)
    (hP : ∀ e,∀ v∈P e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card I→
      v∈tensorRectangle U V)
    (x : Profile p n) (hx : x∈Xspace p n) (hR : ∀ e,(x e).rank≤R)
    (hquad : x∈quadraticCutConstraints (fun e=>P e⊔selectedAtComponent l s z e) K) :
    ∃ (c : I→F) (y : Profile p n),
      x=(∑ i,c i•atom p (l i) (s i) (z i))+y ∧ y∈Xspace p n ∧
      ∀ e,colSp (y e)≤tensorCross U V := by
  classical
  let A:=selectedTensorSpace (fun i=>selV p.j (s i)) (fun i=>baseV (z i))
  let L:=tensorCross U V
  obtain ⟨E,hE,hEL⟩:=selected_tensor_extractors U V _ _ hs ht
  have he (i : I) : E (point p (s i) (z i))=Pi.single i 1:=hE i
  have hW (e : Comp p.g) : x e∈Wspace p n := by
    obtain ⟨w,hw,rfl⟩:=mem_X.mp hx
    exact (Wspace p n).add_mem ((Wtag_le _) (hw e.val.1)) ((Wtag_le _) (hw e.val.2))
  have hbig (e : Comp p.g) : x e∈quadraticSquares (P e⊔A)⊔quadraticCross (K e) :=
    (sup_le_sup (quadratic_squares_mono
      (sup_le_sup_left (selected_at_component_le l s z e) _)) le_rfl)
      ((quadratic_cut_constraints_mem _ _ x).mp hquad e)
  have hKbig (e : Comp p.g) : K e≤P e⊔A:=
    (hK e).trans (sup_le_sup_left (selected_at_component_le l s z e) _)
  have hs1 (i : I) : dotProduct (Pi.single emptySel 1) (selV p.j (s i))=1 := by
    simp [single_dotProduct,selV,emptySel]
  have ht1 (i : I) : dotProduct (Pi.single none 1) (baseV (z i))=1 := by
    simp [single_dotProduct,baseV]
  have hsplit (e : Comp p.g) := protected_tensor_annihilator U V (P e) (P e)
    (fun i=>selV p.j (s i)) (fun i=>baseV (z i)) hs ht
    (Pi.single emptySel 1) (Pi.single none 1) hs1 ht1 R (hP e) (hP e)
    (x e) (Wspace_le_affineTensorSpace p n (hW e)) (hR e)
    (quadratic_annihilator_vanish (P e⊔A) (K e) (hKbig e) (hbig e))
  choose a w hw hwp using hsplit
  have hread (e : Comp p.g) (i : I) : matrixRead E i (x e)=a e i := by
    rw [hw,map_add]
    have hw0 : matrixRead E i (w e)=0:=matrixRead_zero E i L hEL _
      ((box_mem ..).mp (hwp e)).1
    rw [hw0,add_zero,map_sum]
    simp_rw [map_smul,matrixRead_outer,hE]
    simp [Pi.single_apply]
  have hoff (i : I) (e : Comp p.g) (hn : ¬inc e (l i)) : matrixRead E i (x e)=0 := by
    apply matrix_read_quadratic_constraints E i (P e⊔selectedAtComponent l s z e) (K e) ?_
      ((quadratic_cut_constraints_mem _ _ x).mp hquad e)
    have hh : P e⊔selectedAtComponent l s z e≤((LinearMap.proj i).comp E).ker := by
      apply sup_le
      · intro v hv
        change E v i=0
        rw [show E v=0 from hEL (hPL e hv)]
        rfl
      · apply Submodule.span_le.mpr
        rintro v ⟨j,hj,rfl⟩
        have hji : i≠j:=by intro h; subst j; exact hn hj
        change E (point p (s j) (z j)) i=0
        rw [he]
        simp [Pi.single_eq_of_ne hji]
    exact fun v hv=>hh hv
  have hconst (i : I) : ∃ c : F,∀ e,matrixRead E i (x e)=if inc e (l i) then c else 0 := by
    obtain ⟨w,_,rfl⟩:=mem_X.mp hx
    exact CycleGeometry.cut_star_constant w (l i) (matrixRead E i) (hoff i)
  choose c hc using hconst
  let b : Profile p n:=∑ i,c i•atom p (l i) (s i) (z i)
  have hb : b∈Xspace p n:=Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (atom_mem _ (hz i)))
  have hbval (e : Comp p.g) : b e=∑ i,a e i•mom p (s i) (z i) := by
    simp only [b,Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [←hread e i,hc,atom_def]
    by_cases h : inc e (l i) <;> simp [h]
  refine ⟨c,x-b,(add_sub_cancel _ _).symm,(Xspace p n).sub_mem hx hb,?_⟩
  intro e
  have hy : (x-b) e=w e := by
    change x e-b e=w e
    rw [hw,hbval]
    exact add_sub_cancel_left _ _
  rw [hy]
  exact ((box_mem ..).mp (hwp e)).1

end
end Lax793645Proofs.Simplifications
