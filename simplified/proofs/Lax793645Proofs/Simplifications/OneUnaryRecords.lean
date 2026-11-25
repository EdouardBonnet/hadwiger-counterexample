import Lax793645Proofs.Simplifications.OneRealizedHits
import Lax793645Proofs.Simplifications.ImageCellConditioning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

theorem one_cross_reciprocal (x y : OneUnit p n N) (e : Comp p.g) :
    (oneCrossMatrix x y e)ᵀ=oneCrossMatrix y x e := by
  apply Matrix.ext
  intro i j
  simp only [oneCrossMatrix,Matrix.transpose_apply,LinearMap.toMatrix₂'_apply,
    LinearMap.compl₁₂_apply]
  exact one_unit_actual_reciprocal x y e _ _

def oneLedger (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (x : OneUnit p n N) : ImageLedger a.sp:=
  imageLedger (fun x e=>onePolarMatrix N*oneCoordinateImages x e) a x

theorem one_ledger_rows (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    {x y x' y' : OneUnit p n N}
    (hy : imagePinAgree oneCoordinateImages a y)
    (hy' : imagePinAgree oneCoordinateImages a y') (hx : oneLedger a x=oneLedger a x') :
    imageRowAgree a.sp (oneCrossMatrix y x) (oneCrossMatrix y' x') := by
  simp_rw [one_cross_matrix_images]
  exact image_ledger_rows oneCoordinateImages _ a hy hy' hx

theorem image_row_agree_step {C I : Type} [Fintype C] [Fintype I]
    {P : ImagePlan C I} {X Y Z : ImageCross C I}
    (h : imageRowAgree P X Y) (he : imageRowAgree P Z Y) : imageRowAgree P X Z:=
  fun e v hv w=>(h e v hv w).trans (he e v hv w).symm

variable {I : Type} [Fintype I]

set_option maxHeartbeats 800000 in
/-- The single-frame collision comparison after recording the opposite
pins. Loss is unnormalized and proportional to the two separate query
masses, so pair-dependent acceptance filters do not alter independence. -/
theorem one_record_hit (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    {a b f g : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    {μ δ : Wgt (OneUnit p n N)} (U V : OneUnit p n N→Prop) (key : OneKeys t N)
    (ha : ∀ x,U x→imagePinAgree oneCoordinateImages f x ∧
      (∀ i,oneFrameLaw m (x i)) ∧ oneVolleyKeys v t x=key)
    (hb : ∀ y,V y→imagePinAgree oneCoordinateImages g y ∧
      (∀ i,oneFrameLaw m (y i)) ∧ oneVolleyKeys w t y=key)
    (hpromise : ∀ x,U x→∀ y,V y→v.legal t ∧ w.legal t ∧ v.roleMatch w t ∧
      ∃ Q : OneCross p n,OneRealized v w t m Q ∧
        imageRowAgree f.sp Q (oneCrossMatrix x y) ∧
        imageRowAgree g.sp (fun e=>(Q e)ᵀ) (oneCrossMatrix y x))
    {ζ : ℝ} {k : ℕ} (hz : ζ≤0.004) (hkz : ζ*k≤0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : imagePinClear oneCoordinateImages a ζ μ)
    (hB : imagePinClear oneCoordinateImages b ζ δ)
    (haf : a.sp≤f.sp) (hbg : b.sp≤g.sp)
    (hf : imagePlanRank f.sp=imagePlanRank a.sp+k)
    (hg : imagePlanRank g.sp=imagePlanRank b.sp+k)
    (hN : 100≤2*N) (hT : (dim (OneCheckGram p n):ℝ)≤0.01*(2*N))
    (L : ℝ) (hLf : bp (dim (ImageLedger f.sp))≤L) (hLg : bp (dim (ImageLedger g.sp))≤L) :
    hit (2*N)*(pr μ U*pr δ V)≤
      pr (pairW μ δ) (fun xy=>U xy.1 ∧ V xy.2 ∧
        (oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false))+
      (hit (2*N)*tau (2*N) k*L)*(pr μ U+pr δ V) := by
  classical
  apply prune_pairs μ δ hμ hδ U V (oneLedger g) (oneLedger f)
    (fun xy=>(oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false))
    (hit (2*N)) (tau (2*N) k) (bp_pos _).le (bp_pos _) _ _
  · intro i j hi hj
    let F:=memberC U (oneLedger g) i
    let G:=memberC V (oneLedger f) j
    let α:=onW μ F
    let β:=onW δ G
    change tau (2*N) k≤pr μ F at hi
    change tau (2*N) k≤pr δ G at hj
    obtain ⟨hα,hclearA⟩:=image_cell_clear oneCoordinateImages hz hkz hμ hA haf hf
      F (fun x hx=>(ha x hx.1).1) hi
    obtain ⟨hβ,hclearB⟩:=image_cell_clear oneCoordinateImages hz hkz hδ hB hbg hg
      G (fun y hy=>(hb y hy.1).1) hj
    obtain ⟨x,hx,_⟩:=exists_of_pr_pos hμ.nz ((bp_pos _).trans_le hi)
    obtain ⟨y,hy,_⟩:=exists_of_pr_pos hδ.nz ((bp_pos _).trans_le hj)
    have ha' (z : OneUnit p n N) (hz : α z≠0) : F z:=
      Classical.byContradiction (fun h=>hz (normW_carried (subW_carried μ F) z h))
    have hb' (z : OneUnit p n N) (hz : β z≠0) : G z:=
      Classical.byContradiction (fun h=>hz (normW_carried (subW_carried δ G) z h))
    obtain ⟨hv,hw,hr,Q,hQ,hrow,hrow'⟩:=hpromise x hx.1 y hy.1
    apply one_realized_conflict_hit v w t m hv hw hr Q hQ hα hβ hclearA hclearB
      (fun z hz=>(ha z (ha' z hz).1).2.1) (fun z hz=>(hb z (hb' z hz).1).2.1)
      (fun z hz z' hz'=>(ha z (ha' z hz).1).2.2.trans (hb z' (hb' z' hz').1).2.2.symm)
      _ hN hT
    intro x' hx' y' hy'
    have hX:=ha' x' hx'
    have hY:=hb' y' hy'
    refine ⟨image_row_agree_step
      (one_ledger_rows f (ha x' hX.1).1 (ha x hx.1).1 (hY.2.trans hy.2.symm)) hrow,?_⟩
    simp_rw [one_cross_reciprocal]
    exact image_row_agree_step
      (one_ledger_rows g (hb y' hY.1).1 (hb y hy.1).1 (hX.2.trans hx.2.symm)) hrow'
  · rw [card_space]
    exact hLg
  · rw [card_space]
    exact hLf

end
end Lax793645Proofs.Simplifications
