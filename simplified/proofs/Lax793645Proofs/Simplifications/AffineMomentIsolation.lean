import Lax793645Proofs.Simplifications.AffineResidualCuts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap Finset
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem key_projection_le_selected (v : Volley p n I) (t : Tagging p I)
    (i : Bool) (z : Place p) :
    sPin (v.keyPlan t) z i ≤ selectedTensorSpace
      (fun j : CallsAt v i => selV p.j (v.sel j.val))
      (fun j : CallsAt v i => baseV (v.par j.val)) := by
  classical
  rintro _ ⟨k,⟨c,rfl⟩,rfl⟩
  change (IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c) ∈ _
  rw [v.key_proj]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨j.val,(v.visitH_here ..).mp hj⟩,rfl⟩

/-- Isolate every annihilating component using one pair of protected spaces
per endpoint. This has no selector-degree hypothesis. -/
theorem affine_component_isolation (v : Volley p n I) (t : Tagging p I)
    (a b : Plan p n) (C : ChanOut p n) (mode : Bool) (x : Xpair p n)
    (other : I → Bool) (hb : v.bounded other)
    (R q : ℕ) (hr : 2*planRank a+28 ≤ R) (hq : R^2+14 ≤ q)
    (hv : affineAvoids v a q) (ho : orth p C (v.frozen a t) b mode x) :
    ∃ H : RaySeparation v a, ∀ i e,
      ∃ (c : CallsAt v i → F) (z : Moment p n),
        (x i).val e=(∑ j : CallsAt v i, c j • mom p (v.sel j.val) (v.par j.val))+z ∧
        colSp z ≤ H.space i := by
  classical
  choose U V hpin hlow hs ht using hv
  choose E hE hkill using fun i => selected_tensor_extractors (U i) (V i) _ _ (hs i) (ht i)
  let H : RaySeparation v a := ⟨fun i => tensorCross (U i) (V i),E,hE,hkill,hpin⟩
  refine ⟨H,?_⟩
  intro i e
  have hc : Fintype.card (CallsAt v i) ≤ 14 := by
    simpa only [CallsAt,Fintype.card_coe] using v.here_card hb i
  have hM : (x i).val e ∈ Wspace p n := by
    obtain ⟨w,hw,hx⟩ := mem_X.mp (x i).property
    rw [←hx]
    exact (Wspace p n).add_mem ((Wtag_le _) (hw e.val.1)) ((Wtag_le _) (hw e.val.2))
  have hR : ((x i).val e).rank ≤ R :=
    (rank_vanish (vanish_one ho i e)).trans ((Nat.add_le_add
      (v.frozen_here_dim hb a t i (e,true)) (v.frozen_here_dim hb a t i (e,false))).trans
        (by omega))
  let ss (j : CallsAt v i) := selV p.j (v.sel j.val)
  let tt (j : CallsAt v i) := baseV (v.par j.val)
  have hs1 (j : CallsAt v i) : dotProduct (Pi.single emptySel 1) (ss j)=1 := by
    simp [ss,single_dotProduct,selV,emptySel]
  have ht1 (j : CallsAt v i) : dotProduct (Pi.single none 1) (tt j)=1 := by
    simp [tt,single_dotProduct,baseV]
  have hl (c : Bool) (y : Ray p n) (hy : y ∈ sPin a (e,c) i)
      (hr : Matrix.rank (flattenMatrix.symm y) ≤ R^2+Fintype.card (CallsAt v i)) :
      y ∈ tensorRectangle (U i) (V i) := hlow i (e,c) y hy (by omega)
  have hvan : vanish (sPin a (e,true) i ⊔ selectedTensorSpace ss tt)
      (sPin a (e,false) i ⊔ selectedTensorSpace ss tt) ((x i).val e) := by
    apply vanish_enlarge _ (vanish_one ho i e)
    · rw [v.sPin_frozen]
      exact sup_le_sup le_rfl (key_projection_le_selected v t i (e,true))
    · rw [v.sPin_frozen]
      exact sup_le_sup le_rfl (key_projection_le_selected v t i (e,false))
  obtain ⟨c,z,hz,hbox⟩ := protected_tensor_annihilator (U i) (V i)
    (sPin a (e,true) i) (sPin a (e,false) i) ss tt (hs i) (ht i)
    (Pi.single emptySel 1) (Pi.single none 1) hs1 ht1 R (hl true) (hl false)
    ((x i).val e) (Wspace_le_affineTensorSpace p n hM) hR hvan
  exact ⟨c,z,hz,((box_mem ..).mp hbox).1⟩

/-- Cut relations synchronize selected coefficients. The test is an ordinary
linear functional, with no interpolation in selector labels. -/
theorem linear_star_constant {x : Profile p n} (hx : x ∈ Xspace p n)
    (l : Tag p.g) (f : Moment p n →ₗ[F] F)
    (hzero : ∀ e, ¬inc e l → f (x e)=0) :
    ∃ c : F, ∀ e, f (x e)=if inc e l then c else 0 := by
  obtain ⟨w,hw,rfl⟩ := mem_X.mp hx
  exact CycleGeometry.cut_star_constant w l f hzero

end
end Lax793645Proofs.Simplifications
