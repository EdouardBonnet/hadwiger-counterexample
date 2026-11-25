import Lax793645Proofs.Simplifications.BaseQueryComparison
import Lax793645Proofs.Simplifications.ExactPaintComparisons

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Template Filter Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {q : Format} {d : Rates} {b : Bool}
  {b' : PreparationParameters} {s0 : ℕ}

/-- Omitting the predicted statuses preserves the direct comparison for
an exact finite sum of unary products. All measures stay unnormalized. -/
theorem exact_base_paint_side_release (w : Quill p q d b)
    (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (M : ℕ) (h : QueryParameters p M b' s0) (hw : w.moral t z)
    (K : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (r : ℕ) (u c : ℝ),0<u ∧ 0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : Wgt (Keys (p:=p) t (M*n)),design (w.pen t) W 1 K →
      ∃ X : Silhouette p (M*n) r,
        w.baseMarkedTest t z M b' s0 n X W (bp (-c*n)) u ε := by
  let A:=Messenger q→F
  let D : ℝ:=num A
  have hD : 0<D:=by dsimp only [D,num]; positivity
  let a:=ε/D
  have ha : 0<a:=div_pos hε hD
  choose u hu hg using fun e : A=>exact_paint_side_release (w.withInk e) t z M h
    (w.withInk_moral t z e hw) K a ha
  obtain ⟨v,hv,hvu⟩ : ∃ v : ℝ,0<v ∧ ∀ e,v≤u e := by
    let S:=Finset.univ.image u
    have hn : S.Nonempty:=Finset.image_nonempty.mpr Finset.univ_nonempty
    obtain ⟨e,he,hval⟩:=Finset.mem_image.mp (Finset.min'_mem S hn)
    exact ⟨S.min' hn,hval ▸ hu e,fun e=>Finset.min'_le S (u e)
      (Finset.mem_image_of_mem u (Finset.mem_univ e))⟩
  let r:=fun _ : A=>paletteSize (Messenger q) (Fin K)
  refine ⟨bouquet r,v,1/200,hv,by norm_num,?_⟩
  filter_upwards [eventually_all.mpr hg,
    pay_nat (a:=(1/100:ℝ)) (Fintype.card A) (by norm_num : (1/200:ℝ)<1/100)]
    with n hn hpay W hW
  choose X hX using fun e : A=>hn e W hW
  refine ⟨bundleY r X,fun r' Y hY m U hU=>?_⟩
  have hE (e : A) : pr U ((w.withInk e).flunk t z Y W m (u e) a)
      ≤bp (-(1/100:ℝ)*n) :=
    hX e r' Y (refines_next hY (bundle_refines r X e)) m U hU
  have hsub o (ho : w.baseFlunk t z Y W m v ε o) :
      ∃ e : A,(w.withInk e).flunk t z Y W m (u e) a o := by
    obtain ⟨hframe,harea,s,hs⟩:=ho
    by_contra! hh
    have heach (e : A) :
        |(w.withInk e).prowl s t z m o W-(w.withInk e).sheen t z o m s Y W|≤a := by
      apply le_of_not_gt
      intro hn
      exact hh e ⟨hframe,w.area_mono t z Y harea (hvu e),s,hn⟩
    rw [Quill.baseProwl_ink,Quill.baseSheen_ink,←Finset.sum_sub_distrib] at hs
    have ht:=(abs_sum_le_sum_abs _ Finset.univ).trans
      (Finset.sum_le_sum fun e _=>heach e)
    have heq : (∑ _e : A,a)=ε := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change D*(ε/D)=ε
      field_simp
    exact hs.not_ge (ht.trans_eq heq)
  refine ((pr_mono hU.drain.1.nz hsub).trans (pr_exists_le hU.drain.1.nz _)).trans ?_
  refine (Finset.sum_le_sum fun e _=>hE e).trans ?_
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hpay

end
end Lax793645Proofs.Simplifications
