import Lax793645Proofs.Simplifications.BaseQueries

/-! The whole-key comparison remains valid after omitting the predicted bits.
There are finitely many bit completions; use a common refinement and sum the
unnormalized query measures. The two leaf draws are not conditioned here. -/
namespace Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
open Filter Finset Matrix Function
open scoped BigOperators Topology
namespace StatusAnalysis.Quill
variable {p : Shape} {q : Format} {d : Rates} {b : Bool} {n N M r s0 : ℕ}
  {b' : PreparationParameters}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

private theorem positive_minimum {A : Type} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 < f a) : ∃ c : ℝ, 0 < c ∧ ∀ a, c ≤ f a := by
  classical
  cases isEmpty_or_nonempty A
  next he => exact ⟨1,zero_lt_one,fun i => (he.false i).elim⟩
  next he =>
    let S := univ.image f
    have hn : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    obtain ⟨a,ha,hv⟩ := mem_image.mp (Finset.min'_mem S hn)
    exact ⟨S.min' hn,hv ▸ hf a,fun a => Finset.min'_le S (f a)
      (mem_image_of_mem f (mem_univ a))⟩

def baseFlunk (Y : Silhouette p N r) (W : Wgt (Keys (p:=p) t N)) (m : Mixer p n)
    (δ ε : ℝ) (o : UnitType p n N) : Prop :=
  PreparationParameters.frameSide p m o ∧ w.matchesArea t z Y o δ ∧
    ∃ s : Charts p n d, ε < |w.baseProwl t z s m o W-w.baseSheen t z o m s Y W|

def baseMarkedTest (M : ℕ) (b' : PreparationParameters) (s0 n : ℕ) {r}
    (X : Silhouette p (M*n) r) (W : Wgt (Keys (p:=p) t (M*n))) (L u ε : ℝ) :=
  ∀ r' : ℕ, ∀ Y : Silhouette p (M*n) r', refines Y X →
    ∀ (m : Mixer p n) (U : Wgt (UnitType p n (M*n))), b'.Align s0 p M n m U →
      pr U (w.baseFlunk t z Y W m u ε) ≤ L

theorem baseSideRelease (M : ℕ) (h : QueryParameters p M b' s0)
    (hw : w.moral t z) (ε : ℝ) (he : 0 < ε) :
    ∃ (l : ℕ) (u c : ℝ), 0 < u ∧ 0 < c ∧
      ∀ᶠ n : ℕ in atTop, ∀ W : Wgt (Keys (p:=p) t (M*n)),
        (∀ x, |W x| ≤ 1) → ∃ X : Silhouette p (M*n) l,
          w.baseMarkedTest t z M b' s0 n X W (bp (-c*n)) u ε := by
  classical
  let A := Messenger q → F
  let D : ℝ := num A
  have hD : 0 < D := by unfold D num A; positivity
  let a := ε/D
  have ha : 0 < a := div_pos he hD
  choose r u c hu hc hg using fun e : A =>
    (w.withInk e).sideRelease t z M h (w.withInk_moral t z e hw) a ha
  obtain ⟨v,hv,hvu⟩ := positive_minimum u hu
  obtain ⟨C,hC,hCc⟩ := positive_minimum c hc
  refine ⟨bouquet r,v,C/2,hv,half_pos hC,?_⟩
  filter_upwards [eventually_all.mpr hg, pay_nat (a:=C) (Fintype.card A) (half_lt_self hC)]
    with n hn hpay W hW
  choose X hX using fun e : A => hn e W hW
  refine ⟨bundleY r X,fun r' Y hY m U hU => ?_⟩
  have hE (e : A) : pr U ((w.withInk e).flunk t z Y W m (u e) a) ≤ bp (-C*n) := by
    refine (hX e r' Y (refines_next hY (bundle_refines r X e)) m U hU).trans ?_
    exact bp_le (mul_le_mul_of_nonneg_right (neg_le_neg (hCc e)) (Nat.cast_nonneg n))
  have hsub o (ho : w.baseFlunk t z Y W m v ε o) :
      ∃ e : A, (w.withInk e).flunk t z Y W m (u e) a o := by
    obtain ⟨hframe,harea,s,hs⟩ := ho
    by_contra! hh
    have heach (e : A) :
        |(w.withInk e).prowl s t z m o W-(w.withInk e).sheen t z o m s Y W| ≤ a := by
      apply le_of_not_gt
      intro hn
      exact hh e ⟨hframe, w.area_mono t z Y harea (hvu e),s,hn⟩
    rw [baseProwl_ink,baseSheen_ink,← Finset.sum_sub_distrib] at hs
    have ht := (abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum fun e _ => heach e)
    have heq : (∑ _e : A, a) = ε := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
      change D*(ε/D)=ε
      field_simp
    exact hs.not_ge (ht.trans_eq heq)
  refine ((pr_mono hU.drain.1.nz hsub).trans (pr_exists_le hU.drain.1.nz _)).trans ?_
  refine (Finset.sum_le_sum fun e _ => hE e).trans ?_
  simpa only [sum_const,card_univ,nsmul_eq_mul] using hpay

end StatusAnalysis.Quill
end
end Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
