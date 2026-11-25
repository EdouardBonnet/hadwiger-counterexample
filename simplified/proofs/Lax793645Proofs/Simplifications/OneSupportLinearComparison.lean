import Lax793645Proofs.Simplifications.OneSupportProductBounds
import Lax793645Proofs.Simplifications.OnePositiveCellTests
import Lax793645Proofs.Simplifications.OneLinearComparisonCalendar

/-! Whole-tuple domination for linear partitions, at a height fixed before the partition complexity and accuracy. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneQuill
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

variable (θ : ℝ)
theorem one_support_linear_query_domination {R : ℕ}
    (hθ : 0≤θ ∧ θ≤1) (L : OneKeys t N→ₗ[F]Vec (Fin R))
    (hY : OneRefines Y (oneLinearKeyPalette t L))
    (φ : Wgt (Vec (Fin R))) (hφ : ∀ x,0≤φ x ∧ φ x≤1)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hframe : ∀ i,oneFrameLaw m (o i))
    (hj : 1≤p.j) (hm : reducedBinaryGood m) (hfire : oneLitFire o) (hsel : (w.pen t).diffsel)
    (C : ℝ) (hC : 0<C) (hcap : ∀ i x,w.policies t z n i x≤C*unif x)
    {ε : ℝ} (hε : 0≤ε)
    (hclose : ∀ i,OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε)
    (hdom : ∀ i k,oneSupportSeraph w t z o m s Y θ i k≤oneSeraph w t z o m s Y i k)
    (hN : 2*num ((Messenger q)×Toast p)+2≤(N:ℝ)) :
    oneSupportSheen w t z o m s Y θ (φ ∘ L)-oneProwl w t z o m s (φ ∘ L)≤
      num (Messenger q→Vec (Fin R))*(C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)) := by
  obtain ⟨U,hU,hdecomp⟩:=one_linear_positive_expansion t z L Y hY
  have hf : φ ∘ L=fun x=>∑ a : Messenger q→Vec (Fin R),
      φ (∑ i,a i)*prodW (oneCellTest t z Y (U a)) x := funext (hdecomp φ)
  have hs {I : Type} [Fintype I] (c : Wgt I) (W : I→Wgt (OneKeys t N)) :
      oneSupportSheen w t z o m s Y θ (fun x=>∑ i,c i*W i x)=
        ∑ i,c i*oneSupportSheen w t z o m s Y θ (W i) := by
    unfold oneSupportSheen
    simp only [Finset.mul_sum,avg_sum]
    apply sum_congr rfl
    intro i _
    rw [←avg_mul']
    exact avg_congr (fun x _=>by ring)
  rw [hf,hs,one_prowl_linear_sum,←sum_sub_distrib]
  let E:=C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
    2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)
  have hE : 0≤E := by
    unfold E
    have hfact : 0≤quadraticNetFact (trayPort p t):=(quadratic_net_fact_pos _).le
    have hn : 0≤num (Messenger q):=by unfold num; positivity
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg C) (bp_pos _).le)
      (mul_nonneg hn hε)) (mul_nonneg (mul_nonneg (by norm_num) hfact) (bp_pos _).le)
  calc
    _ ≤ ∑ _ : Messenger q→Vec (Fin R),E := by
      apply sum_le_sum
      intro a _
      rw [←mul_sub]
      exact (mul_le_mul_of_nonneg_left
        (one_support_cell_query_domination w t z o m s Y θ (U a) hθ (hU a)
          hκ hframe hj hm hfire hsel C hC hcap hε hclose hdom hN) (hφ _).1).trans
        (mul_le_of_le_one_left hE (hφ _).2)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,num,E]

theorem one_support_domination_certificate {R K : ℕ}
    (hg : Odd p.g) (hY : OneFullLinearSilhouette Y R)
    (hd : ∀ i,d i≤K^2)
    (hs : ∀ i j,totalRank (s i (Pi.single j 1))≤K)
    (hw : ∀ i,IsLaw (w.policies t z n i)) :
    ∀ i x,oneSupportSeraph w t z o m s Y
      (bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))) i x≤oneSeraph w t z o m s Y i x := by
  intro i x
  apply support_lower_domination
  · exact (one_seraph_floor w t z o m s Y i (hw i) x).1
  · intro hx
    exact one_reflected_status_atom_bound hg K (hd _) Y hY (w.allure t z i)
      (parcel b i) o m (s (parcel b i)) (hs _) (Y (t i) (z i) x) (w.amp i) hx

theorem one_support_linear_comparison_calendar (w : Quill p q d b)
    (t : Tagging p (Messenger q)) (z : Messenger q→F) (hw : w.moral t z)
    (M K s0 : ℕ) (h : OneUnaryParameters p M K s0) (R : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ δ≤ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),reducedBinaryGood m → ∀ r (Y : OneSilhouette p (M*n) r),
      ∀ (o : OneUnit p n (M*n)),(∀ i,oneFrameLaw m (o i)) →
      oneMatchesArea w t z Y o δ → oneLitFire o →
      ∀ (s : Charts p n d) (T : ℕ),OneFullLinearSilhouette Y T →
      (∀ i,d i≤K^2) → (∀ i j,totalRank (s i (Pi.single j 1))≤K) →
      ∀ (L : OneKeys t (M*n)→ₗ[F]Vec (Fin R)),
      OneRefines Y (oneLinearKeyPalette t L) →
      ∀ φ : Wgt (Vec (Fin R)),(∀ x,0≤φ x ∧ φ x≤1) →
      oneSupportSheen w t z o m s Y (bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))) (φ ∘ L)-
        oneProwl w t z o m s (φ ∘ L)≤ε := by
  let k:=num (Messenger q→Vec (Fin R))
  let x:=2+num (Messenger q)
  let δ:=ε/((k+1)*x)
  have hk : 0≤k:=by dsimp only [k,num]; positivity
  have hx : 2≤x:=by dsimp only [x,num]; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Messenger q))]
  have hden : 1≤(k+1)*x:=by nlinarith
  have hd : 0<δ:=div_pos hε (lt_of_lt_of_le zero_lt_one hden)
  have hdε : δ≤ε:= (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
    (by nlinarith)
  let C:=(scanPrice p)⁻¹
  have hC : 0<C:=inv_pos_of_pos (scanPrice_pos p)
  have hz:=(trend_sizes atTop (le_refl _) h.hM).2
  have h₁ : ∀ᶠ n : ℕ in atTop,C^2*bp (-(n:ℝ)/10)≤δ := by
    have he:=(bp_nat_vanish (by norm_num : 0<(1/10:ℝ))).const_mul (C^2)
    filter_upwards [he.eventually (eventually_le_nhds (by simpa only [mul_zero] using hd))]
      with n hn
    simpa only [show -(1/10:ℝ)*n= -(n:ℝ)/10 from by ring] using hn
  have h₂ : ∀ᶠ n : ℕ in atTop,
      2*quadraticNetFact (trayPort p t)*bp (-((M*n:ℕ):ℝ)/2)≤δ := by
    have he:=((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul
      (2*quadraticNetFact (trayPort p t))
    filter_upwards [he.eventually (eventually_le_nhds (by simpa only [mul_zero] using hd))]
      with n hn
    simpa only [Function.comp_apply,show -(1/2:ℝ)*((M*n:ℕ):ℝ)= -((M*n:ℕ):ℝ)/2 from by ring] using hn
  refine ⟨δ,hd,hdε,?_⟩
  filter_upwards [h₁,h₂,eventually_ge_atTop (2*p.r),
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2))]
    with n hn₁ hn₂ hn hN m hm r Y o hframe harea hfire s T hfull hdims hcharts L hY φ hφ
  have hκ i : IsLaw (w.policies t z n i):=
    Appearance.witLaw (w.allure_apt t z hw i) h.hR hn
  have hcap i v : w.policies t z n i v≤C*unif v:=
    dialCap p _ _ _ h.hR hn (w.allure_apt t z hw i) v
  have hsel : (w.pen t).diffsel:=fun i j hij _ he=>hij (hw.1 he)
  have hθ : 0≤bp (-(oneStatusCoordinateBound p (K^2) K:ℝ)) ∧
      bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))≤1:=
    ⟨(bp_pos _).le,(bp_le (neg_nonpos.mpr (Nat.cast_nonneg _))).trans_eq (by simp [bp])⟩
  have hdom:=one_support_domination_certificate w t z o m s Y h.hg hfull hdims hcharts hκ
  have ht:=one_support_linear_query_domination w t z o m s Y
    (bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))) hθ L hY φ hφ hκ hframe h.hJ hm hfire hsel
    C hC hcap hd.le harea hdom hN
  apply ht.trans
  have ha : C^2*bp (-(n:ℝ)/10)+num (Messenger q)*δ+
      2*quadraticNetFact (trayPort p t)*bp (-((M*n:ℕ):ℝ)/2)≤x*δ := by
    dsimp only [x]
    linarith
  have he : (k+1)*(x*δ)=ε := by dsimp only [δ]; field_simp
  exact (mul_le_mul_of_nonneg_left ha hk).trans
    ((mul_le_mul_of_nonneg_right (by linarith : k≤k+1) (by positivity : 0≤x*δ)).trans_eq he)



end OneQuill

end
end Lax793645Proofs.Simplifications
