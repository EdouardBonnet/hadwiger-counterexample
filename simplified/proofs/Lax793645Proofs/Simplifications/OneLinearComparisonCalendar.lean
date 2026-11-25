import Lax793645Proofs.Simplifications.OneLinearQueryTestComparison
import Lax793645Proofs.Simplifications.OneCellPositivityScales

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {q : Format} {d : Rates} {b : Bool} {K s0 : ℕ}
namespace OneQuill

def oneMatchesArea {n N r : ℕ} (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (Y : OneSilhouette p N r) (o : OneUnit p n N) (δ : ℝ):=
  ∀ i,OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) δ

theorem one_gauze_area {n N r : ℕ} (w : Quill p q d b) (t : Tagging p (Messenger q))
    (z : Messenger q→F) (hw : w.moral t z) (Y : OneSilhouette p N r)
    (o : OneUnit p n N) (m : Mixer p n) (δ η : ℝ)
    (h : oneGauze p δ η Y m K o) : oneMatchesArea w t z Y o δ :=
  fun i=>(h (parcel b i) (w.allure t z i)).1 (w.allure_apt t z hw i)

/-- The linear-test accuracy is fixed before n, and is uniform over
charts, orientations, later partition refinements, and bounded cell tests. -/
theorem one_linear_comparison_calendar (w : Quill p q d b)
    (t : Tagging p (Messenger q)) (z : Messenger q→F) (hw : w.moral t z)
    (M : ℕ) (h : OneUnaryParameters p M K s0) (R : ℕ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ δ≤ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),reducedBinaryGood m → ∀ r (Y : OneSilhouette p (M*n) r),
      ∀ (o : OneUnit p n (M*n)),(∀ i,oneFrameLaw m (o i)) →
      oneMatchesArea w t z Y o δ → oneLitFire o →
      ∀ (s : Charts p n d) (L : OneKeys t (M*n)→ₗ[F]Vec (Fin R)),
      OneRefines Y (oneLinearKeyPalette t L) →
      ∀ φ : Wgt (Vec (Fin R)),(∀ x,|φ x|≤1) →
      |oneProwl w t z o m s (φ ∘ L)-oneSheen w t z o m s Y (φ ∘ L)|≤ε := by
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
    with n hn₁ hn₂ hn hN m hm r Y o hframe harea hfire s L hY φ hφ
  have hκ i : IsLaw (w.policies t z n i):=
    Appearance.witLaw (w.allure_apt t z hw i) h.hR hn
  have hcap i v : w.policies t z n i v≤C*unif v:=
    dialCap p _ _ _ h.hR hn (w.allure_apt t z hw i) v
  have hsel : (w.pen t).diffsel:=fun i j hij _ he=>hij (hw.1 he)
  have ht:=one_linear_query_test w t z o m s Y L hY φ hφ hκ hframe h.hJ hm hfire hsel
    C hC hcap harea hN
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
