import Lax793645Proofs.Simplifications.OneProductTests
import Lax793645Proofs.Simplifications.OneBaseCellComparison
import Lax793645Proofs.Simplifications.OneBaseLinearComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N r k K s0:ℕ}

theorem one_base_paint_query_comparison (w:Quill p q d b) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (A:Fin k→OnePaint t N)
    (hA:∀ j,|(A j).coeff|≤1) (hp:∀ j,OnePigments z Y (A j))
    (hκ:∀ i,IsLaw (w.policies t z n i)) (hframe:∀ i,oneFrameLaw m (o i))
    (hj:1≤p.j) (hm:reducedBinaryGood m) (hfire:oneLitFire o) (hsel:(w.pen t).diffsel)
    (C:ℝ) (hC:0<C) (hcap:∀ i x,w.policies t z n i x≤C*unif x)
    {ε:ℝ} (hclose:oneMatchesArea w t z Y o ε)
    (hN:2*num (Messenger q×Toast p)+2≤(N:ℝ)):
    |oneBaseProwl w t z s m o (oneMural A)-oneBaseSheen w t z o m s Y (oneMural A)|≤
      k*(C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)) := by
  choose f hf using hp
  let U (j:Fin k) (i:Messenger q) (c:Fin r):=ind (f j i c=true)
  have hU j i c:|U j i c|≤1:=by
    rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have he:oneMural A=fun x=>∑ j,(A j).coeff*prodW (oneCellTest t z Y (U j)) x:=by
    funext x
    apply sum_congr rfl
    intro j _
    congr 1
    apply prod_congr rfl
    intro i _
    change ind ((A j).flies i (x i))=ind (f j i (Y (t i) (z i) (x i))=true)
    rw [hf j i]
  rw [he,one_base_prowl_linear_sum,one_base_sheen_linear_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _j:Fin k,(C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)):=by
      apply sum_le_sum
      intro j _
      rw [←mul_sub,abs_mul]
      exact ((mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)).trans_eq (one_mul _)).trans
        (one_base_cell_query_comparison w t z o m s Y (U j) (hU j) hκ hframe hj hm hfire hsel
          C hC hcap hclose hN)
    _ = _:=by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Exact finite products, with arbitrary unary sets, need only a
bounded palette and direct binary mixing. -/
theorem one_base_product_comparison_calendar (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (k:ℕ) (ε:ℝ) (hε:0<ε):
    ∃ δ:ℝ,0<δ ∧ ∀ᶠ n:ℕ in atTop,
      ∀ W:Wgt (OneKeys t (M*n)),OneDesign t W k →
      ∃ X:OneSilhouette p (M*n) (onePaletteSize (Messenger q) (Fin k)),
      ∀ (m:Mixer p n),reducedBinaryGood m → ∀ r (Y:OneSilhouette p (M*n) r),
      OneRefines Y X → ∀ o:OneUnit p n (M*n),(∀ i,oneFrameLaw m (o i)) →
      oneMatchesArea w t z Y o δ → oneLitFire o → ∀ s:Charts p n d,
      |oneBaseProwl w t z s m o W-oneBaseSheen w t z o m s Y W|≤ε := by
  let D:ℝ:=k
  let x:=2+num (Messenger q)
  let δ:=ε/((D+1)*x)
  have hD:0≤D:=by dsimp [D,num]; positivity
  have hx:0<x:=by dsimp [x,num]; positivity
  have hd:0<δ:=div_pos hε (mul_pos (by positivity) hx)
  let C:=(scanPrice p)⁻¹
  have hC:0<C:=inv_pos_of_pos (scanPrice_pos p)
  have hz:=(trend_sizes atTop le_rfl h.hM).2
  have h₁:∀ᶠ n:ℕ in atTop,C^2*bp (-(n:ℝ)/10)≤δ:=by
    have he:=(bp_nat_vanish (by norm_num:0<(1/10:ℝ))).const_mul (C^2)
    filter_upwards [he.eventually (eventually_le_nhds (by simpa only [mul_zero] using hd))] with n hn
    simpa only [show -(1/10:ℝ)*n= -(n:ℝ)/10 from by ring] using hn
  have h₂:∀ᶠ n:ℕ in atTop,2*quadraticNetFact (trayPort p t)*bp (-((M*n:ℕ):ℝ)/2)≤δ:=by
    have he:=((bp_tendsto_zero (by norm_num:0<(1/2:ℝ))).comp hz).const_mul
      (2*quadraticNetFact (trayPort p t))
    filter_upwards [he.eventually (eventually_le_nhds (by simpa only [mul_zero] using hd))] with n hn
    simpa only [Function.comp_apply,show -(1/2:ℝ)*((M*n:ℕ):ℝ)= -((M*n:ℕ):ℝ)/2 from by ring] using hn
  refine ⟨δ,hd,?_⟩
  filter_upwards [h₁,h₂,eventually_ge_atTop (2*p.r),
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2))]
    with n hn₁ hn₂ hn hN W hW
  obtain ⟨F,rfl,hF⟩:=hW
  obtain ⟨X,hX⟩:=one_build_palette t z F
  refine ⟨X,?_⟩
  intro m hm r Y hY o hframe harea hfire s
  have hκ i:IsLaw (w.policies t z n i):=Appearance.witLaw (w.allure_apt t z hw i) h.hR hn
  have hcap i v:w.policies t z n i v≤C*unif v:=
    dialCap p _ _ _ h.hR hn (w.allure_apt t z hw i) v
  have hsel:(w.pen t).diffsel:=fun i j hij _ he=>hij (hw.1 he)
  let cost:=C^2*bp (-(n:ℝ)/10)+num (Messenger q)*δ+
    2*quadraticNetFact (trayPort p t)*bp (-((M*n:ℕ):ℝ)/2)
  have hc : |oneBaseProwl w t z s m o (oneMural F)-
      oneBaseSheen w t z o m s Y (oneMural F)|≤k*cost:=
    one_base_paint_query_comparison w t z o m s Y F hF
      (fun j=>one_finer_pigment hY (F j) (hX j)) hκ hframe h.hJ hm hfire hsel C hC hcap harea hN
  apply hc.trans
  have ha:cost≤x*δ:=by dsimp [cost,x]; linarith only [hn₁,hn₂]
  have he:(D+1)*(x*δ)=ε:=by dsimp [δ]; field_simp
  exact (mul_le_mul_of_nonneg_left ha hD).trans
    ((mul_le_mul_of_nonneg_right (by linarith:D≤D+1) (mul_pos hx hd).le).trans_eq he)

end OneQuill
end
end Lax793645Proofs.Simplifications
