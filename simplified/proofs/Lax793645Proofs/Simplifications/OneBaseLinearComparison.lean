import Lax793645Proofs.Simplifications.OneBaseSurrogateHits
import Lax793645Proofs.Simplifications.OneSimultaneousScores

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {K s0:ℕ}

theorem one_base_linear_comparison_calendar (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (R:ℕ) (ε:ℝ) (hε:0<ε):
    ∃ δ:ℝ,0<δ ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (m:Mixer p n),reducedBinaryGood m → ∀ r (Y:OneSilhouette p (M*n) r),
      ∀ o:OneUnit p n (M*n),(∀ i,oneFrameLaw m (o i)) →
      oneMatchesArea w t z Y o δ → oneLitFire o →
      ∀ (s:Charts p n d) (L:OneKeys t (M*n)→ₗ[F]Vec (Fin R)),
      OneRefines Y (oneLinearKeyPalette t L) →
      ∀ φ:Wgt (Vec (Fin R)),(∀ x,|φ x|≤1) →
      |oneBaseProwl w t z s m o (φ ∘ L)-oneBaseSheen w t z o m s Y (φ ∘ L)|≤ε := by
  let A:=Messenger q→F
  let D:ℝ:=num A
  have hD:0<D:=by dsimp [D,num]; positivity
  let a:=ε/D
  have ha:0<a:=div_pos hε hD
  choose θ hθ hθε hcal using fun e:A=>one_linear_comparison_calendar
    (w.withInk e) t z (w.withInk_moral t z e hw) M h R a ha
  obtain ⟨δ,hd,hmin⟩:=one_finite_positive_min θ hθ
  refine ⟨δ,hd,?_⟩
  filter_upwards [eventually_all.mpr hcal] with n hn m hm r Y o hframe harea hfire s L hY φ hφ
  rw [one_base_prowl_ink,one_base_sheen_ink,←Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun _=>a) fun e _=>?_).trans_eq ?_)
  · exact hn e m hm r Y o hframe (fun i=>(harea i).trans (hmin e)) hfire s L hY φ hφ
  · simp only [Finset.sum_const,card_univ,nsmul_eq_mul]
    change D*(ε/D)=ε
    field_simp

def OneBaseSober {n N:ℕ} (w:Quill p q d b) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (K:ℕ) (H:OneKeys t N→Prop) (m:Mixer p n) (α:ℝ)
    (o:OneUnit p n N):=
  ∀ s:Charts p n d,OneBaseSteady w m K s o →
    α≤oneBaseProwl w t z s m o (fun k=>ind (H k))

/-- Large linear cells are hit uniformly outside exponentially small
prepared mixed mass. The event quantifies over every effective-space chart. -/
theorem one_base_linear_hit_calendar (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤M) (C:ℝ) (R:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ α c:ℝ,0<α ∧ 0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)*n)) →
      (∀ x,u x≤bp (C*(2*N))*oneUnitRaw m N x) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ (L:OneKeys t N→ₗ[F]Vec (Fin R)) (P:Vec (Fin R)→Prop),
      ε≤pr (oneLawNu p N t z) (P ∘ L) →
      pr u (fun o=>¬OneBaseSober w t z K (P ∘ L) m α o)≤bp (-c*n) := by
  let α:=oneDilate w t K*(ε/4)
  have hα:0<α:=mul_pos (one_dilate_pos ..) (by positivity)
  obtain ⟨θ,hθ,hcal⟩:=one_base_linear_comparison_calendar w t z hw M h R α hα
  let r:=oneLinearPaletteSize (Messenger q) R
  let D:ℝ:=num (Messenger q)
  have hD:0≤D:=Nat.cast_nonneg _
  let δ:=min θ (ε/(4*(D+1)*(r+1:ℝ)))
  have hd:0<δ:=lt_min hθ (by positivity)
  have hδ:D*(r:ℝ)*δ≤ε/4:=by
    have hi:δ*(4*(D+1)*(r+1:ℝ))≤ε:=
      (le_div_iff₀ (by positivity)).mp (min_le_right ..)
    have hh:D*(r:ℝ)≤(D+1)*(r+1:ℝ):=mul_le_mul (by linarith) (by linarith)
      (Nat.cast_nonneg _) (by linarith)
    linarith only [hi,mul_le_mul_of_nonneg_right hh hd.le]
  have hz:=(trend_sizes atTop le_rfl h.hM).2
  have href:∀ᶠ n:ℕ in atTop,
      D*(2*quadraticNetFact (trayPort p t)*bp (-((M*n:ℕ):ℝ)/2))≤ε/4:=by
    have hh:=(((bp_tendsto_zero (by norm_num:0<(1/2:ℝ))).comp hz).const_mul
      (2*quadraticNetFact (trayPort p t))).const_mul D
    filter_upwards [hh.eventually (eventually_le_nhds (by simpa only [mul_zero] using div_pos hε (by norm_num:0<(4:ℝ))))]
      with n hn
    simpa only [mul_zero,Function.comp_apply,
      show -(1/2:ℝ)*((M*n:ℕ):ℝ)= -((M*n:ℕ):ℝ)/2 from by ring] using hn
  refine ⟨α,1/200,hα,by norm_num,?_⟩
  filter_upwards [hcal,href,one_generic_gauze_calendar r M h δ δ hd hd,
    one_lit_fire_calendar p C M hM,eventually_ge_atTop (max 1 (2*p.r)),
    pay_nat (a:=1/100) 2 (by norm_num : (1/200:ℝ)<1/100),
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2)),
    hz.eventually (eventually_ge_atTop (2*num (Toast p)+1))]
    with n hc href hg hf hn hpay hN hT N m u hu hside hcap hroom hU hB L P hH
  let Y:=oneLinearKeyPalette t L
  have hY:OneRefines Y (oneLinearKeyPalette t L):=one_refines_self Y
  have hG:=hg m u hu hside hroom hU Y
  have hF:pr u (fun o=>¬oneLitFire o)≤bp (-(1/100:ℝ)*n):=by
    refine (hf m hroom u hcap).trans (bp_le ?_)
    have hn':(1:ℝ)≤n:=by exact_mod_cast le_trans (le_max_left ..) hn
    nlinarith only [hn']
  have hsub o (ho:¬OneBaseSober w t z K (P ∘ L) m α o):
      (¬oneGenericGauze p δ δ Y m K o) ∨ ¬oneLitFire o:=by
    by_contra! hgood
    apply ho
    intro s hs
    have hh:=one_base_sheen_hit w t z m Y o s (P ∘ L) hd hH hw h.hR
      ((le_max_right ..).trans hn) hs hN (by linarith only [hT])
      (by change D*(_+_)≤_; linarith only [hδ,href]) hgood.1
    have htest:=hc m hB r Y o hs.frame
      (fun i=>(one_generic_gauze_area w t z hw hs.generic Y o m δ δ hgood.1 i).trans (min_le_left ..))
      hgood.2 s L hY (fun y=>ind (P y))
      (fun y=>(abs_of_nonneg (ind_nonneg _)).le.trans (ind_le_one _))
    change |oneBaseProwl w t z s m o (fun k=>ind ((P ∘ L) k))-
      oneBaseSheen w t z o m s Y (fun k=>ind ((P ∘ L) k))|≤α at htest
    dsimp only [α] at *
    linarith only [hh,(abs_le.mp htest).1]
  exact ((pr_mono hu.nz hsub).trans (pr_or_le hu.nz)).trans
    ((add_le_add hG hF).trans (by simpa only [two_mul] using hpay))

end OneQuill
end
end Lax793645Proofs.Simplifications
