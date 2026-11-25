import Lax793645Proofs.Simplifications.OneProductComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {K s0:ℕ}

/-- Fixed finite products of unary sets have a positive base-query hit
outside exponentially small mixed mass. No conditioning on compatibility
and no weak-product decomposition occurs in this estimate. -/
theorem one_base_product_relative_hit (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤M) (C:ℝ) (k:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)*n)) →
      (∀ x,u x≤bp (C*(2*N))*oneUnitRaw m N x) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ H:OneKeys t N→Prop,OneDesign t (fun x=>ind (H x)) k →
      ε≤pr (oneLawNu p N t z) H →
      pr u (fun o=>¬OneBaseSober w t z K H m
        (oneDilate w t K*(pr (oneLawNu p N t z) H/4)) o)≤bp (-c*n) := by
  let α:=oneDilate w t K*(ε/4)
  have hα:0<α:=mul_pos (one_dilate_pos ..) (by positivity)
  obtain ⟨θ,hθ,hcal⟩:=one_base_product_comparison_calendar w t z hw M h k α hα
  let r:=onePaletteSize (Messenger q) (Fin k)
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
  refine ⟨1/200,by norm_num,?_⟩
  filter_upwards [hcal,href,one_generic_gauze_calendar r M h δ δ hd hd,
    one_lit_fire_calendar p C M hM,eventually_ge_atTop (max 1 (2*p.r)),
    pay_nat (a:=1/100) 2 (by norm_num : (1/200:ℝ)<1/100),
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2)),
    hz.eventually (eventually_ge_atTop (2*num (Toast p)+1))]
    with n hc href hg hf hn hpay hN hT N m u hu hside hcap hroom hU hB H hdesign hH
  obtain ⟨Y,hY⟩:=hc (fun x=>ind (H x)) hdesign
  have hG:=hg m u hu hside hroom hU Y
  have hF:pr u (fun o=>¬oneLitFire o)≤bp (-(1/100:ℝ)*n):=by
    refine (hf m hroom u hcap).trans (bp_le ?_)
    have hn':(1:ℝ)≤n:=by exact_mod_cast le_trans (le_max_left ..) hn
    nlinarith only [hn']
  have hsub o (ho:¬OneBaseSober w t z K H m
      (oneDilate w t K*(pr (oneLawNu p N t z) H/4)) o):
      (¬oneGenericGauze p δ δ Y m K o) ∨ ¬oneLitFire o:=by
    by_contra! hgood
    apply ho
    intro s hs
    have hh:=one_base_sheen_hit w t z m Y o s H hd (le_refl (pr (oneLawNu p N t z) H)) hw h.hR
      ((le_max_right ..).trans hn) hs hN (by linarith only [hT])
      (by change D*(_+_)≤_; linarith only [hδ,href,hH]) hgood.1
    have htest:=hY m hB r Y (one_refines_self Y) o hs.frame
      (fun i=>(one_generic_gauze_area w t z hw hs.generic Y o m δ δ hgood.1 i).trans (min_le_left ..))
      hgood.2 s
    dsimp only [α] at *
    have hdilate:=one_dilate_pos w t K
    nlinarith only [hh,(abs_le.mp htest).1,hH,hdilate]
  exact ((pr_mono hu.nz hsub).trans (pr_or_le hu.nz)).trans
    ((add_le_add hG hF).trans (by simpa only [two_mul] using hpay))

/-- The gain coefficient is independent of the partition complexity. -/
theorem one_base_product_hit_gain (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤M) (C:ℝ) (k:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)*n)) →
      (∀ x,u x≤bp (C*(2*N))*oneUnitRaw m N x) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ H:OneKeys t N→Prop,OneDesign t (fun x=>ind (H x)) k →
      ε≤pr (oneLawNu p N t z) H →
      pr u (fun o=>¬OneBaseSober w t z K H m (oneDilate w t K*(ε/4)) o)≤bp (-c*n) := by
  obtain ⟨c,hc,hcal⟩:=one_base_product_relative_hit w t z hw M h hM C k ε hε
  refine ⟨c,hc,?_⟩
  filter_upwards [hcal] with n hn N m u hu hs hcap hN hU hB H hdesign hH
  refine (pr_mono hu.nz (fun o ho hgood=>ho (fun a ha=>?_))).trans
    (hn m u hu hs hcap hN hU hB H hdesign hH)
  exact (mul_le_mul_of_nonneg_left (by linarith only [hH]) (one_dilate_pos w t K).le).trans
    (hgood a ha)


theorem one_base_product_hit_calendar (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤M) (C:ℝ) (k:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ α c:ℝ,0<α ∧ 0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)*n)) →
      (∀ x,u x≤bp (C*(2*N))*oneUnitRaw m N x) →
      Fintype.card (Row p n)+2*p.h+3≤N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ H:OneKeys t N→Prop,OneDesign t (fun x=>ind (H x)) k →
      ε≤pr (oneLawNu p N t z) H →
      pr u (fun o=>¬OneBaseSober w t z K H m α o)≤bp (-c*n) := by
  obtain ⟨c,hc,hcal⟩:=one_base_product_hit_gain w t z hw M h hM C k ε hε
  exact ⟨oneDilate w t K*(ε/4),c,mul_pos (one_dilate_pos ..) (by positivity),hc,hcal⟩

end OneQuill
end
end Lax793645Proofs.Simplifications
