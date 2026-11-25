import Lax793645Proofs.Simplifications.OnePredictedRareEvents
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.HistogramBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {n N K:ℕ} {q:Format} {d:Rates} {b:Bool}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)
    (pin:ImagePlan (Comp p.g) (OneColumn p n)) (K:ℕ)
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop) (m:Mixer p n) (s:Charts p n d)

def oneBillboard (o:OneUnit p n N) (x:Inputs p n (Messenger q)):Bool:=
  decide (OneProtectedInput (w.pen t) pin K x ∧ oneDeposit w t z m o s x)
def oneCustomer:=fromFlags μ ((w.pen t).state z n)
  (oneBillboard w t z pin K m s) (oneResultKey (w.pen t))
def oneCustom:=hung (oneCustomer w t z pin K μ m s) (oneOwnKeyPart t z)

theorem one_good_natural_core:
    oneGoodHistogram w t z pin K μ P m s=
      flaggedW μ ((w.pen t).state z n) (oneBillboard w t z pin K m s)
        (oneResultKey (w.pen t)) (fun o b=>P o ∧ b=true) := by
  apply weights_eq_of_tests
  intro f
  change avg (inputHistogram _ _ _ _) f=_
  rw [input_histogram_mean,avg_avg,flaggedW,mixW_avg]
  apply avg_congr
  intro o _
  rw [mapW_avg]
  unfold avg subW
  apply sum_congr rfl
  intro x _
  simp only [Function.comp_apply,oneBillboard,decide_eq_true_eq,ind_and]
  change _= ((w.pen t).state z n x)*(ind (P o)*(ind (OneProtectedInput (w.pen t) pin K x)*ind (oneDeposit w t z m o s x)))*f (oneVolleyKeys ((w.pen t).draw x) t o)
  ring

theorem one_good_natural_carried:
    carried (oneGoodHistogram w t z pin K μ P m s) (oneOwnKeyPart t z) := by
  intro k hk
  change avg _ (fun x=>pr μ _) =0
  have he x:pr μ (fun o=>(OneProtectedInput (w.pen t) pin K x ∧ P o ∧ oneDeposit w t z m o s x) ∧
      oneVolleyKeys ((w.pen t).draw x) t o=k)=0:=by
    have h o:¬((OneProtectedInput (w.pen t) pin K x ∧ P o ∧ oneDeposit w t z m o s x) ∧
      oneVolleyKeys ((w.pen t).draw x) t o=k):=by
      rintro ⟨⟨_,_,hD⟩,hkey⟩
      exact hk (hkey ▸ hD.2.2)
    simp only [pr,ind_zero (h _),avg_const,mul_zero]
  simp_rw [he]
  rw [avg_const,mul_zero]

theorem one_good_natural_custom:
    oneCustom w t z pin K μ m s (oneGoodHistogram w t z pin K μ P m s) := by
  let v:=oneGoodHistogram w t z pin K μ P m s
  refine ⟨v,⟨_,one_good_natural_core w t z pin K μ P m s⟩,?_⟩
  funext k
  change v k=v k*ind (oneOwnKeyPart t z k)
  by_cases hk:oneOwnKeyPart t z k
  · rw [ind_one hk,mul_one]
  rw [show v k=0 from one_good_natural_carried w t z pin K μ P m s k hk,zero_mul]

theorem one_good_natural_nonneg (hμ:∀ o,0≤μ o):
    ∀ x,0≤oneGoodHistogram w t z pin K μ P m s x:=
  fun _=>avg_nonneg (prodW_nonneg fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _))
    (fun _=>pr_nonneg hμ)

theorem one_good_natural_mono_filter (Q:OneUnit p n N→Prop)
    (hμ:∀ o,0≤μ o) (hPQ:∀ o,P o → Q o):
    ∀ x,oneGoodHistogram w t z pin K μ P m s x≤oneGoodHistogram w t z pin K μ Q m s x := by
  intro x
  apply avg_mono (prodW_nonneg fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _))
  exact fun _=>pr_mono hμ (fun o ho=>⟨⟨ho.1.1,hPQ o ho.1.2.1,ho.1.2.2⟩,ho.2⟩)

theorem one_good_natural_rejection (hμ:SubLaw μ) (hpen:OnePenSpace (w.pen t) pin K)
    (hκ:∀ i,IsLaw (w.policies t z n i)):
    (∀ k,0≤oneGoodHistogram w t z pin K μ P m s k ∧
      oneGoodHistogram w t z pin K μ P m s k≤oneNaturalSales w t z μ P m s k) ∧
    varOne (oneNaturalSales w t z μ P m s) (oneGoodHistogram w t z pin K μ P m s)≤
      bp (num (Messenger q)+oneBaseProtectionDim p K-n) := by
  rw [oneNaturalSales,one_sales_histogram]
  exact input_histogram_rejection (fun x=>oneVolleyKeys ((w.pen t).draw x) t)
    μ ((w.pen t).state z n) (fun x o=>P o ∧ oneDeposit w t z m o s x)
    (OneProtectedInput (w.pen t) pin K) _ hμ (prodW_law hκ).nz
    (one_query_rejection (w.pen t) pin K hpen z hκ)

/-- Rejection and prediction errors lower a fixed conditional hit
threshold. They are never divided by compatible-pair mass. -/
theorem one_protected_predicted_hit (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E H:OneKeys t N→Prop) (hHE:∀ x,H x → E x)
    {a h:ℝ} (hh:0<h)
    (hq:OnePredictedQualified w t z s m K μ P a α g ε E)
    (hμ:IsLaw μ) (hw:w.moral t z) (hr:1≤p.r) (hn:2*p.r≤n)
    (hpen:OnePenSpace (w.pen t) pin K)
    (herr:Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε)≤h)
    (hreject:bp (num (Messenger q)+oneBaseProtectionDim p K-n)≤a*h)
    (hbad:pr μ (fun o=>¬OneBaseSober w t z K H m (4*h) o)≤a):
    a*h≤pr (oneGoodHistogram w t z pin K μ P m s) H := by
  have hfull:=one_predicted_qualify_hit w t z s m K μ P α g ε E H hHE
    (h:=2*h) (by positivity) hq hμ hw hr hn (herr.trans (by linarith))
    (by simpa only [show 2*(2*h)=4*h from by ring] using hbad)
  have hmass:=(one_good_natural_rejection w t z pin K μ P m s hμ.sub hpen
    (fun i=>Appearance.witLaw (w.allure_apt t z hw i) hr hn)).2
  have hgap:=(var_pr _ _ H).trans hmass
  nlinarith only [hfull,hgap,hreject]

end OneQuill
end
end Lax793645Proofs.Simplifications
