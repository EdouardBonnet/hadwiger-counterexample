import Lax793645Proofs.Simplifications.OneGenericQueryBounds
import Lax793645Proofs.Simplifications.OneQueryHistograms
import Lax793645Proofs.Simplifications.OneConditionalSignaturePositivity
import Lax793645Proofs.Simplifications.BaseQueries

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Template Filter Finset Matrix Function
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N K r:ℕ}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)

def oneBaseDeposit (m:Mixer p n) (o:OneUnit p n N) (s:Charts p n d)
    (x:Inputs p n (Messenger q)):Prop:=
  (∀ i,w.sameInk i (onePrinted b s t w.sel w.flav m o x i)) ∧
    ((w.pen t).draw x).reads (reducedScript w.script) m ∧
      oneOwnKeyPart t z (oneVolleyKeys ((w.pen t).draw x) t o)

def oneBaseProwl (s:Charts p n d) (m:Mixer p n) (o:OneUnit p n N)
    (W:Wgt (OneKeys t N)):=
  avg ((w.pen t).state z n) (fun x=>ind (oneBaseDeposit w t z m o s x)*
    W (oneVolleyKeys ((w.pen t).draw x) t o))

def oneBaseSeraph (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (i:Messenger q):Wgt (OneAtomKey (p:=p) (t i) N):=
  fun k=>pr (oneReflected (w.allure t z i) Y (parcel b i) o m (s (parcel b i))
    (Y (t i) (z i) k)) (w.sameInk i)

def oneBaseMirror (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (x:OneKeys t N):=
  oneKappa (w.pen t)*prodW (oneBaseSeraph w t z o m s Y) x

def oneBaseSheen (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (W:Wgt (OneKeys t N)):=
  avg (oneLawNu p N t z) (fun x=>oneBaseMirror w t z o m s Y x*W x)

theorem one_base_deposit_ink (m:Mixer p n) (o:OneUnit p n N) (s:Charts p n d)
    (x:Inputs p n (Messenger q)):
    ind (oneBaseDeposit w t z m o s x)=
      ∑ e:Messenger q→F,ind (oneDeposit (w.withInk e) t z m o s x) := by
  let e:Messenger q→F:=fun i=>(onePrinted b s t w.sel w.flav m o x i).2.2
  have he:oneBaseDeposit w t z m o s x ↔ oneDeposit (w.withInk e) t z m o s x:=by
    constructor
    · rintro ⟨ha,hb,hc⟩
      exact ⟨funext fun i=>Prod.ext (ha i).1 (Prod.ext (ha i).2 rfl),hb,hc⟩
    · rintro ⟨ha,hb,hc⟩
      refine ⟨fun i=>?_,hb,hc⟩
      have hi:=congr_fun ha i
      change onePrinted b s t w.sel w.flav m o x i=((w.amp i).1,(w.amp i).2.1,e i) at hi
      have h1:=congrArg (fun a:Magazine p (d (parcel b i))=>a.1) hi
      have h2:=congrArg (fun a:Magazine p (d (parcel b i))=>a.2.1) hi
      exact ⟨h1,h2⟩
  rw [Finset.sum_eq_single e,he]
  · intro f _ hf
    apply ind_zero
    intro hh
    apply hf
    funext i
    exact (congrArg (fun a=>a.2.2) (congr_fun hh.1 i)).symm
  · simp

theorem one_base_prowl_ink (s:Charts p n d) (m:Mixer p n) (o:OneUnit p n N)
    (W:Wgt (OneKeys t N)):
    oneBaseProwl w t z s m o W=∑ e:Messenger q→F,oneProwl (w.withInk e) t z o m s W := by
  unfold oneBaseProwl
  simp_rw [one_base_deposit_ink,Finset.sum_mul,avg_sum]
  apply sum_congr rfl
  intro e _
  apply avg_congr
  intro x _
  change ind _*W _=W _*ind _
  exact mul_comm _ _

theorem one_base_seraph_ink (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (i:Messenger q) (k:OneAtomKey (p:=p) (t i) N):
    oneBaseSeraph w t z o m s Y i k=∑ e:F,
      oneReflected (w.allure t z i) Y (parcel b i) o m (s (parcel b i))
        (Y (t i) (z i) k) ((w.amp i).1,(w.amp i).2.1,e):=w.sameInk_sum i _

theorem one_base_mirror_ink (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (x:OneKeys t N):
    oneBaseMirror w t z o m s Y x=∑ e:Messenger q→F,
      oneMirror (w.withInk e) t z o m s Y x := by
  unfold oneBaseMirror prodW
  simp_rw [one_base_seraph_ink]
  rw [Fintype.prod_sum,Finset.mul_sum]
  rfl

theorem one_base_sheen_ink (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (W:Wgt (OneKeys t N)):
    oneBaseSheen w t z o m s Y W=∑ e:Messenger q→F,oneSheen (w.withInk e) t z o m s Y W := by
  unfold oneBaseSheen
  simp_rw [one_base_mirror_ink,Finset.sum_mul,avg_sum]
  rfl

structure OneBaseSteady (m:Mixer p n) (K:ℕ) (s:Charts p n d)
    (o:OneUnit p n N):Prop where
  frame:∀ i,oneFrameLaw m (o i)
  steadyAxes (i:Messenger q):Quill.prelim (b:=b) K s i
  enough (i:Messenger q):(w.amp i).1.diagO=(w.amp i).2.1.1
  generic:oneGeneric w

theorem one_base_seraph_floor (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (i:Messenger q) (hw:IsLaw (w.policies t z n i)) (k):
    0≤oneBaseSeraph w t z o m s Y i k ∧ oneBaseSeraph w t z o m s Y i k≤1 := by
  have h:=oneReflectedLaw (w.allure t z i) Y hw (parcel b i) o m (s (parcel b i))
    (Y (t i) (z i) k)
  exact ⟨pr_nonneg h.nz,(pr_le_tot h.nz).trans h.total.le⟩

theorem one_base_mirror_floor (o:OneUnit p n N) (m:Mixer p n) (s:Charts p n d)
    (Y:OneSilhouette p N r) (hw:∀ i,IsLaw (w.policies t z n i)) (x:OneKeys t N):
    0≤oneBaseMirror w t z o m s Y x ∧ oneBaseMirror w t z o m s Y x≤1 := by
  have h0:0≤prodW (oneBaseSeraph w t z o m s Y) x:=
    prodW_nonneg (fun i y=>(one_base_seraph_floor w t z o m s Y i (hw i) y).1) x
  have h1:prodW (oneBaseSeraph w t z o m s Y) x≤1:=by
    have hh:=Finset.prod_le_prod (s:=univ) (g:=fun _:Messenger q=>(1:ℝ))
      (fun i _=>(one_base_seraph_floor w t z o m s Y i (hw i) (x i)).1)
      (fun i _=>(one_base_seraph_floor w t z o m s Y i (hw i) (x i)).2)
    simpa [prodW] using hh
  exact ⟨mul_nonneg (one_kappa_pos _).le h0,
    (mul_le_mul (one_kappa_top w t) h1 h0 zero_le_one).trans_eq (one_mul _)⟩

theorem one_base_thin_glaze (m:Mixer p n) (Y:OneSilhouette p N r) (o:OneUnit p n N)
    (i:Messenger q) (s:Charts p n d) (k:OneAtomKey (p:=p) (t i) N)
    {δ:ℝ} (hd:0<δ) (hw:w.moral t z) (hp:OneBaseSteady w m K s o)
    (he:oneGenericGauze p δ δ Y m K o) (ht:1≤p.r) (hn:2*p.r≤n):
    δ≤oneReference (w.allure t z i) Y (Y (t i) (z i) k) →
      basebeta p K/2≤oneBaseSeraph w t z o m s Y i k := by
  intro hh
  obtain ⟨h1,h2,h3⟩:=hp.steadyAxes i
  have hpos:=oneGenericDemonstrates (w.allure t z i) Y o (m:=m) (s (parcel b i)) K
    (parcel b i) (Y (t i) (z i) k) δ hd (w.amp i).1 (w.amp i).2.1.2
    (hw.2.2 i) (hw.2.1 i) ht hn hh (hp.generic i) (he _) h1 h2 h3
  have h4:((w.amp i).1.diagO,(w.amp i).2.1.2)=(w.amp i).2.1:=Prod.ext (hp.enough i) rfl
  rw [h4] at hpos
  exact hpos

def oneDilate (K:ℕ):=oneKappa (w.pen t)*(basebeta p K/2)^Fintype.card (Messenger q)
theorem one_dilate_pos (K:ℕ):0<oneDilate w t K:=
  mul_pos (one_kappa_pos _) (pow_pos (half_pos (basebeta_pos _ _)) _)

end OneQuill
end
end Lax793645Proofs.Simplifications
