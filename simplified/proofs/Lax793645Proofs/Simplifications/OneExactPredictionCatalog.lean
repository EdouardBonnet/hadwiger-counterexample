import Lax793645Proofs.Simplifications.OneExactEndpointPredictions
import Lax793645Proofs.Simplifications.ExactSevenPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N c R : ℕ}

def OneTesterFree (Y : OneSilhouette p N c) (f : Pulsar p c) : Prop :=
  ∀ l q q' k,oneFromPulse Y f l q k=oneFromPulse Y f l q' k

theorem one_tester_free_zero (Y : OneSilhouette p N c) : OneTesterFree Y 0 := by
  intro l q q' k
  rfl

/-- A tester-independent function cannot differ from another one by
the displayed tester bit. Both diagonal laws assign positive mass to
the full cell through any chosen key. -/
theorem one_exact_tester_separated (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R) (hg : 0<p.g)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2) :
    TesterSeparated (oneWisp p Y) (OneTesterFree Y) := by
  intro f g γ hf hg' he
  let l : Tag p.g:=⟨0,hg⟩
  let k : OneAtomKey (p:=p) l N:=0
  have h0:=he l 0 (Y l 0 k) (one_full_reference_positive Y hY hN hsmall l 0 k)
  have h1:=he l 1 (Y l 1 k) (one_full_reference_positive Y hY hN hsmall l 1 k)
  have hf' : f l 1 (Y l 1 k)=f l 0 (Y l 0 k):=hf l 1 0 k
  have hg'' : g l 1 (Y l 1 k)=g l 0 (Y l 0 k):=hg' l 1 0 k
  simp only [mul_zero,add_zero] at h0
  simp only [mul_one,hf',hg'',h0] at h1
  exact add_left_cancel (h1.symm.trans (add_zero _).symm)

theorem one_palette_good_mono {H J : Space (OneJointKey p N)} (hHJ : H≤J)
    {o : OneUnit p n N} (h : OnePaletteGood J o) : OnePaletteGood H o := by
  intro i s a b hab
  have he : (⟨a.val,hHJ a.property⟩ : J)=(⟨b.val,hHJ b.property⟩ : J) :=
    h i s hab
  exact Subtype.ext (congrArg (fun z : J=>z.val) he)

/-- One bounded prepared event controls both the support gap and exact
normalization. It supplies the canonical catalogue for every allowed
basis at a unit, with no choice depending on its opposite leaf. -/
theorem one_exact_catalog_control (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (K B : ℕ) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r)
    (hB : (B:ℝ)<bp ((p.b:ℝ)-2*p.j)) :
    ∃ H : Space (OneJointKey p N),dim H≤2*(p.g*R) ∧
      (∀ o o',OnePaletteGood H o→OnePaletteGood H o'→OneFullTableGap Y m K o o') ∧
      ∀ o : OneUnit p n N,OnePaletteGood H o→∀ d : Rates,∀ v : Charts p n d,
      (∀ i w,totalRank (v i w)≤K)→
      ∀ i E,E.card≤B→∀ w α f,
        ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E (yokeSet w α) f→
          OneTesterFree Y f ∧
          onePostulates (o i) (oneFromPulse Y f) (oneYoke m o i (v i w) α) ∅ 0 := by
  obtain ⟨H,hH,hgap⟩:=one_palette_support_space hg hr hn Y hY m K hN hsmall
  obtain ⟨J,hJ,hnorm⟩:=one_exact_endpoint_prediction Y hY hN hsmall m K hg h3 hj hr hn hroom
  refine ⟨H⊔J,?_,?_,?_⟩
  · have hd : dim (H⊔J : Space (OneJointKey p N))+dim (H⊓J : Space (OneJointKey p N))=
        dim H+dim J:=Submodule.finrank_sup_add_finrank_inf_eq H J
    omega
  · intro o o' ho ho'
    exact hgap o o' (one_palette_good_mono le_sup_left ho) (one_palette_good_mono le_sup_left ho')
  · intro o ho d v hv i E hE w α f hf
    have hsize : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j):=
      (by exact_mod_cast hE : (E.card:ℝ)≤B).trans_lt hB
    have hh:=hnorm o (one_palette_good_mono le_sup_right ho) d v i w α (hv i w) E hsize f hf
    exact ⟨hh.2.1,hh.2.2⟩

end
end Lax793645Proofs.Simplifications
