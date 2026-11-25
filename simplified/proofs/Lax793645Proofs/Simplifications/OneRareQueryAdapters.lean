import Lax793645Proofs.Simplifications.OneRareQueryWrappers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneStation
variable {p:Shape} {n N:ℕ} {q:Format} {d:Rates} {side:Bool}

abbrev sales (w:Quill p q d side) (t:Tagging p (Messenger q)) (z:Messenger q→F)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N)) (K:ℕ) (μ:Wgt (OneUnit p n N))
    (P:OneUnit p n N→Prop) (m:Mixer p n) (s:Charts p n d):=
  OneQuill.oneGoodHistogram w t z pin.sp K μ P m s
abbrev custom (w:Quill p q d side) (μ:Wgt (OneUnit p n N)) (s:Charts p n d)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (m:Mixer p n)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N)) (K:ℕ):=
  OneQuill.oneCustom w t z pin.sp K μ m s

theorem sales_custom (w:Quill p q d side) (μ:Wgt (OneUnit p n N)) (s:Charts p n d)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (m:Mixer p n)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N)) (K:ℕ) (P:OneUnit p n N→Prop):
    custom w μ s t z m pin K (sales w t z pin K μ P m s):=
  OneQuill.one_good_natural_custom w t z pin.sp K μ P m s

theorem sales_pos (w:Quill p q d side) (μ:Wgt (OneUnit p n N)) (s:Charts p n d)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (m:Mixer p n)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N)) (K:ℕ) (P:OneUnit p n N→Prop)
    (hμ:∀ o,0≤μ o) (x):0≤sales w t z pin K μ P m s x:=
  OneQuill.one_good_natural_nonneg w t z pin.sp K μ P m s hμ x

theorem sales_mono_filter (w:Quill p q d side) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (s:Charts p n d) (m:Mixer p n)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N)) (K:ℕ) (μ:Wgt (OneUnit p n N))
    (P Q:OneUnit p n N→Prop) (hμ:∀ o,0≤μ o) (hPQ:∀ o,P o → Q o):
    ∀ x,sales w t z pin K μ P m s x≤sales w t z pin K μ Q m s x:=
  OneQuill.one_good_natural_mono_filter w t z pin.sp K μ P m s Q hμ hPQ

theorem predicted_qualify_hit (w:Quill p q d side) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (s:Charts p n d) (m:Mixer p n) (K:ℕ)
    (pin:ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E H:OneKeys t N→Prop) (hHE:∀ x,H x → E x) {a h:ℝ} (hh:0<h)
    (hq:OneQuill.OnePredictedQualified w t z s m K μ P a α g ε E)
    (hμ:IsLaw μ) (hw:w.moral t z) (hr:1≤p.r) (hn:2*p.r≤n)
    (hpen:OnePenSpace (w.pen t) pin.sp K)
    (herr:Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε)≤h)
    (hreject:bp (num (Messenger q)+oneBaseProtectionDim p K-n)≤a*h)
    (hbad:pr μ (fun o=>¬OneQuill.OneBaseSober w t z K H m (4*h) o)≤a):
    a*h≤pr (sales w t z pin K μ P m s) H:=
  OneQuill.one_protected_predicted_hit w t z pin.sp K μ P m s α g ε E H hHE hh hq hμ hw hr hn hpen herr hreject hbad

end OneStation
end
end Lax793645Proofs.Simplifications
