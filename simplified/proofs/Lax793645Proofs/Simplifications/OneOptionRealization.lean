import Lax793645Proofs.Simplifications.OneOptionContracts
import Lax793645Proofs.Simplifications.OneScalarRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OneOptions
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}

/-- An accepted pair of numerical options gives an actual quadratic
realization, preserving every stored pin and every selected key. -/
theorem realize (w : Typus p q d e) (m : Mixer p n)
    (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (T : OneCross p n) (s : Charts p n d) (t : Charts p n e)
    (hg : Odd p.g) (ha : (onePinClosure p n).close a.sp=a.sp)
    (hb : (onePinClosure p n).close b.sp=b.sp)
    (hc : chances w s t a b T K)
    (hroom : oneRealizationRoom p K (Fintype.card (Messenger q)))
    (u v : Inputs p n (Messenger q)) (x y : OneUnit p n N)
    (hx : notified m a b T True x)
    (hy : notified m b a (fun e=>(T e)ᵀ) True y)
    (hu : OneProtectedInput (w.qA.pen w.t) a.sp K u)
    (hv : OneProtectedInput (w.qB.pen w.t) b.sp K v)
    (hA : OneQuill.oneDeposit w.qA w.t w.z m x s u)
    (hB : OneQuill.oneDeposit w.qB w.t w.z m y t v)
    (hkeys : oneVolleyKeys ((w.qA.pen w.t).draw u) w.t x=
      oneVolleyKeys ((w.qB.pen w.t).draw v) w.t y) :
    let U:=(w.qA.pen w.t).draw u
    let V:=(w.qB.pen w.t).draw v
    U.legal w.t ∧ V.legal w.t ∧ U.roleMatch V w.t ∧
      ∃ Q : OneCross p n,OneRealized U V w.t m Q ∧
        imageRowAgree (a.sp⊔oneKeyPlan U w.t) Q (oneCrossMatrix x y) ∧
        imageRowAgree (b.sp⊔oneKeyPlan V w.t) (fun e=>(Q e)ᵀ) (oneCrossMatrix y x) := by
  intro U V
  obtain ⟨⟨hfmt,hma,hmb,hfull,hrhy,hsa,hsb⟩,
    ⟨hchartA,hpenA,hstillA,hsafeA⟩,hchartB,hpenB,hstillB,hsafeB⟩:=hc
  obtain ⟨protA⟩:=hu
  obtain ⟨protB⟩:=hv
  refine ⟨(w.qA.pen w.t).draw_legal u,(w.qB.pen w.t).draw_legal v,
    one_rhyme_match w.t w.qA.amp w.qB.amp s t _ _ _ _ u v m x y hA.1 hB.1 hrhy,?_⟩
  have hflag : oneTableFlag a b (fun e=>((T e)ᵀ)ᵀ) x:=by
    simpa only [Matrix.transpose_transpose] using hx.2.2.2
  apply one_scalar_realization U V w.t m hg
    ((w.qA.pen w.t).draw_legal u) ((w.qB.pen w.t).draw_legal v)
    (shots_ok true _ rfl hfmt) (shots_ok false _ rfl hfmt) x y hx.2.2.1 hy.2.2.1
    a.sp b.sp K ha hb hpenA.1 hpenB.1 protA protB
    (one_safe_of_flags a b ha T x y hx.2.1 hy.2.2.2 hsafeA)
    (one_safe_of_flags b a hb (fun e=>(T e)ᵀ) y x hy.2.1 hflag hsafeB)
    hkeys ?_ ?_ ?_ ?_ hroom
  · exact one_still_recipe w.t true a.sp T s hchartA m x y _ _ u w.qA.amp hA.1
      V rfl w.z hma.2.1 hfull hstillA
      (one_flag_contract a b ha T x y hx.2.1 hy.2.2.2)
  · exact one_still_recipe w.t false b.sp (fun e=>(T e)ᵀ) t hchartB m y x _ _ v w.qB.amp hB.1
      U rfl w.z hmb.2.1 hfull hstillB
      (one_flag_contract b a hb (fun e=>(T e)ᵀ) y x hy.2.1 hflag)
  · exact one_procl_grad w.t w.qA.amp w.qB.amp hg s t _ _ _ _ u v m x y hA.1 hB.1
      (reducedScript w.qA.script) hsa hA.2.1
  · exact one_procl_grad w.t w.qB.amp w.qA.amp hg t s _ _ _ _ v u m y x hB.1 hA.1
      (reducedScript w.qB.script) hsb hB.2.1

end OneOptions
end
end Lax793645Proofs.Simplifications
