import Lax793645Proofs.Simplifications.OneUnaryRecords
import Lax793645Proofs.Simplifications.OneProtectedKeys

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def onePromise (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (a b : ImagePlan (Comp p.g) (OneColumn p n)) (x y : OneUnit p n N) :=
  v.legal t ∧ w.legal t ∧ v.roleMatch w t ∧
    ∃ Q : OneCross p n,OneRealized v w t m Q ∧
      imageRowAgree (a⊔oneKeyPlan v t) Q (oneCrossMatrix x y) ∧
      imageRowAgree (b⊔oneKeyPlan w t) (fun e=>(Q e)ᵀ) (oneCrossMatrix y x)

/-- Record the opposite pins separately on every equal-key event. -/
theorem one_record_at_key (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    {a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    {μ δ : Wgt (OneUnit p n N)} (U V : OneUnit p n N→Prop)
    (ha : ∀ x,U x→imagePinAgree oneCoordinateImages a x ∧ (∀ i,oneFrameLaw m (x i)))
    (hb : ∀ y,V y→imagePinAgree oneCoordinateImages b y ∧ (∀ i,oneFrameLaw m (y i)))
    (h : ∀ x,U x → ∀ y,V y → oneVolleyKeys v t x=oneVolleyKeys w t y → onePromise v w t m a.sp b.sp x y)
    {ζ : ℝ} {k : ℕ} (hv : imagePlanRank (a.sp⊔oneKeyPlan v t)=imagePlanRank a.sp+k)
    (hw : imagePlanRank (b.sp⊔oneKeyPlan w t)=imagePlanRank b.sp+k)
    (hz : ζ≤0.004) (hK : ζ*k≤0.004) (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : imagePinClear oneCoordinateImages a ζ μ) (hB : imagePinClear oneCoordinateImages b ζ δ)
    (hN : 100≤2*N) (hT : (dim (OneCheckGram p n):ℝ)≤0.01*(2*N))
    (L : ℝ) (hLf : bp (dim (ImageLedger (a.sp⊔oneKeyPlan v t)))≤L)
    (hLg : bp (dim (ImageLedger (b.sp⊔oneKeyPlan w t)))≤L)
    (key : OneKeys t N) :
    hit (2*N)*(pr μ (fun x=>U x ∧ oneVolleyKeys v t x=key)*
      pr δ (fun y=>V y ∧ oneVolleyKeys w t y=key))≤
      pr (pairW μ δ) (fun xy=>(U xy.1 ∧ oneVolleyKeys v t xy.1=key) ∧
        (V xy.2 ∧ oneVolleyKeys w t xy.2=key) ∧
        (oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false))+
      (hit (2*N)*tau (2*N) k*L)*(pr μ (fun x=>U x ∧ oneVolleyKeys v t x=key)+
        pr δ (fun y=>V y ∧ oneVolleyKeys w t y=key)) := by
  let U' x:=U x ∧ oneVolleyKeys v t x=key
  let V' y:=V y ∧ oneVolleyKeys w t y=key
  have hn : 0≤hit (2*N)*tau (2*N) k*L:=
    mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) ((bp_pos _).le.trans hLf)
  by_cases hU:∃ x,U' x
  · obtain ⟨x,hx⟩:=hU
    by_cases hV:∃ y,V' y
    · obtain ⟨y,hy⟩:=hV
      let f : ImagePin (Comp p.g) (OneColumn p n) (2*N):=
        ⟨a.sp⊔oneKeyPlan v t,oneCoordinateImages x⟩
      let g : ImagePin (Comp p.g) (OneColumn p n) (2*N):=
        ⟨b.sp⊔oneKeyPlan w t,oneCoordinateImages y⟩
      apply one_record_hit v w t m (a:=a) (b:=b) (f:=f) (g:=g) U' V' key
        ?_ ?_ ?_ hz hK hμ hδ hA hB le_sup_left le_sup_left hv hw hN hT L hLf hLg
      · intro z hz
        exact ⟨one_keys_freeze v t a x z (ha x hx.1).1 (ha z hz.1).1
          (hx.2.trans hz.2.symm),(ha z hz.1).2,hz.2⟩
      · intro z hz
        exact ⟨one_keys_freeze w t b y z (hb y hy.1).1 (hb z hz.1).1
          (hy.2.trans hz.2.symm),(hb z hz.1).2,hz.2⟩
      · exact fun x hx y hy=>h x hx.1 y hy.1 (hx.2.trans hy.2.symm)
    · have hv0 : pr δ V'=0:=by
        have he : V'=(fun _=>False):=funext fun y=>propext ⟨fun hy=>hV ⟨y,hy⟩,False.elim⟩
        rw [he,pr_false]
      change hit (2*N)*(pr μ U'*pr δ V')≤_
      rw [hv0,mul_zero,mul_zero]
      exact add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
        (mul_nonneg hn (add_nonneg (pr_nonneg hμ.nz) (le_refl 0)))
  · have hu0 : pr μ U'=0:=by
      have he : U'=(fun _=>False):=funext fun x=>propext ⟨fun hx=>hU ⟨x,hx⟩,False.elim⟩
      rw [he,pr_false]
    change hit (2*N)*(pr μ U'*pr δ V')≤_
    rw [hu0,zero_mul,mul_zero]
    exact add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
      (mul_nonneg hn (add_nonneg (le_refl 0) (pr_nonneg hδ.nz)))

theorem one_record_sum (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    {a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    {μ δ : Wgt (OneUnit p n N)} (U V : OneUnit p n N→Prop)
    (ha : ∀ x,U x→imagePinAgree oneCoordinateImages a x ∧ (∀ i,oneFrameLaw m (x i)))
    (hb : ∀ y,V y→imagePinAgree oneCoordinateImages b y ∧ (∀ i,oneFrameLaw m (y i)))
    (h : ∀ x,U x → ∀ y,V y → oneVolleyKeys v t x=oneVolleyKeys w t y → onePromise v w t m a.sp b.sp x y)
    {ζ : ℝ} {k : ℕ} (hv : imagePlanRank (a.sp⊔oneKeyPlan v t)=imagePlanRank a.sp+k)
    (hw : imagePlanRank (b.sp⊔oneKeyPlan w t)=imagePlanRank b.sp+k)
    (hz : ζ≤0.004) (hK : ζ*k≤0.004) (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : imagePinClear oneCoordinateImages a ζ μ) (hB : imagePinClear oneCoordinateImages b ζ δ)
    (hN : 100≤2*N) (hT : (dim (OneCheckGram p n):ℝ)≤0.01*(2*N))
    (L : ℝ) (hLf : bp (dim (ImageLedger (a.sp⊔oneKeyPlan v t)))≤L)
    (hLg : bp (dim (ImageLedger (b.sp⊔oneKeyPlan w t)))≤L) :
    hit (2*N)*(∑ key : OneKeys t N,pr μ (fun x=>U x ∧ oneVolleyKeys v t x=key)*
      pr δ (fun y=>V y ∧ oneVolleyKeys w t y=key))≤
      pr (pairW μ δ) (fun xy=>(oneRawHoles m).conflict
        (xy.1 true,xy.1 false) (xy.2 true,xy.2 false))+2*(hit (2*N)*tau (2*N) k*L) := by
  let C (xy:OneUnit p n N×OneUnit p n N):=
    (oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false)
  let P:=pairW μ δ
  let H:=hit (2*N)*tau (2*N) k*L
  let G (key : OneKeys t N) (xy:OneUnit p n N×OneUnit p n N):=
    (U xy.1 ∧ oneVolleyKeys v t xy.1=key) ∧ (V xy.2 ∧ oneVolleyKeys w t xy.2=key) ∧ C xy
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun key _=>one_record_at_key v w t m U V ha hb h hv hw hz hK
    hμ hδ hA hB hN hT L hLf hLg key).trans ?_
  rw [Finset.sum_add_distrib]
  have hi : (∑ key,pr P (G key))≤pr P C:=by
    rw [←sum_pr_tag P C (oneVolleyKeys v t ∘ Prod.fst)]
    exact Finset.sum_le_sum fun key _=>pr_mono (subLaw_pair hμ hδ).nz
      (fun xy h=>⟨h.2.2,h.1.2⟩)
  refine add_le_add hi ?_
  have hU : (∑ key,pr μ (fun x=>U x ∧ oneVolleyKeys v t x=key))≤1:=
    (sum_pr_tag μ U (oneVolleyKeys v t)).trans_le ((pr_le_tot hμ.nz).trans hμ.total)
  have hV : (∑ key,pr δ (fun y=>V y ∧ oneVolleyKeys w t y=key))≤1:=
    (sum_pr_tag δ V (oneVolleyKeys w t)).trans_le ((pr_le_tot hδ.nz).trans hδ.total)
  have hH : 0≤H:=mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) ((bp_pos _).le.trans hLf)
  rw [←Finset.mul_sum,Finset.sum_add_distrib,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith only [hU,hV]) hH

end
end Lax793645Proofs.Simplifications
