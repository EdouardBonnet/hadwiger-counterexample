import Lax793645Proofs.Simplifications.ImageGramCharacters
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PrimalChannelTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

theorem image_cross_pair_rep (f : Module.Dual F (ImageCross C I)) :
    ∃ M : ImageCross C I,imageCrossPair M=f := by
  classical
  let B : ImageCross C I→ₗ[F]Module.Dual F (ImageCross C I):={
    toFun:=imageCrossPair
    map_add' :=fun x y=>LinearMap.ext fun z=>by
      simp only [image_cross_pair_apply,Pi.add_apply,LinearMap.add_apply,mpair_add,Finset.sum_add_distrib]
    map_smul' :=fun c x=>LinearMap.ext fun z=>by
      simp only [image_cross_pair_apply,Pi.smul_apply,LinearMap.smul_apply,mpair_smul,
        RingHom.id_apply,smul_eq_mul,Finset.mul_sum] }
  have hb : Function.Injective B:=by
    rw [←LinearMap.ker_eq_bot]
    refine le_bot_iff.mp (fun x hx=>?_)
    have he : x=0:=by
      funext e
      apply mpair_nondeg
      apply LinearMap.ext
      intro z
      change imageCrossPair x=0 at hx
      have h:=LinearMap.congr_fun hx (Pi.single e z)
      rw [image_cross_pair_apply,Finset.sum_eq_single e] at h
      · rwa [Pi.single_eq_same] at h
      · intro j _ hj; simp [hj]
      · simp
    exact he ▸ Submodule.zero_mem _
  exact rk_surj.mpr ((rk_inj.mp hb).trans Subspace.dual_finrank_eq.symm) f

/-- An invertible change of ambient coordinates preserves spreading.
Targets outside its image are handled as empty events. -/
theorem image_clear_left (X : A→C→Mat (Fin N) I) (H : C→Mat (Fin N) (Fin N))
    (hH : ∀ e,Function.Injective (H e).mulVec) {w : Wgt A} (hw : SubLaw w)
    {a : ImagePin C I N} {ζ : ℝ} (ha : imagePinClear X a ζ w) :
    imagePinClear (fun x e=>H e*X x e) a ζ w := by
  classical
  intro b
  by_cases hp : 0<pr w (imagePinAgree (fun x e=>H e*X x e) b)
  · obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw.nz hp
    let b' : ImagePin C I N:=⟨b.sp,X x⟩
    apply (pr_mono hw.nz (q:=imagePinAgree X b') ?_).trans (ha b')
    intro y hy e v hv
    apply hH e
    have he:=(hy e v hv).trans (hx e v hv).symm
    simpa only [←Matrix.mulVec_mulVec] using he
  · exact (not_lt.mp hp).trans (bp_pos _).le

variable {V : Type} [AddCommGroup V] [Module F V] [Fintype V]

/-- Quantitative Gram matching for any finite linear test of the cross
table. This is the collision-counting interface for a single primal mode. -/
theorem image_gram_hit (X Y : A→C→Mat (Fin N) I) (Q : ImageCross C I)
    (T : ImageCross C I→ₗ[F]V) {u w : Wgt A} (hu : IsLaw u) (hw : IsLaw w)
    {a b : ImagePin C I N} (hc : imagePinClear X a 0.05 u) (hd : imagePinClear Y b 0.05 w)
    (h : ∀ x,u x≠0→∀ y,w y≠0→imageRowAgree a.sp (imageActual X Y x y) Q ∧
      imageRowAgree b.sp (fun e=>(imageActual X Y x y e)ᵀ) (fun e=>(Q e)ᵀ))
    (hN : 100≤N) (hT : (dim V:ℝ)≤0.01*N) :
    hit N≤pr (pairW u w) (fun x=>T (imageActual X Y x.1 x.2)=T Q) := by
  classical
  let v:=pairW u w
  let s (x : A×A):=T (imageActual X Y x.1 x.2-Q)
  have hh (g : Module.Dual F V) :
      let Z:=avg v (fun x=>wsign (g (s x)))
      Z=1 ∨ |Z|≤bp (-0.45*N) := by
    obtain ⟨M,hM⟩:=image_cross_pair_rep (g.comp T)
    have he (x : A×A) : g (s x)=imageCrossPair M (imageActual X Y x.1 x.2-Q):=
      (LinearMap.congr_fun hM _).symm
    dsimp only
    simp_rw [he]
    exact image_gram_character X Y Q M hu hw hc hd h
  have hg:=indicator_test s v (pairW_law hu hw) (bp (-0.45*N)) (bp_pos _).le hh
  have he : pr v (fun x=>s x=0)=pr v (fun x=>T (imageActual X Y x.1 x.2)=T Q):=by
    apply congrArg (pr v)
    funext x
    apply propext
    simp only [s,map_sub,sub_eq_zero]
  rw [he] at hg
  apply le_trans _ hg
  have hn : (100:ℝ)≤N:=by exact_mod_cast hN
  unfold hit
  have heq:=bp_le (show -0.45*N≤-0.02*(N:ℝ) by linarith only [hn])
  have heq' : 2*bp (-0.02*N)≤bp (-(dim V:ℝ)):=by
    rw [←bp_one,←bp_add]
    apply bp_le
    linarith only [hn,hT]
  linarith only [heq,heq']

/-- The ambient dot product can be replaced by any nondegenerate matrix
pairing, with no change in the spreading or Gram-hit loss. -/
theorem image_polar_gram_hit (X Y : A→C→Mat (Fin N) I)
    (H : C→Mat (Fin N) (Fin N)) (hH : ∀ e,Function.Injective (H e).mulVec)
    (Q : ImageCross C I) (T : ImageCross C I→ₗ[F]V)
    {u w : Wgt A} (hu : IsLaw u) (hw : IsLaw w) {a b : ImagePin C I N}
    (hc : imagePinClear X a 0.05 u) (hd : imagePinClear Y b 0.05 w)
    (h : ∀ x,u x≠0→∀ y,w y≠0→
      imageRowAgree a.sp (imageActual X (fun y e=>H e*Y y e) x y) Q ∧
      imageRowAgree b.sp (fun e=>(imageActual X (fun y e=>H e*Y y e) x y e)ᵀ)
        (fun e=>(Q e)ᵀ)) (hN : 100≤N) (hT : (dim V:ℝ)≤0.01*N) :
    hit N≤pr (pairW u w)
      (fun x=>T (imageActual X (fun y e=>H e*Y y e) x.1 x.2)=T Q) :=
  image_gram_hit X _ Q T hu hw hc (image_clear_left Y H hH hw.sub hd) h hN hT

end
end Lax793645Proofs.Simplifications
