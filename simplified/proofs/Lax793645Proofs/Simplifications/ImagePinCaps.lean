import Lax793645Proofs.Simplifications.ClosedImagePeeling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

/-- Completing the image equations also transfers an upper bound from
closed pins to arbitrary pins. Only the error exponent pays the closure factor. -/
theorem image_pin_cap_of_closed (X : A→C→Mat (Fin N) I)
    (c : ℕ) (hc : 0<c) (cl : ImageClosure C I c) (hzero : cl.close ⊥=⊥)
    (w : Wgt A) (hw : ∀ x,0≤w x) (ζ : ℝ) (hz : 0≤ζ)
    (hclosed : ∀ b : ImagePin C I N,cl.close b.sp=b.sp→
      pr w (imagePinAgree X b)≤fee N (ζ/c) (imagePlanRank b.sp))
    (a : ImagePin C I N) :
    pr w (imagePinAgree X a)≤fee N ζ (imagePlanRank a.sp) := by
  classical
  by_contra! he
  have hbot : imagePlanRank (⊥ : ImagePlan C I)=0 := by simp [imagePlanRank,dim]
  have hg : (imagePlanRank (cl.close a.sp):ℝ)≤c*imagePlanRank a.sp := by
    have hh:=cl.growth ⊥ a.sp bot_le hzero
    rw [hbot,Nat.sub_zero,Nat.sub_zero] at hh
    exact_mod_cast hh
  have hc' : (0:ℝ)<c:=by exact_mod_cast hc
  obtain ⟨x,hx,hs⟩:=closed_pin_family_completion w hw (imagePinAgree X a) X a.sp
    (cl.close a.sp) (cl.extensive a.sp)
    (fun x hx y hy e v hv=>(hx e v hv).trans (hy e v hv).symm)
    0 (Nat.zero_le _) c ζ hc' hz (by simpa using hg) (by simpa using he)
  have hh:=hclosed ⟨cl.close a.sp,X x⟩ (cl.idempotent a.sp)
  have hm:=pr_mono hw (fun y (hy : imagePinAgree X a y ∧
    imagePinAgree X ⟨cl.close a.sp,X x⟩ y)=>hy.2)
  have hs' : fee N (ζ/c) (imagePlanRank (cl.close a.sp))<
      pr w (imagePinAgree X ⟨cl.close a.sp,X x⟩) := by
    apply lt_of_lt_of_le _ hm
    simpa using hs
  exact (not_lt_of_ge hh) hs'

end
end Lax793645Proofs.Simplifications
