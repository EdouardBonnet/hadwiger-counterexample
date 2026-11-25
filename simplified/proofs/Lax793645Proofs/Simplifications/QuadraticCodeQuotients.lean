import Lax793645Proofs.Simplifications.QuadraticFullCodes
import Lax793645Proofs.Simplifications.PrescribedKernelGram

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

theorem quadratic_code_pull_equal (L : Mat R I) (G H : Mat R R)
    (h : quadraticGramCode G=quadraticGramCode H) :
    quadraticGramCode (Lᵀ*G*L)=quadraticGramCode (Lᵀ*H*L) := by
  apply Subtype.ext
  funext v
  change evmat (pullM L L G) v v=evmat (pullM L L H) v v
  rw [evmat_pull,evmat_pull]
  exact congrFun (congrArg Subtype.val h) (L*ᵥv)

theorem quadratic_quotient_code (L : Mat R I) (hL : Surjective L.mulVec) (G H : Mat R R) :
    quadraticGramCode (Lᵀ*G*L)=quadraticGramCode (Lᵀ*H*L) ↔
      quadraticGramCode G=quadraticGramCode H := by
  constructor
  · intro h
    apply Subtype.ext
    funext v
    obtain ⟨u,rfl⟩:=hL v
    have hh:=congrFun (congrArg Subtype.val h) u
    change evmat (pullM L L G) u u=evmat (pullM L L H) u u at hh
    change evmat G (L*ᵥu) (L*ᵥu)=evmat H (L*ᵥu) (L*ᵥu)
    simpa only [evmat_pull] using hh
  · exact quadratic_code_pull_equal L G H

/-- The number of independent quadratic equations cannot increase when
nominal columns are replaced by a basis of their span. -/
theorem quadratic_code_dimension_mono (L : Mat R I) (hL : Surjective L.mulVec) :
    dim (QuadraticGramCode R) ≤ dim (QuadraticGramCode I) := by
  let P:=liftM Lᵀ Lᵀ
  have hker : (quadraticGramCode (I:=R)).ker ≤
      ((quadraticGramCode (I:=I)).comp P).ker := by
    intro G hG
    change quadraticGramCode (P G)=0
    have hz : quadraticGramCode G=quadraticGramCode (0 : Mat R R):=by simpa using hG
    have hh:=quadratic_code_pull_equal L G 0 hz
    simpa only [P,liftM_def,transpose_transpose,Matrix.mul_zero,Matrix.zero_mul,map_zero] using hh
  obtain ⟨f,hf⟩:=mem_range_comp hker
  have hi : Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨G,rfl⟩:=quadratic_gram_code_surjective x
    have hval:=LinearMap.congr_fun hf G
    change f (quadraticGramCode G)=quadraticGramCode (P G) at hval
    have hz : quadraticGramCode (Lᵀ*G*L)=quadraticGramCode (Lᵀ*(0 : Mat R R)*L) := by
      simpa only [P,liftM_def,transpose_transpose,Matrix.mul_zero,Matrix.zero_mul,map_zero] using hval.symm.trans hx
    have hh:=(quadratic_quotient_code L hL G 0).mp hz
    change quadraticGramCode G=0
    simpa only [map_zero] using hh
  exact LinearMap.finrank_le_finrank_of_injective hi

end
end Lax793645Proofs.Simplifications
