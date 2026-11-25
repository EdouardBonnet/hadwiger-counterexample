import Lax793645Proofs.Simplifications.QuadraticPrescribedKernels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R U : Type} [Fintype I] [Fintype R] [Fintype U]
  [DecidableEq I] [DecidableEq R] [DecidableEq U]

/-- Auxiliary dual columns certify the exact kernel. The target LᵀL has
column space equal to the annihilator of ker L. No inclusion--exclusion
over additional image kernels is used. -/
theorem auxiliary_kernel_certificate (L : Mat R I) (hL : Surjective L.mulVec)
    (P : Mat U I) :
    ind (P.mulVecLin.ker=L.mulVecLin.ker)=
      bp (num I*num R)*ind (L.mulVecLin.ker≤P.mulVecLin.ker)*
        pr unif (fun Y : Mat U I=>Pᵀ*Y=Lᵀ*L) := by
  classical
  by_cases hk : L.mulVecLin.ker≤P.mulVecLin.ker
  · obtain ⟨Z,hZ⟩:=factor_through_quotient L P hk
    subst P
    have he (Y : Mat U I) : (Z*L)ᵀ*Y=Lᵀ*L ↔ Zᵀ*Y=L := by
      rw [Matrix.transpose_mul,Matrix.mul_assoc]
      constructor
      · intro h
        have hLt : Injective Lᵀ.mulVec:=transpose_surj_iff.mp (by
          simpa only [Matrix.transpose_transpose] using hL)
        obtain ⟨C,hC⟩:=mat_left_inv hLt
        have hh:=congrArg (fun X=>C*X) h
        simpa only [←Matrix.mul_assoc,hC,Matrix.one_mul] using hh
      · exact congrArg (fun X=>Lᵀ*X)
    simp_rw [he]
    rw [ind_one hk, mul_one, exact_kernel_mul_iff L hL]
    by_cases hi : Injective Z.mulVec
    · rw [ind_one hi,pr_gram_fixed hi,←bp_add]
      rw [show num I*num R + -num R*num I=0 by ring,bp_zero]
    · have hn (Y : Mat U I) : ¬Zᵀ*Y=L := by
        intro h
        have hs : Surjective Zᵀ.mulVec := by
          intro v
          obtain ⟨x,hx⟩:=hL v
          exact ⟨Y*ᵥx,by rw [Matrix.mulVec_mulVec,h,hx]⟩
        exact hi (transpose_surj_iff.mp hs)
      simp only [ind_zero hi,show (fun Y : Mat U I=>Zᵀ*Y=L)=(fun _=>False) from
        funext fun Y=>propext ⟨fun h=>(hn Y h).elim,False.elim⟩,pr_false,mul_zero]
  · have he : P.mulVecLin.ker≠L.mulVecLin.ker:=fun h=>hk h.ge
    rw [ind_zero he,ind_zero hk,mul_zero,zero_mul]

/-- The redundant Gram equations and auxiliary equations have no
quadratic-in-the-column-count normalization loss. -/
theorem auxiliary_kernel_normalization (u d N : ℝ) (hd : 0≤d) (hdu : d≤u) :
    d*N+(u-d)*(u-d+1)/2-u*(u+1)/2-u*d ≤ d*N := by
  have h : 0≤d*(2*u-d):=mul_nonneg hd (by linarith)
  nlinarith

end
end Lax793645Proofs.Simplifications
