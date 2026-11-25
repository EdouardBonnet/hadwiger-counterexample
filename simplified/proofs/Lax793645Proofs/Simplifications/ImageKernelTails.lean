import Lax793645Proofs.Simplifications.ImagePinCaps
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FrameIntersectionBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O C D : Type} [Fintype O] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  {N : ℕ}

def imageKernelRank (images : O→C→Mat (Fin N) D) (x : O) : ℕ:=
  ∑ e,dim (images x e).mulVecLin.ker

def kernelImagePin {t : ℕ} (f : C→Mat D (Fin t)) : ImagePin C D N:=⟨fun e=>colSp (f e),0⟩

theorem large_image_kernel_pin (images : O→C→Mat (Fin N) D) {x : O} {t : ℕ}
    (h : t ≤ imageKernelRank images x) :
    ∃ f : C→Mat D (Fin t),t ≤ imagePlanRank (kernelImagePin (N:=N) f).sp ∧
      imagePinAgree images (kernelImagePin f) x := by
  choose M hM hg using (fun e:C=>bounded_pack (images x e).mulVecLin.ker t)
  refine ⟨M,?_,?_⟩
  · change t ≤ ∑ e,dim (colSp (M e))
    simp_rw [hg]
    by_cases hh : ∃ e,t ≤ dim (images x e).mulVecLin.ker
    · obtain ⟨e,he⟩:=hh
      have hs := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun e=>min (dim (images x e).mulVecLin.ker) t)
        (fun _ _=>Nat.zero_le _) (mem_univ e)
      simpa only [min_eq_right he] using hs
    · push Not at hh
      simp_rw [min_eq_left (hh _).le]
      exact h
  · intro e v hv
    change images x e*ᵥv=(0 : Mat (Fin N) D)*ᵥv
    rw [Matrix.zero_mulVec]
    exact hM e hv

theorem image_kernel_candidates (t : ℕ) :
    num (C→Mat D (Fin t))=bp (num C*num D*t) := by
  unfold num
  rw [Fintype.card_fun]
  push_cast
  rw [card_space,dim_mat,←bp_mul_nat]
  simp only [Fintype.card_fin,Nat.cast_mul]
  congr 1
  ring

/-- A large total kernel supplies a bounded-rank zero-image pin. The
candidate count only depends on the nominal dimension and its rank. -/
theorem image_kernel_tail (images : O→C→Mat (Fin N) D) (μ : Wgt O)
    (hμ : ∀ x,0 ≤ μ x) (ζ : ℝ) (hζ : ζ ≤ 1)
    (H : ∀ a : ImagePin C D N,
      pr μ (imagePinAgree images a) ≤ fee N ζ (imagePlanRank a.sp)) (t : ℕ) :
    pr μ (fun x=>t ≤ imageKernelRank images x)  ≤ 
      bp (num C*num D*t-(1-ζ)*t*N) := by
  let P (f : C→Mat D (Fin t)) (x:O):=
    t ≤ imagePlanRank (kernelImagePin (N:=N) f).sp ∧ imagePinAgree images (kernelImagePin f) x
  have hh f : pr μ (P f) ≤ bp (-(1-ζ)*(t:ℝ)*N) := by
    by_cases h : t ≤ imagePlanRank (kernelImagePin (N:=N) f).sp
    · simp only [P,h,true_and]
      refine (H _).trans (bp_le ?_)
      have ht : (t:ℝ) ≤ imagePlanRank (kernelImagePin (N:=N) f).sp:=by exact_mod_cast h
      change -(1-ζ)*(imagePlanRank (kernelImagePin (N:=N) f).sp:ℝ)*N ≤ _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonpos_left ht (by linarith only [hζ])) (Nat.cast_nonneg _)
    · simp only [P,h,false_and,pr_false]
      exact (bp_pos _).le
  refine ((pr_mono hμ (fun x hx=>large_image_kernel_pin images hx)).trans
    (pr_exists_le hμ P)).trans ?_
  refine (Finset.sum_le_sum (fun f _=>hh f)).trans_eq ?_
  rw [sum_const,card_univ,nsmul_eq_mul]
  change num (C→Mat D (Fin t))*bp _=_
  rw [image_kernel_candidates,←bp_add]
  congr 1
  ring

end
end Lax793645Proofs.Simplifications
