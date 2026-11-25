import Lax793645Proofs.Simplifications.LinearProjectionFourier
import Lax793645Proofs.Simplifications.LinearDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem fourier_norm_sub (f g : Wgt (Vec I)) :
    fourierNorm (fun x=>f x-g x)≤fourierNorm f+fourierNorm g := by
  have he : (fun x=>f x-g x)=(fun x=>f x+(-1)*g x):=by ext x; ring
  rw [he]
  refine (fourier_norm_add f (fun x=>(-1)*g x)).trans_eq ?_
  rw [fourier_norm_smul]
  norm_num

theorem fourier_norm_bounded_count (f : Wgt (Vec I)) (B : ℝ)
    (hf : ∀ x,|f x|≤B) : fourierNorm f≤num (Vec I)*B := by
  have hb ξ : |linearFourier f ξ|≤B := by
    refine (abs_avg_le unif_law.nz).trans (unif_law.avg_le (fun x=>?_))
    change |vectorPhase ξ x*f x|≤B
    rw [abs_mul,vectorPhase,wsign_abs,one_mul]
    exact hf x
  exact (Finset.sum_le_sum (fun ξ _=>hb ξ)).trans_eq (by simp [num])

theorem linear_bounded_fourier_norm (P : Mat J I) (φ : Wgt (Vec J))
    (B : ℝ) (hφ : ∀ x,|φ x|≤B) :
    fourierNorm (fun x=>φ (P*ᵥx))≤num (Vec J)*B := by
  have hh:=fourier_norm_affine_pullback P 0 φ
  simp only [add_zero] at hh
  exact hh.trans (fourier_norm_bounded_count φ B hφ)

theorem projection_fourier_norm (P : Mat J I) (f : Wgt (Vec I)) :
    fourierNorm (banner unif P.mulVec f)≤fourierNorm f := by
  unfold fourierNorm
  apply Finset.sum_le_sum
  intro ξ _
  rw [linear_projection_fourier]
  split
  · exact le_rfl
  · simp only [abs_zero]
    exact abs_nonneg _

/-- Small linear bias also controls the change in conditional averages.
The error depends only on the number of common cells and Fourier norm. -/
theorem linear_reference_projection_error (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (γ : ℝ) (hγ : 0≤γ) (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (f : Wgt (Vec I)) :
    lcost ν (banner ν P.mulVec f) (banner unif P.mulVec f)≤
      2*γ*num (Vec J)*fourierNorm f := by
  let a:=cashbook ν P.mulVec f
  let b:=cashbook unif P.mulVec f
  obtain ⟨W,hW,hcost⟩:=bounded_discrepancy_test (mapW ν P.mulVec) a b
  let g:=banner unif P.mulVec f
  have he : lcost ν (banner ν P.mulVec f) g=
      dip ν (fun x=>f x-g x) (W∘P.mulVec) := by
    have hl : lcost ν (banner ν P.mulVec f) g=lcost (mapW ν P.mulVec) a b :=
      (mapW_avg ν P.mulVec (fun y=>|a y-b y|)).symm
    rw [hl,←hcost]
    unfold dip
    rw [mapW_avg]
    change dip ν (fun x=>banner ν P.mulVec f x-g x) (W∘P.mulVec)=
      dip ν (fun x=>f x-g x) (W∘P.mulVec)
    rw [dip_sub,dip_sub,cash_orth ν hν.nz P.mulVec f W]
  have hz : dip unif (fun x=>f x-g x) (W∘P.mulVec)=0 := by
    rw [dip_sub]
    have hh:=cash_orth unif unif_law.nz P.mulVec f W
    change dip unif g (W∘P.mulVec)=_ at hh
    rw [hh,sub_self]
  have hnorm : fourierNorm (fun x=>(f x-g x)*(W∘P.mulVec) x)≤
      2*fourierNorm f*num (Vec J) := by
    have hsub : fourierNorm (fun x=>f x-g x)≤2*fourierNorm f:=
      (fourier_norm_sub f g).trans (by linarith only [projection_fourier_norm P f])
    have hw' : fourierNorm (W∘P.mulVec)≤num (Vec J) := by
      simpa only [mul_one,Function.comp_def] using linear_bounded_fourier_norm P W 1 hW
    exact (fourier_norm_mul _ _).trans ((mul_le_mul hsub hw'
      (fourier_norm_nonneg _) (mul_nonneg (by norm_num) (fourier_norm_nonneg f))).trans_eq (by ring))
  have hh:=small_bias_test ν hν γ hγ hbias (fun x=>(f x-g x)*(W∘P.mulVec) x)
  change |dip ν (fun x=>f x-g x) (W∘P.mulVec)-dip unif (fun x=>f x-g x) (W∘P.mulVec)|≤_ at hh
  rw [hz,sub_zero,←he] at hh
  exact ((le_abs_self _).trans hh).trans
    ((mul_le_mul_of_nonneg_left hnorm hγ).trans_eq (by ring))

end
end Lax793645Proofs.Simplifications
