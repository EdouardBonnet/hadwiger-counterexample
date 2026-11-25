import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def fourCorner (A B C : Vec I→ₗ[F] Vec I→ₗ[F] F)
    (f₀ f₁ f₂ f₃ : Wgt (Vec I)) : ℝ :=
  avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
    f₀ x*f₁ y*f₂ z*f₃ (x+y+z)*wsign (A x y+B x z+C y z))))

theorem four_corner_rank (A B C : Vec I→ₗ[F] Vec I→ₗ[F] F)
    (f₀ f₁ f₂ f₃ : Wgt (Vec I))
    (h₀ : ∀ x,|f₀ x|≤1) (h₁ : ∀ x,|f₁ x|≤1)
    (h₂ : ∀ x,|f₂ x|≤1) (h₃ : ∀ x,|f₃ x|≤1) :
    |fourCorner A B C f₀ f₁ f₂ f₃|≤bp (-(rk (A+B):ℝ)/2) := by
  classical
  let U s x := f₀ x*f₃ (x+s)*wsign (B x s)
  let V s y := f₁ y*f₂ (y+s)*wsign (C y (y+s))
  let T s x y := U s x*V s y*wsign ((A+B) x y)
  have hU s x : |U s x|≤1 := by
    simp only [U,abs_mul,wsign_abs,mul_one]
    simpa using mul_le_mul (h₀ x) (h₃ (x+s)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hV s y : |V s y|≤1 := by
    simp only [V,abs_mul,wsign_abs,mul_one]
    simpa using mul_le_mul (h₁ y) (h₂ (y+s)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have heq : fourCorner A B C f₀ f₁ f₂ f₃=
      avg unif (fun s=>avg unif (fun y=>V s y*
        avg unif (fun x=>U s x*wsign ((A+B) x y)))) := by
    calc
      fourCorner A B C f₀ f₁ f₂ f₃=
          avg unif (fun x=>avg unif (fun y=>avg unif (fun s=>T s x y))) := by
        apply avg_congr
        intro x _
        apply avg_congr
        intro y _
        rw [←phase_trans y]
        apply avg_congr
        intro s _
        have hxy : x+y+(s+y)=x+s := by
          have hy : y+y=0 := ZModModule.add_self _
          calc
            x+y+(s+y)=x+s+(y+y) := by abel
            _=x+s := by rw [hy,add_zero]
        simp only [hxy,T,U,V,LinearMap.add_apply,map_add,wsign_add]
        rw [show s+y=y+s from add_comm _ _]
        ring
      _=avg unif (fun x=>avg unif (fun s=>avg unif (fun y=>T s x y))) :=
        avg_congr (fun x _=>avg_avg _ _ _)
      _=avg unif (fun s=>avg unif (fun x=>avg unif (fun y=>T s x y))) := avg_avg _ _ _
      _=avg unif (fun s=>avg unif (fun y=>avg unif (fun x=>T s x y))) :=
        avg_congr (fun s _=>avg_avg _ _ _)
      _=_ := by
        apply avg_congr
        intro s _
        apply avg_congr
        intro y _
        rw [←avg_mul']
        apply avg_congr
        intro x _
        unfold T
        ring
  rw [heq]
  exact (abs_avg_le unif_law.nz).trans (unif_law.avg_le fun s=>
    walsh_bound (A+B) (U s) (V s) (hU s) (hV s))

theorem bilinear_flip_rank (A : Vec I→ₗ[F] Vec I→ₗ[F] F) : rk A.flip=rk A := by
  have he : avg (pairW unif unif) (fun z=>wsign (A.flip z.1 z.2))=
      avg (pairW unif unif) (fun z=>wsign (A z.1 z.2)) := by
    simp only [pairW_avg,LinearMap.flip_apply]
    exact avg_avg _ _ _
  rw [wsign_bilin,wsign_bilin] at he
  have hi : Function.Injective bp := (show StrictMono bp from fun _ _ h=>bp_lt h).injective
  have hh := neg_inj.mp (hi he)
  exact_mod_cast hh

theorem four_corner_swap_xy (A B C : Vec I→ₗ[F] Vec I→ₗ[F] F)
    (f₀ f₁ f₂ f₃ : Wgt (Vec I)) :
    fourCorner A B C f₀ f₁ f₂ f₃=fourCorner A.flip C B f₁ f₀ f₂ f₃ := by
  unfold fourCorner
  rw [avg_avg]
  apply avg_congr
  intro y _
  apply avg_congr
  intro x _
  apply avg_congr
  intro z _
  simp only [LinearMap.flip_apply]
  rw [show A x y+C y z+B x z=A x y+B x z+C y z by abel]
  ac_rfl

theorem four_corner_swap_yz (A B C : Vec I→ₗ[F] Vec I→ₗ[F] F)
    (f₀ f₁ f₂ f₃ : Wgt (Vec I)) :
    fourCorner A B C f₀ f₁ f₂ f₃=fourCorner B A C.flip f₀ f₂ f₁ f₃ := by
  unfold fourCorner
  apply avg_congr
  intro x _
  rw [avg_avg]
  apply avg_congr
  intro z _
  apply avg_congr
  intro y _
  simp only [LinearMap.flip_apply]
  ac_rfl

/-- All three ranks in the proposed four-corner estimate. For matrix
bilinear forms, `flip` is transpose. -/
theorem four_corner_max_rank (A B C : Vec I→ₗ[F] Vec I→ₗ[F] F)
    (f₀ f₁ f₂ f₃ : Wgt (Vec I))
    (h₀ : ∀ x,|f₀ x|≤1) (h₁ : ∀ x,|f₁ x|≤1)
    (h₂ : ∀ x,|f₂ x|≤1) (h₃ : ∀ x,|f₃ x|≤1) :
    |fourCorner A B C f₀ f₁ f₂ f₃|≤
      bp (-(max (max (rk (A+B)) (rk (A+C.flip))) (rk (B+C)):ℝ)/2) := by
  have h₁' := four_corner_rank A B C f₀ f₁ f₂ f₃ h₀ h₁ h₂ h₃
  have h₂' := four_corner_rank A.flip C B f₁ f₀ f₂ f₃ h₁ h₀ h₂ h₃
  rw [←four_corner_swap_xy] at h₂'
  have hflip : A.flip+C=(A+C.flip).flip := by ext x y; rfl
  rw [hflip,bilinear_flip_rank] at h₂'
  have h₃' := four_corner_rank B.flip C.flip A f₂ f₀ f₁ f₃ h₂ h₀ h₁ h₃
  rw [←four_corner_swap_xy,←four_corner_swap_yz] at h₃'
  have hflip' : B.flip+C.flip=(B+C).flip := by ext x y; rfl
  rw [hflip',bilinear_flip_rank] at h₃'
  rcases max_choice (max (rk (A+B):ℝ) (rk (A+C.flip):ℝ)) (rk (B+C):ℝ) with he|he
  · rw [he]
    rcases max_choice (rk (A+B):ℝ) (rk (A+C.flip):ℝ) with hf|hf
    · rwa [hf]
    · rwa [hf]
  · rwa [he]

end
end Lax793645Proofs.Simplifications
