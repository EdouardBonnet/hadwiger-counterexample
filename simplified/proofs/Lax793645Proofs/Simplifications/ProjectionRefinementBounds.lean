import Lax793645Proofs.Simplifications.LinearDensityRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem lcost_symm (ν f g : Wgt A) : lcost ν f g=lcost ν g f := by
  unfold lcost
  apply avg_congr
  intro x _
  exact abs_sub_comm _ _

theorem projection_lcost_contract (ν : Wgt A) (hν : ∀ x,0≤ν x)
    (P : A→B) (f g : Wgt A) :
    lcost ν (banner ν P f) (banner ν P g)≤lcost ν f g := by
  obtain ⟨W,hW,hcost⟩:=bounded_discrepancy_test ν (banner ν P f) (banner ν P g)
  have he : dip ν (fun x=>banner ν P f x-banner ν P g x) W=
      dip ν (fun x=>f x-g x) (banner ν P W) := by
    rw [dip_sub,dip_sub,projection_self_adjoint ν hν P f W,
      projection_self_adjoint ν hν P g W]
  rw [←hcost,he]
  refine (le_abs_self _).trans ((abs_avg_le hν).trans ?_)
  apply avg_mono hν
  intro x
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left
    (cashbook_bound ν hν P W 1 zero_le_one hW (P x)) (abs_nonneg _)).trans_eq (mul_one _)

theorem cashbook_bound_of_banner (ν f : Wgt A) (hν : ∀ x,0≤ν x)
    (P : A→B) (L : ℝ) (hL : 0≤L)
    (h : ∀ x,0≤banner ν P f x ∧ banner ν P f x≤L) :
    ∀ c,0≤cashbook ν P f c ∧ cashbook ν P f c≤L := by
  intro c
  by_cases hc : mapW ν P c=0
  · simp only [cashbook,hc,div_zero]
    exact ⟨le_rfl,hL⟩
  have hp : 0<mapW ν P c:=lt_of_le_of_ne (map_nz hν _ _) (Ne.symm hc)
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos hν hp
  simpa only [banner,Function.comp_apply,hx] using h x

/-- Refining a partition preserves L1 approximation up to a factor two. -/
theorem refined_projection_lcost (ν : Wgt A) (hν : SubLaw ν)
    (P : A→B) (Q : B→C) (f : Wgt A) :
    lcost ν f (banner ν P f)≤2*lcost ν f (banner ν (Q∘P) f) := by
  let g:=banner ν (Q∘P) f
  obtain ⟨W,hW,hcost⟩:=bounded_discrepancy_test ν f (banner ν P f)
  have he : dip ν (fun x=>f x-banner ν P f x) W=
      dip ν (fun x=>f x-g x) (fun x=>W x-banner ν P W x) := by
    have ho:=refinement_test_orthogonal ν hν.nz P Q f W
    rw [dip_sub]
    have hs:=projection_self_adjoint ν hν.nz P f W
    rw [hs]
    conv_rhs => rw [dip_sym,dip_sub,dip_sym,dip_sym ν (banner ν P W)]
    rw [dip_sub,dip_sub]
    change _=dip ν f W-dip ν g W-(dip ν f (banner ν P W)-dip ν g (banner ν P W))
    rw [ho]
    ring
  have hb x : |W x-banner ν P W x|≤2 := by
    have hp : |banner ν P W x|≤1:=cashbook_bound ν hν.nz P W 1 zero_le_one hW (P x)
    exact (abs_sub _ _).trans (by linarith only [hW x,hp])
  rw [←hcost,he]
  refine (le_abs_self _).trans ((abs_avg_le hν.nz).trans ?_)
  unfold lcost
  rw [←avg_mul']
  apply avg_mono hν.nz
  intro x
  rw [abs_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)

end
end Lax793645Proofs.Simplifications
