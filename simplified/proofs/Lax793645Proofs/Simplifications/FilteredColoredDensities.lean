import Lax793645Proofs.Simplifications.RelativeDensityEnergy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O X Y B : Type} [Fintype O] [Fintype X] [Fintype Y] [Fintype B]

theorem stained_weight_identity (κ : Wgt X) (hκ : IsLaw κ) (v : X→Y) (y : Y) (x : X) :
    mapW κ v y*stained κ v y x=κ x*ind (v x=y) := by
  by_cases hy : mapW κ v y=0
  · rw [hy,zero_mul]
    by_cases hx : v x=y
    · rw [ind_one hx,mul_one]
      exact (le_antisymm (by exact (weight_le_pr hκ.nz hx).trans_eq hy) (hκ.nz x)).symm
    · rw [ind_zero hx,mul_zero]
  · rw [stained,if_pos hy,onW_val]
    change mapW κ v y*(κ x*ind (v x=y)/mapW κ v y)=_
    field_simp

theorem stained_weighted_average (κ : Wgt X) (hκ : IsLaw κ) (v : X→Y) (f : Y→Wgt X) :
    avg (mapW κ v) (fun y=>avg (stained κ v y) (f y))=avg κ (fun x=>f (v x) x) := by
  unfold avg
  simp_rw [Finset.mul_sum,←mul_assoc,stained_weight_identity κ hκ v]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (v x)]
  · rw [ind_one rfl,mul_one]
  · intro y _ hy
    rw [ind_zero (Ne.symm hy),mul_zero,zero_mul]
  · simp

theorem supported_density_average (ν p : Wgt B) (hs : lsupp p ν) (f : Wgt B) :
    dip ν (density ν p) f=avg p f := by
  unfold dip avg
  simp_rw [←mul_assoc]
  simp_rw [show ∀ x,ν x*density ν p x=p x from fun x=>congr_fun (supported_density_restore ν p hs) x]

def coloredCutDensities (ν : Wgt B) (κ : Wgt X) (v : O→X→Y) (K : O→X→B)
    (S : B→Prop) : O×Y→Wgt B :=
  fun i=>density ν (subW (coloredP κ v K i) S)

theorem colored_cut_support {S : B→Prop} (ν : Wgt B) (hS : ∀ x,S x → ν x≠0)
    (κ : Wgt X) (v : O→X→Y) (K : O→X→B) (i : O×Y) :
    lsupp (subW (coloredP κ v K i) S) ν := by
  intro x hx
  apply hS x
  by_contra hh
  exact hx (by simp [subW,ind_zero hh])

/-- Every subweight of the joint orientation/status law is an unnormalized
status filter. Zero-probability statuses require no arbitrary division. -/
theorem colored_filter_representation (π : Wgt O) (hπ : IsLaw π)
    (κ : Wgt X) (hκ : IsLaw κ) (v : O→X→Y)
    (t : Wgt (O×Y)) (ht : ∀ i,0≤t i) (hcap : ∀ i,t i≤colored π κ v i) :
    ∃ F : O→Y→ℝ,(∀ o y,0≤F o y ∧ F o y≤1) ∧
      ∀ (K : O→X→B) (ν : Wgt B) (S : B→Prop),
      (∀ x,S x → ν x≠0) → ∀ f : Wgt B,
      dip ν (mixW t (coloredCutDensities ν κ v K S)) f=
        avg π (fun o=>avg κ (fun x=>f (K o x)*ind (S (K o x))*F o (v o x))) := by
  let μ:=colored π κ v
  have hμ : ∀ i,0≤μ i:=fun i=>mul_nonneg (hπ.nz i.1) (map_nz hκ.nz _ _)
  let F (o:O) (y:Y):=t (o,y)/μ (o,y)
  have hF o y : 0≤F o y ∧ F o y≤1 := by
    refine ⟨div_nonneg (ht _) (hμ _),?_⟩
    by_cases hh : μ (o,y)=0
    · simp [F,hh]
    · exact (div_le_one (lt_of_le_of_ne (hμ _) (Ne.symm hh))).mpr (hcap _)
  have he i : t i=μ i*F i.1 i.2 := by
    by_cases hh : μ i=0
    · have hz:=le_antisymm ((hcap i).trans_eq hh) (ht i)
      simp [hh,F,hz]
    · dsimp only [F]
      field_simp
  refine ⟨F,hF,fun K ν S hS f=>?_⟩
  rw [dip_density_mixture]
  have hd i : dip ν (coloredCutDensities ν κ v K S i) f=
      avg (stained κ (v i.1) i.2) (fun x=>f (K i.1 x)*ind (S (K i.1 x))) := by
    rw [coloredCutDensities,supported_density_average ν _ (colored_cut_support ν hS κ v K i)]
    change avg (subW (mapW (stained κ (v i.1) i.2) (K i.1)) S) f=_
    unfold subW
    have hh : avg (fun x=>mapW (stained κ (v i.1) i.2) (K i.1) x*ind (S x)) f=
        avg (mapW (stained κ (v i.1) i.2) (K i.1)) (fun x=>f x*ind (S x)) := by
      unfold avg
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hh,mapW_avg]
  simp_rw [hd]
  have he' (g : Wgt (O×Y)) : avg t g=avg μ (fun i=>F i.1 i.2*g i) := by
    unfold avg
    apply Finset.sum_congr rfl
    intro i _
    rw [he i]
    ring
  rw [he']
  change avg (semi π (fun o=>mapW κ (v o))) _=_
  rw [semi_avg]
  apply avg_congr
  intro o _
  simp_rw [←avg_mul']
  rw [stained_weighted_average κ hκ (v o)]
  apply avg_congr
  intro x _
  ring

end
end Lax793645Proofs.Simplifications
