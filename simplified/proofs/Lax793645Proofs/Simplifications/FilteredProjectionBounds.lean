import Lax793645Proofs.Simplifications.FilteredColoredDensities
import Lax793645Proofs.Simplifications.UniformHitBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O X Y B C : Type} [Fintype O] [Fintype X] [Fintype Y] [Fintype B] [Fintype C]

theorem colored_cut_density_nonneg (π : Wgt O) (hπ : IsLaw π) (κ : Wgt X) (hκ : IsLaw κ)
    (v : O→X→Y) (K : O→X→B) (S : B→Prop) (ν : Wgt B) (hν : ∀ x,0≤ν x)
    (i : O×Y) (x : B) : 0≤coloredCutDensities ν κ v K S i x := by
  exact div_nonneg (subW_nonneg ((colored_ultra hπ hκ K v).labs i).nz S x) (hν x)

/-- Cell tails bound every filtered projected density, with no division
by the mass of the filter. The bound is independent of partition size. -/
theorem filtered_cut_projection_bound (π : Wgt O) (hπ : IsLaw π)
    (κ : Wgt X) (hκ : IsLaw κ) (v : O→X→Y) (K : O→X→B)
    (S : B→Prop) (ν : Wgt B) (hν : IsLaw ν) (hS : ∀ x,S x → ν x≠0)
    (P : B→C) (L δ η : ℝ) (hL : 0≤L) (hδ : 0<δ) (hsmall : η≤δ)
    (hs : stamina (mapW ν P) δ)
    (ht : ∀ c,pr π (fun o=>L*mapW ν P c<pr (mapW κ (K o)) (fun x=>S x ∧ P x=c))≤η)
    (t : Wgt (O×Y)) (ht0 : ∀ i,0≤t i) (htcap : ∀ i,t i≤colored π κ v i) :
    ∀ x,0≤banner ν P (mixW t (coloredCutDensities ν κ v K S)) x ∧
      banner ν P (mixW t (coloredCutDensities ν κ v K S)) x≤L+1 := by
  obtain ⟨F,hF,hrep⟩:=colored_filter_representation (B:=B) π hπ κ hκ v t ht0 htcap
  let d:=mixW t (coloredCutDensities ν κ v K S)
  have hd x : 0≤d x:=avg_nonneg ht0 (fun i=>colored_cut_density_nonneg π hπ κ hκ v K S ν hν.nz i x)
  have hnum c : mapW (fun x=>ν x*d x) P c≤
      avg π (fun o=>pr (mapW κ (K o)) (fun x=>S x ∧ P x=c)) := by
    have he : mapW (fun x=>ν x*d x) P c=dip ν d (fun x=>ind (P x=c)) := by
      unfold mapW pr dip avg
      simp only [mul_assoc]
    rw [he,hrep K ν S hS]
    apply avg_mono hπ.nz
    intro o
    unfold pr
    rw [mapW_avg]
    apply avg_mono hκ.nz
    intro x
    rw [ind_and]
    have hh:=mul_le_mul_of_nonneg_left (hF o (v o x)).2
      (mul_nonneg (ind_nonneg (P (K o x)=c)) (ind_nonneg (S (K o x))))
    simpa only [mul_one,one_mul,mul_comm] using hh
  intro x
  change 0≤cashbook ν P d (P x) ∧ cashbook ν P d (P x)≤L+1
  have hden : 0≤mapW ν P (P x):=map_nz hν.nz _ _
  refine ⟨div_nonneg (map_nz (fun y=>mul_nonneg (hν.nz y) (hd y)) P _) hden,?_⟩
  by_cases hz : mapW ν P (P x)=0
  · simp only [cashbook,hz,div_zero]
    linarith only [hL]
  have hpos : 0<mapW ν P (P x):=lt_of_le_of_ne hden (Ne.symm hz)
  apply (div_le_iff₀ hpos).mpr
  have hh:=hit_mean_bound π (fun o=>pr (mapW κ (K o)) (fun y=>S y ∧ P y=P x)) hπ
    (fun o=>(pr_le_tot (mapW_law hκ (K o)).nz).trans_eq (mapW_law hκ (K o)).total)
    L (mapW ν P (P x)) η (mul_nonneg hL hden) (ht (P x))
  have he:=hsmall.trans (hs (P x) hz)
  have hn:=(hnum (P x)).trans hh
  nlinarith only [hn,he]

end
end Lax793645Proofs.Simplifications
