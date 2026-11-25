import Lax793645Proofs.Simplifications.FilteredDensityEnergy
import Lax793645Proofs.Simplifications.ColoredQuadratic

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Y]

theorem supported_density_restore (ν p : Wgt B) (hs : lsupp p ν) :
    (fun x=>ν x*density ν p x)=p := by
  funext x
  unfold density
  by_cases hp : p x=0
  · simp [hp]
  · have hν:=hs x hp
    field_simp

theorem relative_energy_cells (ν p : Wgt B) (hs : lsupp p ν) (P : B→C) :
    ode ν (banner ν P (density ν p))=cellSquare (mapW p P) (mapW ν P) := by
  unfold ode dip banner cashbook
  rw [supported_density_restore ν p hs]
  change avg ν (fun x=>(mapW p P (P x)/mapW ν P (P x))*
    (mapW p P (P x)/mapW ν P (P x)))=_
  simp_rw [←pow_two]
  rw [←mapW_avg ν P (fun c=>(mapW p P c/mapW ν P c)^2)]
  unfold avg cellSquare
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : mapW ν P c=0
  · simp [hc]
  · field_simp

theorem sub_cell_square_bound (p q : Wgt C) (hp : SubLaw p) (hq : IsLaw q)
    (δ : ℝ) (hδ : 0<δ) (hs : stamina q δ) : cellSquare p q≤δ⁻¹ := by
  have hh c : (p c)^2/q c≤δ⁻¹*p c := by
    by_cases hc : q c=0
    · rw [hc,div_zero]
      exact mul_nonneg (inv_pos_of_pos hδ).le (hp.nz _)
    have hc' : 0<q c:=lt_of_le_of_ne (hq.nz c) (Ne.symm hc)
    calc
      _≤p c/q c:=div_le_div_of_nonneg_right
        (by nlinarith only [hp.nz c,hp.weight_le_one c]) hc'.le
      _≤p c/δ:=div_le_div_of_nonneg_left (hp.nz c) hδ (hs c hc)
      _=δ⁻¹*p c:=by ring
  refine (Finset.sum_le_sum (fun c _=>hh c)).trans ?_
  rw [←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hp.total (inv_pos_of_pos hδ).le).trans_eq (mul_one _)

theorem mixed_sub_cell_square_bound (u : Wgt Y) (hu : IsLaw u)
    (p : Y→Wgt C) (hp : ∀ y,SubLaw (p y)) (q : Wgt C) (hq : IsLaw q)
    (B : ℝ) (hB : 0≤B) (hcap : ∀ c,mixW u p c≤B*q c) :
    avg u (fun y=>cellSquare (p y) q)≤num Y*B := by
  have hh y : u y*cellSquare (p y) q≤B := by
    have hc c : u y*(p y c)^2/q c≤B*p y c := by
      have h0 : u y*p y c≤B*q c:=
        (weight_le_tot (fun j=>mul_nonneg (hu.nz j) ((hp j).nz c)) y).trans (hcap c)
      by_cases hz : q c=0
      · rw [hz,div_zero]
        exact mul_nonneg hB ((hp y).nz c)
      apply (div_le_iff₀ (lt_of_le_of_ne (hq.nz c) (Ne.symm hz))).mpr
      nlinarith only [mul_le_mul_of_nonneg_right h0 ((hp y).nz c)]
    calc
      _=∑ c,u y*(p y c)^2/q c:=by unfold cellSquare; rw [Finset.mul_sum]; simp [mul_div_assoc]
      _≤∑ c,B*p y c:=Finset.sum_le_sum (fun c _=>hc c)
      _≤B:=by
        rw [←Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (hp y).total hB).trans_eq (mul_one _)
  exact (Finset.sum_le_sum (fun y _=>hh y)).trans_eq (by simp [num])

/-- The status-conditional measures may be subprobabilities, so the
prescribed Gram event can be retained without renormalizing any filter. -/
theorem colored_sub_energy_bound (μ : Wgt A) (hμ : IsLaw μ)
    (u : A→Wgt Y) (hu : ∀ o,IsLaw (u o))
    (p : A→Y→Wgt C) (hp : ∀ o y,SubLaw (p o y))
    (q : Wgt C) (hq : IsLaw q) (B δ η : ℝ) (hB : 0≤B) (hδ : 0<δ)
    (hs : stamina q δ)
    (ht : ∀ c,pr μ (fun o=>B*q c<mixW (u o) (p o) c)≤η) :
    avg μ (fun o=>avg (u o) (fun y=>cellSquare (p o y) q))≤num Y*B+num C*η/δ := by
  let F o:=avg (u o) (fun y=>cellSquare (p o y) q)
  let bad o:=∃ c,B*q c<mixW (u o) (p o) c
  have hbad : pr μ bad≤num C*η:=
    (pr_exists_le hμ.nz _).trans ((Finset.sum_le_sum (fun c _=>ht c)).trans_eq (by simp [num]))
  have hgood o (ho : ¬bad o) : F o≤num Y*B:=
    mixed_sub_cell_square_bound (u o) (hu o) (p o) (hp o) q hq B hB
      (fun c=>le_of_not_gt (fun hc=>ho ⟨c,hc⟩))
  have hall o : F o≤δ⁻¹:=(hu o).avg_le
    (fun y=>sub_cell_square_bound (p o y) q (hp o y) hq δ hδ hs)
  have hb o : F o≤num Y*B+δ⁻¹*ind (bad o) := by
    by_cases ho : bad o
    · rw [ind_one ho,mul_one]
      exact (hall o).trans (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hB))
    · rw [ind_zero ho,mul_zero,add_zero]
      exact hgood o ho
  have hh:=avg_mono hμ.nz hb
  rw [avg_add,hμ.avg_const,avg_mul'] at hh
  calc
    avg μ F≤num Y*B+δ⁻¹*pr μ bad:=hh
    _≤num Y*B+δ⁻¹*(num C*η):=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad (inv_pos_of_pos hδ).le)
    _=num Y*B+num C*η/δ:=by ring

end
end Lax793645Proofs.Simplifications
