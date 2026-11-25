import Lax793645Proofs.Simplifications.QuadraticProjection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalFlags

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real
open scoped BigOperators
noncomputable section
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

def cellSquare (p q : Wgt C) := ∑ c, (p c)^2/q c

theorem cell_square_bound (p q : Wgt C) (hp : IsLaw p) (hq : IsLaw q)
    (δ : ℝ) (hδ : 0<δ) (hs : stamina q δ) : cellSquare p q ≤ δ⁻¹ := by
  have h (c : C) : (p c)^2/q c≤δ⁻¹*p c := by
    by_cases hc : q c=0
    · rw [hc,div_zero]; exact mul_nonneg (inv_pos_of_pos hδ).le (hp.nz _)
    have hc' : 0<q c := lt_of_le_of_ne (hq.nz c) (Ne.symm hc)
    calc (p c)^2/q c ≤ p c/q c := div_le_div_of_nonneg_right
           (by nlinarith only [hp.nz c,hp.weight_le_one c]) hc'.le
         _ ≤ p c/δ := div_le_div_of_nonneg_left (hp.nz c) hδ (hs c hc)
         _ = _ := by ring
  exact (sum_le_sum fun c _ => h c).trans_eq (by
    rw [←Finset.mul_sum]; change δ⁻¹*tot p=δ⁻¹; rw [hp.total,mul_one])

theorem mixed_cell_square_bound (u : Wgt Y) (hu : IsLaw u)
    (p : Y→Wgt C) (hp : ∀ y, IsLaw (p y)) (q : Wgt C) (hq : IsLaw q)
    (B : ℝ) (hB : 0≤B) (hcap : ∀ c,mixW u p c≤B*q c) :
    avg u (fun y => cellSquare (p y) q) ≤ num Y*B := by
  have h (y : Y) : u y*cellSquare (p y) q ≤ B := by
    have hc (c : C) : u y*(p y c)^2/q c ≤ B*p y c := by
      have h0 : u y*p y c ≤ B*q c :=
        (weight_le_tot (fun j => mul_nonneg (hu.nz j) ((hp j).nz c)) y).trans (hcap c)
      by_cases hz : q c=0
      · rw [hz,div_zero]; exact mul_nonneg hB ((hp y).nz c)
      apply (div_le_iff₀ (lt_of_le_of_ne (hq.nz c) (Ne.symm hz))).mpr
      nlinarith only [mul_le_mul_of_nonneg_right h0 ((hp y).nz c)]
    calc _ = ∑ c, u y*(p y c)^2/q c := by unfold cellSquare; rw [Finset.mul_sum]; simp [mul_div_assoc]
         _ ≤ ∑ c, B*p y c := sum_le_sum fun c _ => hc c
         _ = B := by
           rw [←Finset.mul_sum]; change B*tot (p y)=B; rw [(hp y).total,mul_one]
  exact (sum_le_sum fun y _ => h y).trans_eq (by simp [num])

theorem colored_quadratic_bound [Nonempty B]
    (μ : Wgt A) (w : Wgt X) (hμ : IsLaw μ) (hw : IsLaw w)
    (K : A→X→B) (v : A→X→Y) (f : B→C)
    (B δ η : ℝ) (hB : 0≤B) (hδ : 0<δ)
    (hs : stamina (mapW unif f) δ)
    (ht : ∀ c, pr μ (fun o => B*mapW unif f c < mapW (mapW w (K o)) f c)≤η) :
    quadraticBudget (colored μ w v) (coloredP w v K) f ≤ num Y*B+num C*η/δ := by
  classical
  let q := mapW unif f
  have hq : IsLaw q := mapW_law unif_law f
  let u (a : A) := mapW w (v a)
  let p (a : A) (y : Y) := mapW (mapW (stained w (v a) y) (K a)) f
  have hu a : IsLaw (u a) := mapW_law hw _
  have hp a y : IsLaw (p a y) := mapW_law (mapW_law (stained_law _ hw _) _) _
  have he a : mixW (u a) (p a)=mapW (mapW w (K a)) f := by
    unfold p
    rw [←map_mix,←map_mix]
    exact congrArg (fun z => mapW (mapW z (K a)) f) (stain_inputs (v a) hw).symm
  let F a := avg (u a) (fun y => cellSquare (p a y) q)
  let bad a := ∃ c, B*q c < mapW (mapW w (K a)) f c
  have hbad : pr μ bad≤num C*η :=
    (pr_exists_le hμ.nz _).trans ((sum_le_sum fun c _ => ht c).trans_eq (by simp [num]))
  have hgood a (ha : ¬bad a) : F a≤num Y*B := by
    apply mixed_cell_square_bound _ (hu a) _ (hp a) q hq B hB
    rw [he a]
    exact fun c => le_of_not_gt fun hc => ha ⟨c,hc⟩
  have hall a : F a≤δ⁻¹ :=
    (hu a).avg_le fun y => cell_square_bound _ q (hp a y) hq δ hδ hs
  have hbound a : F a ≤ num Y*B + δ⁻¹*ind (bad a) := by
    by_cases ha : bad a
    · rw [ind_one ha,mul_one]
      exact (hall a).trans (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hB))
    · rw [ind_zero ha,mul_zero,add_zero]; exact hgood a ha
  have h := avg_mono hμ.nz hbound
  rw [avg_add,hμ.avg_const,avg_mul'] at h
  have hright := mul_le_mul_of_nonneg_left hbad (inv_pos_of_pos hδ).le
  have henergy : quadraticBudget (colored μ w v) (coloredP w v K) f=avg μ F := by
    unfold quadraticBudget colored
    rw [semi_avg]
    apply avg_congr
    intro a _
    apply avg_congr
    intro y _
    exact quadratic_cells _ f
  rw [henergy]
  calc avg μ F ≤ num Y*B+δ⁻¹*pr μ bad := h
       _ ≤ num Y*B+δ⁻¹*(num C*η) := add_le_add le_rfl hright
       _ = num Y*B+num C*η/δ := by ring

theorem colored_mixture (μ : Wgt A) (w : Wgt X) (hw : IsLaw w)
    (K : A→X→B) (v : A→X→Y) :
    mixW (colored μ w v) (coloredP w v K)=mixW μ (fun a => mapW w (K a)) := by
  funext b
  unfold mixW colored
  rw [semi_avg]
  apply avg_congr
  intro a _
  have he : mixW (mapW w (v a)) (fun y => mapW (stained w (v a) y) (K a))=
      mapW w (K a) := by
    rw [←map_mix,←stain_inputs (v a) hw]
  exact congr_fun he b

end
end Lax793645Proofs.Simplifications
