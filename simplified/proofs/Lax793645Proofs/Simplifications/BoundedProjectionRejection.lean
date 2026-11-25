import Lax793645Proofs.Simplifications.ProjectedDensityMend
import Lax793645Proofs.Simplifications.ProjectionRefinementBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type} [Fintype A] [Fintype B]

theorem density_lcost_le_variation (ν p q : Wgt A) (hν : ∀ x,0≤ν x) :
    lcost ν (density ν p) (density ν q)≤varOne p q := by
  unfold lcost avg varOne density
  apply sum_le_sum
  intro x _
  dsimp only
  rw [←sub_div,abs_div,abs_of_nonneg (hν x)]
  by_cases hx : ν x=0
  · rw [hx,zero_mul]
    exact abs_nonneg _
  · exact le_of_eq (by field_simp)

theorem reduced_density_approximation (ν p q f : Wgt A) (hν : ∀ x,0≤ν x) :
    lcost ν (density ν q) f≤varOne p q+lcost ν (density ν p) f := by
  have hh : lcost ν (density ν q) f≤lcost ν (density ν p) (density ν q)+
      lcost ν (density ν p) f := by
    unfold lcost
    rw [←avg_add]
    apply avg_mono hν
    intro x
    rw [abs_sub_comm (density ν p x) (density ν q x)]
    exact abs_sub_le _ _ _
  exact hh.trans (add_le_add (density_lcost_le_variation ν p q hν) le_rfl)

theorem reduced_projection_bounds (ν p pg : Wgt A) (hν : IsLaw ν) (P : A→B)
    (hpg : ∀ x,0≤pg x ∧ pg x≤p x) (C : ℝ)
    (hp : ∀ x,0≤banner ν P (density ν p) x ∧ banner ν P (density ν p) x≤C) :
    ∀ x,0≤banner ν P (density ν pg) x ∧ banner ν P (density ν pg) x≤C := by
  intro x
  exact ⟨book_nonneg ν P hν _ (fun x=>div_nonneg (hpg x).1 (hν.nz x)) _,
    (book_order ν P hν _ _ (fun x=>div_le_div_of_nonneg_right (hpg x).2 (hν.nz x)) _).trans
      (hp x).2⟩

/-- A small deleted mass changes a product of bounded projected
densities by at most the projection bound times that mass. No assertion
is made about products of the unbounded original densities. -/
theorem projected_rejection_overlap (ν p q pg qg : Wgt A) (hν : IsLaw ν) (P : A→B)
    (hpg : ∀ x,0≤pg x ∧ pg x≤p x) (hqg : ∀ x,0≤qg x ∧ qg x≤q x)
    (C : ℝ) (hC : 0≤C)
    (hp : ∀ x,0≤banner ν P (density ν p) x ∧ banner ν P (density ν p) x≤C)
    (hq : ∀ x,0≤banner ν P (density ν q) x ∧ banner ν P (density ν q) x≤C) :
    dip ν (banner ν P (density ν p)) (banner ν P (density ν q))≤
      dip ν (banner ν P (density ν pg)) (banner ν P (density ν qg))+
        C*(varOne p pg+varOne q qg) := by
  have hh:=bounded_overlap_transfer ν (banner ν P (density ν pg)) (banner ν P (density ν qg))
    (banner ν P (density ν p)) (banner ν P (density ν q)) hν.nz C hp hq
    (fun x=>(reduced_projection_bounds ν p pg hν P hpg C hp x).1)
    (fun x=>(reduced_projection_bounds ν q qg hν P hqg C hq x).1)
  apply hh.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add
    ((projection_lcost_contract ν hν.nz P _ _).trans (density_lcost_le_variation ν p pg hν.nz))
    ((projection_lcost_contract ν hν.nz P _ _).trans (density_lcost_le_variation ν q qg hν.nz))

end
end Lax793645Proofs.Simplifications
