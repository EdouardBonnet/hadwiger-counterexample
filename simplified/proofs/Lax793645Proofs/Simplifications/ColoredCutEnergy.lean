import Lax793645Proofs.Simplifications.FilteredColoredDensities

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {O X Y B C : Type} [Fintype O] [Fintype X] [Fintype Y] [Fintype B] [Fintype C]

theorem colored_cut_energy (π : Wgt O) (hπ : IsLaw π) (κ : Wgt X) (hκ : IsLaw κ)
    (v : O→X→Y) (K : O→X→B) (S : B→Prop) (ν : Wgt B) (hν : IsLaw ν)
    (hS : ∀ x,S x → ν x≠0) (P : B→C)
    (L δ η : ℝ) (hL : 0≤L) (hδ : 0<δ) (hs : stamina (mapW ν P) δ)
    (ht : ∀ c,pr π (fun o=>L*mapW ν P c<pr (mapW κ (K o)) (fun x=>S x ∧ P x=c))≤η) :
    densityFamilyEnergy ν (colored π κ v) (coloredCutDensities ν κ v K S) P≤
      num Y*L+num C*η/δ := by
  let u (o:O):=mapW κ (v o)
  let p (o:O) (y:Y):=mapW (subW (coloredP κ v K (o,y)) S) P
  have hu o : IsLaw (u o):=mapW_law hκ _
  have hp o y : SubLaw (p o y) := by
    have hh:=subLaw_sub ((colored_ultra hπ hκ K v).labs (o,y)).sub S
    refine ⟨map_nz hh.nz P,?_⟩
    change tot (mapW (subW (coloredP κ v K (o,y)) S) P)≤1
    rw [map_mass]
    exact hh.total
  have he o c : mixW (u o) (p o) c=pr (mapW κ (K o)) (fun x=>S x ∧ P x=c) := by
    change avg (mapW κ (v o)) (fun y=>pr (subW (mapW (stained κ (v o) y) (K o)) S)
      (fun x=>P x=c))=_
    have hi y : pr (subW (mapW (stained κ (v o) y) (K o)) S) (fun x=>P x=c)=
        avg (stained κ (v o) y) (fun x=>ind (S (K o x) ∧ P (K o x)=c)) := by
      rw [pr_sub,pr,mapW_avg]
    simp_rw [hi]
    rw [stained_weighted_average κ hκ (v o)]
    exact (mapW_avg κ (K o) (fun x=>ind (S x ∧ P x=c))).symm
  have henergy : densityFamilyEnergy ν (colored π κ v) (coloredCutDensities ν κ v K S) P=
      avg π (fun o=>avg (u o) (fun y=>cellSquare (p o y) (mapW ν P))) := by
    unfold densityFamilyEnergy colored
    rw [semi_avg]
    apply avg_congr
    intro o _
    apply avg_congr
    intro y _
    exact relative_energy_cells ν _ (colored_cut_support ν hS κ v K (o,y)) P
  rw [henergy]
  apply colored_sub_energy_bound π hπ u hu p hp (mapW ν P) (mapW_law hν P) L δ η hL hδ hs
  intro c
  simpa only [he] using ht c

end
end Lax793645Proofs.Simplifications
