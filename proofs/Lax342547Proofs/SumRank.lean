import Lax342547.SumRank
import Lax342547Proofs.RestrictionRank
import Lax342547.SpanDeficits

namespace Lax342547Proofs.SumRank
open Lax342547.SumRank

set_option backward.isDefEq.respectTransparency false
open Lax342547.SpanDeficits
open scoped BigOperators

/--
---
conclusion: Lax342547.SumRank.stacked_rank
---
-/
theorem stacked_rank {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (hS : ∀ i, LinearMap.range (M i) ≤ S i) :
    Module.finrank K (LinearMap.range (LinearMap.pi (fun i => (M i).codRestrict (S i)
      (fun v => hS i (LinearMap.mem_range_self _ v))))) =
      Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V)) := by
  let B := LinearMap.pi (fun i => (M i).codRestrict (S i) (fun v => hS i (LinearMap.mem_range_self _ v)))
  have hker : LinearMap.ker B = ⨅ i, LinearMap.ker (M i) := by
    ext v
    simp only [B,LinearMap.ker_pi,Submodule.mem_iInf,LinearMap.mem_ker]
    constructor
    · intro h i
      exact congrArg Subtype.val (h i)
    · intro h i
      exact Subtype.ext (h i)
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,hker,Subspace.dualAnnihilator_iInf_eq]
  apply congrArg (fun Z : Submodule K (Module.Dual K V) => Module.finrank K Z)
  apply iSup_congr
  intro i
  exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker (M i)).symm


/--
---
conclusion: Lax342547.SumRank.sum_rank_deficit
---
-/
theorem sum_rank_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (hS : ∀ i, LinearMap.range (M i) ≤ S i) :
    (∑ i, Module.finrank K (LinearMap.range (M i))) ≤
      Module.finrank K (LinearMap.range (∑ i, M i))+
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W))+
      ((∑ i, Module.finrank K (LinearMap.range (M i).dualMap))-
        Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V))) := by
  classical
  let B := LinearMap.pi (fun i => (M i).codRestrict (S i) (fun v => hS i (LinearMap.mem_range_self _ v)))
  have hh := Lax342547Proofs.RestrictionRank.finrank_le_map_add_ker (addition S) (LinearMap.range B)
  rw [← LinearMap.range_comp,Lax342547.SpanDeficits.addition_kernel_deficit] at hh
  have hsum : (addition S).comp B = ∑ i, M i := by
    ext v
    simp [addition,B,LinearMap.lsum_apply]
  rw [hsum,Lax342547.SumRank.stacked_rank M S hS] at hh
  have hle : Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V)) ≤
      ∑ i, Module.finrank K (LinearMap.range (M i).dualMap) := by
    have hker := (addition (fun i => LinearMap.range (M i).dualMap)).finrank_range_add_finrank_ker
    rw [Lax342547.SpanDeficits.addition_range,Module.finrank_pi_fintype] at hker
    omega
  simp only [LinearMap.finrank_range_dualMap_eq_finrank_range] at *
  omega

end Lax342547Proofs.SumRank
