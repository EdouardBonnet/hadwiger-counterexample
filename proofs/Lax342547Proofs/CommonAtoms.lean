import Lax342547.CommonAtoms
import Lax342547.Atoms

namespace Lax342547Proofs.CommonAtoms
open Lax342547.CommonAtoms

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.ConcreteGeometry
open Lax342547.CutProfiles
open scoped BigOperators

/--
---
conclusion: Lax342547.CommonAtoms.common_atom_sum_zero
---
-/
theorem common_atom_sum_zero {k n b degree : ℕ} (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ l i, i ∉ allowedBase k n l → z i = 0) :
    (∑ l : Tag k, atom (degree := degree) l s z (hz l)) = 0 := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum,Submodule.coe_zero]
  ext e i j
  simp_rw [Finset.sum_apply,Lax342547.Atoms.atom_component]
  have hh : (∑ l : Tag k, if l ∈ e.val then pointMoment (selectorEval (degree := degree)) s z else 0) = 0 := by
    rw [← Finset.sum_filter (s := Finset.univ) (fun l : Tag k => l ∈ e.val)
      (fun _ => pointMoment (selectorEval (degree := degree)) s z)]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,e.property]
    simpa only [two_nsmul] using ZModModule.add_self (pointMoment (selectorEval (degree := degree)) s z)
  exact congrFun (congrFun hh i) j

/--
---
conclusion: Lax342547.CommonAtoms.common_atom_constant_zero
---
-/
theorem common_atom_constant_zero {k n b degree : ℕ} (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ l i, i ∉ allowedBase k n l → z i = 0)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (heq : ∀ l, φ (atom (degree := degree) l s z (hz l)) = γ) : γ = 0 := by
  have hh := congrArg φ (Lax342547.CommonAtoms.common_atom_sum_zero s z hz)
  rw [map_sum,map_zero] at hh
  simp_rw [heq] at hh
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,ZMod.card,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    show (2 : Binary) = 0 from rfl,zero_mul,zero_add,one_mul] at hh
  exact hh

end Lax342547Proofs.CommonAtoms
