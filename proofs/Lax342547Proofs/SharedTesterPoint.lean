import Lax342547.SharedTesterPoint
import Lax342547Proofs.CommonAtoms
import Lax342547Proofs.ConcreteGeometry

namespace Lax342547Proofs.SharedTesterPoint
open Lax342547.SharedTesterPoint

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteGeometry
open scoped BigOperators

/--
---
conclusion: Lax342547.SharedTesterPoint.shared_point_allowed
---
-/
theorem shared_point_allowed {k n : ℕ} (l : Tag k) :
    ∀ i,i ∉ allowedBase k n l → sharedTesterPoint (k := k) (n := n) i = 0 := by
  intro i hi
  cases i with
  | inl j => rfl
  | inr j => exact False.elim (hi trivial)

/--
---
conclusion: Lax342547.SharedTesterPoint.shared_point_eta_one
---
-/
theorem shared_point_eta_one {k n b degree r : ℕ} (hr : 2*r ≤ n) (hr0 : 0 < r) (s : Fin b → Binary) :
    eta (k := k) (b := b) (degree := degree) hr (pointMoment selectorEval s sharedTesterPoint) = 1 := by
  classical
  have ho (d t : Tag k) : blockTester (b := b) (degree := degree) hr (ordinary d t)
      (pointMoment selectorEval s sharedTesterPoint) = 0 := by
    rw [Lax342547Proofs.ConcreteGeometry.blockTester_point]
    simp [ordinary,sharedTesterPoint]
  have hl (ρ : Fin r) : sharedTesterPoint (k := k) (shared (pairLeft hr ρ)) = if ρ.val = 0 then 1 else 0 := by
    have he : 2*ρ.val < 2 ↔ ρ.val = 0 := by omega
    simp [shared,sharedTesterPoint,pairLeft,he]
  have hright (ρ : Fin r) : sharedTesterPoint (k := k) (shared (pairRight hr ρ)) = if ρ.val = 0 then 1 else 0 := by
    have he : 2*ρ.val+1 < 2 ↔ ρ.val = 0 := by omega
    simp [shared,sharedTesterPoint,pairRight,he]
  unfold eta etaO
  simp only [LinearMap.add_apply,LinearMap.sum_apply,ho,Finset.sum_const_zero,zero_add]
  rw [Lax342547Proofs.ConcreteGeometry.blockTester_point]
  simp_rw [hl,hright]
  have he : (∑ ρ : Fin r, (if ρ.val = 0 then 1 else 0 : Binary)*(if ρ.val = 0 then 1 else 0)) = 1 := by
    let z : Fin r := ⟨0,hr0⟩
    rw [Finset.sum_eq_single z]
    · simp [z]
    · intro ρ _ hρ
      have hv : ρ.val ≠ 0 := fun h => hρ (Fin.ext h)
      simp [hv]
    · simp
  exact he

end Lax342547Proofs.SharedTesterPoint
