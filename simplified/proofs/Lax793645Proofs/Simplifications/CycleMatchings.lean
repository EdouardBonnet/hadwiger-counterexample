import Lax793645Proofs.Simplifications.CycleTrace
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax793645Proofs.Simplifications
open scoped BigOperators
noncomputable section

def alternatingIndices (r : ℕ) : Fin r ⊕ Fin r ≃ Fin (2*r) :=
  Equiv.ofBijective (Sum.elim
    (fun i => (⟨2*i.val,by omega⟩ : Fin (2*r)))
    (fun i => (⟨2*i.val+1,by omega⟩ : Fin (2*r)))) (by
      constructor
      · intro x y h
        have hv := congrArg Fin.val h
        cases x <;> cases y <;> simp only [Sum.elim_inl,Sum.elim_inr] at hv
        · congr 1; apply Fin.ext; omega
        · omega
        · omega
        · congr 1; apply Fin.ext; omega
      · intro i
        by_cases h : i.val%2=0
        · refine ⟨Sum.inl ⟨i.val/2,by omega⟩,?_⟩
          apply Fin.ext; dsimp; omega
        · refine ⟨Sum.inr ⟨i.val/2,by omega⟩,?_⟩
          apply Fin.ext; dsimp; omega)

def cycleDeletedEquiv {r : ℕ} (t : Fin (2*r+1)) :
    Fin (2*r) ≃ {v : Fin (2*r+1) // v ≠ t} :=
  (finSuccAboveEquiv 0).trans {
    toFun := fun v => ⟨v.val+t,by
      intro h
      have hz : v.val=0 := add_right_cancel (h.trans (zero_add t).symm)
      exact v.property hz⟩
    invFun := fun v => ⟨v.val-t,sub_ne_zero.mpr v.property⟩
    left_inv := fun v => Subtype.ext (add_sub_cancel_right _ _)
    right_inv := fun v => Subtype.ext (sub_add_cancel _ _) }

def matchingEdge {r : ℕ} (t : Fin (2*r+1)) (i : Fin r) : Fin (2*r+1) :=
  (⟨2*i.val+1,by omega⟩ : Fin (2*r+1))+t

theorem matchingEdge_next {r : ℕ} (t : Fin (2*r+1)) (i : Fin r) :
    matchingEdge t i+1=(⟨2*i.val+2,by omega⟩ : Fin (2*r+1))+t := by
  unfold matchingEdge
  rw [add_right_comm]
  congr 1
  apply Fin.ext
  simp only [Fin.val_add,Fin.val_one']
  have hi := i.isLt
  have hn : 1 < 2*r+1 := by omega
  rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt (by omega)]

/-- The indicated cycle edges cover every vertex except the deleted one once. -/
theorem matching_covers {r : ℕ} {W : Type*} [AddCommMonoid W]
    (t : Fin (2*r+1)) (w : Fin (2*r+1) → W) :
    (∑ i : Fin r, (w (matchingEdge t i)+w (matchingEdge t i+1))) =
      ∑ v : {v : Fin (2*r+1) // v ≠ t}, w v.val := by
  rw [← (cycleDeletedEquiv t).sum_comp,← (alternatingIndices r).sum_comp]
  rw [Fintype.sum_sum_type,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [matchingEdge_next]
  rfl

def matchingShared {r : ℕ} (x : Fin (2*r+1) → ZMod 2) (t : Fin (2*r+1)) : ZMod 2 :=
  ∑ i : Fin r, x (matchingEdge t i)

/-- The shared functional is defined on components. Its cut identity follows
from the matching itself, with no descent or routing choice. -/
theorem matchingShared_cut {r : ℕ} (s : Fin (2*r+1) → ZMod 2) (t : Fin (2*r+1)) :
    matchingShared (fun l => s l+s (l+1)) t=(∑ l, s l)+s t := by
  unfold matchingShared
  rw [matching_covers,Fintype.sum_eq_add_sum_subtype_ne s t]
  have h : s t+s t=0 := CharTwo.add_self_eq_zero _
  rw [add_right_comm,h,zero_add]

/-- Intrinsic trace bits give exactly the tester identity used on marked
profiles. The only input is the adjacent shared-trace identity. -/
theorem matching_tester_identity {r : ℕ} (τ o x : Fin (2*r+1) → ZMod 2)
    (htrace : ∀ l, x l=(τ l+o l)+(τ (l+1)+o (l+1))) (t : Fin (2*r+1)) :
    (∑ l, o l)+matchingShared x t=(∑ l, τ l)+(τ t+o t) := by
  have he : x=(fun l => (τ l+o l)+(τ (l+1)+o (l+1))) := funext htrace
  rw [he,matchingShared_cut,Finset.sum_add_distrib]
  have hz : (∑ l, o l)+(∑ l, o l)=0 := CharTwo.add_self_eq_zero _
  calc
    _ = ((∑ l, τ l)+(τ t+o t))+((∑ l, o l)+(∑ l, o l)) := by abel
    _ = _ := by rw [hz,add_zero]

/-- Collecting the matching functionals puts one scalar shared tester on each
component; there is no separate shared-demand routing problem. -/
theorem matching_gradient_coefficients {r : ℕ}
    (a x : Fin (2*r+1) → ZMod 2) :
    (∑ t, a t*matchingShared x t) =
      ∑ e, (∑ t, ∑ i : Fin r, if matchingEdge t i=e then a t else 0)*x e := by
  classical
  unfold matchingShared
  simp only [Finset.mul_sum,Finset.sum_mul,ite_mul,zero_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

end
end Lax793645Proofs.Simplifications
