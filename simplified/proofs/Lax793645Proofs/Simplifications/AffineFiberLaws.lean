import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AmbientBatchSlots

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Y Z C : Type} [AddCommGroup Z] [Module F Z] [AddCommGroup C] [Module F C]

/-- A common linear cell can be prescribed by changing only the free
coordinates. The other coordinates and the kernel parameter remain free. -/
def affineCellChart (A : Z→ₗ[F] C) (s : C→ₗ[F] Z)
    (hs : ∀ c,A (s c)=c) (b : C) : Z≃C×A.ker where
  toFun z:=(A z+b,⟨z-s (A z),by simp only [LinearMap.mem_ker,map_sub,hs,sub_self]⟩)
  invFun x:=x.2.val+s (x.1-b)
  left_inv z:=by simp only [add_sub_cancel_right,sub_add_cancel]
  right_inv x:=by
    apply Prod.ext
    · change A (x.2.val+s (x.1-b))+b=x.1
      rw [map_add,show A x.2.val=0 from x.2.property,hs,zero_add,sub_add_cancel]
    · apply Subtype.ext
      change x.2.val+s (x.1-b)-s (A (x.2.val+s (x.1-b)))=x.2.val
      rw [map_add,show A x.2.val=0 from x.2.property,hs,zero_add,add_sub_cancel_right]

theorem affine_cell_coordinates (A : Z→ₗ[F] C) (s : C→ₗ[F] Z)
    (hs : ∀ c,A (s c)=c) (b c : C) (k : A.ker) :
    A ((affineCellChart A s hs b).symm (c,k))+b=c := by
  exact congrArg Prod.fst ((affineCellChart A s hs b).apply_symm_apply (c,k))

variable [Fintype Y] [Fintype Z] [Fintype C] (A : Z→ₗ[F] C)
  (s : C→ₗ[F] Z) (hs : ∀ c,A (s c)=c)

/-- Exact fiber integration, with no reciprocal cell mass. In particular
every distribution on the non-free coordinates is unchanged. -/
theorem affine_fiber_average [Fintype A.ker] (μ : Wgt Y) (b : Y→C) (f : Y→Z→ℝ) :
    avg (pairW μ unif) (fun x=>f x.1 x.2)=
      avg μ (fun y=>avg (pairW unif unif) (fun x : C×A.ker=>
        f y ((affineCellChart A s hs (b y)).symm x))) := by
  rw [pairW_avg]
  apply congrArg (avg μ)
  funext y
  have hh:=mapW_avg (unif : Wgt Z) (affineCellChart A s hs (b y))
    (fun x=>f y ((affineCellChart A s hs (b y)).symm x))
  simp only [Equiv.symm_apply_apply] at hh
  rw [unif_equiv, pair_unif] at hh
  exact hh.symm

include s hs in
/-- The joint common cell is uniform independently of all tester
coordinates, even when its affine offset depends on those coordinates. -/
theorem affine_cell_independence (μ : Wgt Y) (b : Y→C) :
    mapW (pairW μ unif) (fun x : Y×Z=>(x.1,A x.2+b x.1))=pairW μ unif := by
  let : Fintype A.ker:=Fintype.ofFinite _
  funext x
  change pr (pairW μ unif) (fun y=>(y.1,A y.2+b y.1)=x)=_
  unfold pr
  rw [affine_fiber_average A s hs μ b (fun y z=>ind ((y,A z+b y)=x))]
  have he (y : Y) (z : C×A.ker) :
      (y,A ((affineCellChart A s hs (b y)).symm z)+b y)= (y,z.1) := by
    rw [affine_cell_coordinates]
  simp_rw [he]
  simp only [pairW_avg,unif_law.avg_const]
  have hi : mapW (pairW μ (unif : Wgt C)) (_root_.id) x=pairW μ unif x := by
    simp [mapW]
  simpa only [mapW,pr,pairW_avg,id_eq] using hi

include s hs in
/-- The common cell remains uniform after restricting any tester-only
event; this is the version needed for the clean tester coordinates. -/
theorem affine_cell_restriction (μ : Wgt Y) (b : Y→C) (E : Y→Prop) (H : C→Prop) :
    pr (pairW μ unif) (fun x=>E x.1 ∧ H (A x.2+b x.1))=
      pr μ E*pr unif H := by
  have hh:=mapW_pr (pairW μ unif) (fun x : Y×Z=>(x.1,A x.2+b x.1))
    (fun x=>E x.1 ∧ H x.2)
  rw [affine_cell_independence A s hs μ b,pairW_pr] at hh
  exact hh.symm

end
end Lax793645Proofs.Simplifications
