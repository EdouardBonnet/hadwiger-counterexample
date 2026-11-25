import Lax793645Proofs.Simplifications.OneGradientTargets
import Lax793645Proofs.Simplifications.OneProtectedKeys

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneEffectivePins (P : Bool→Comp p.g→Space (Ray p n)) (i : Bool) : Space (Profile p n) :=
  Xspace p n⊓Submodule.pi Set.univ (fun e=>quadraticSquares (P i e))

theorem one_effective_mem (P : Bool→Comp p.g→Space (Ray p n)) (i : Bool) (z : Profile p n) :
    z∈oneEffectivePins P i↔z∈Xspace p n ∧∀ e,z e∈quadraticSquares (P i e) := by
  simp [oneEffectivePins]

theorem one_joint_effective (P : Bool→Comp p.g→Space (Ray p n)) (z : JointProfile p n)
    (hz : z∈jointXspace) (hp : ∀ e,z e∈quadraticSquares (jointSpace (fun i=>P i e))) :
    ∃ u : Bool→Profile p n,z=∑ i,jointEndpointMap i (u i) ∧∀ i,u i∈oneEffectivePins P i := by
  obtain ⟨u,hu,rfl⟩:=(joint_xspace_mem z).mp hz
  refine ⟨u,joint_cut_endpoint_sum u,?_⟩
  intro i
  apply (one_effective_mem P i _).mpr
  refine ⟨hu i,fun e=>?_⟩
  have hh:=joint_block_squares (hp e) i
  simpa only [jointCutEmbed,joint_matrix_block_diagonal,joint_space_projection] using hh

def oneInner (x : OneUnit p n N) (i : Bool) : Profile p n→ₗ[F]F:=
  (oneFunctional (x (!i))).comp (oneMomentEmbed (x i))

variable {I : Type} [Fintype I]

structure OneScalarRecipe (v : Volley p n I) (w : I→Bool) (t : Tagging p I)
    (m : Mixer p n) (x y : OneUnit p n N)
    (P : Bool→Comp p.g→Space (Ray p n)) : Prop where
  summ (i j : Bool) : ∑ a∈v.shoots w i j,v.diagonalAt a=1
  gradient (i j : Bool) (z : Profile p n) : z∈oneEffectivePins P i→
    grad m (v.sumAt t w i j) z=oneFunctional (y j) (oneMomentEmbed (x i) z)

def oneAttackGrad (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (y : OneUnit p n N) : Prop :=∀ a j,
  grad m (v.sumAt t w.obj (v.obj a) j) (v.atomAt t a)=
    if j=w.obj a then 0 else oneInner y (w.obj a) (w.atomAt t a)

theorem one_attack_value (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (y : OneUnit p n N) (hy : ∀ i,oneFrameLaw m (y i)) (ha : oneAttackGrad v w t m y)
    (a : I) (j : Bool) :
    grad m (v.sumAt t w.obj (v.obj a) j) (v.atomAt t a)=
      oneFunctional (y j) (oneMomentEmbed (y (w.obj a)) (w.atomAt t a)) := by
  rw [ha]
  by_cases hj : j=w.obj a
  · rw [if_pos hj,hj,one_functional_self (hy _)]
  · rw [if_neg hj]
    have he : j=!(w.obj a) := by cases j <;> cases h : w.obj a <;> simp_all
    rw [he]
    rfl

/-- The joint effective obstruction test splits into the two endpoint
scalar recipes. Mixed endpoint kernel relations are still permitted. -/
theorem one_recipe_effective (v : Volley p n I) (w : I→Bool) (t : Tagging p I)
    (m : Mixer p n) (x y : OneUnit p n N) (P : Bool→Comp p.g→Space (Ray p n))
    (hrecipe : OneScalarRecipe v w t m x y P) (M : Bool→JointProfile p n)
    (hgrad : ∀ i j z,jointMatrixFunctional (M j) (jointEndpointMap i z)=grad m (v.sumAt t w i j) z)
    (j : Bool) (z : JointProfile p n) (hz : z∈jointXspace)
    (hp : ∀ e,z e∈quadraticSquares (jointSpace (fun i=>P i e))) :
    jointMatrixFunctional (M j) z=jointMatrixFunctional
      (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j)) z := by
  obtain ⟨u,rfl,hu⟩:=one_joint_effective P z hz hp
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hgrad,one_actual_channel_contract x y i j (u i) ((one_effective_mem P i _).mp (hu i)).1]
  exact hrecipe.gradient i j _ (hu i)

theorem one_recipe_atoms (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (x y : OneUnit p n N) (hv : v.legal t) (hy : ∀ i,oneFrameLaw m (y i))
    (hkeys : oneVolleyKeys v t x=oneVolleyKeys w t y) (hat : oneAttackGrad v w t m y)
    (M : Bool→JointProfile p n)
    (hgrad : ∀ i j z,jointMatrixFunctional (M j) (jointEndpointMap i z)=grad m (v.sumAt t w.obj i j) z)
    (j : Bool) (a : I) :
    jointMatrixFunctional (M j) (jointEndpointMap (v.obj a) (v.atomAt t a))=
      jointMatrixFunctional
        (fun e=>channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j))
        (jointEndpointMap (v.obj a) (v.atomAt t a)) := by
  rw [hgrad,one_actual_channel_contract x y (v.obj a) j (v.atomAt t a) (atom_mem _ (hv a)),
    one_attack_value v w t m y hy hat]
  congr 1
  exact (one_atom_share v w t x y hkeys a).symm

end
end Lax793645Proofs.Simplifications
