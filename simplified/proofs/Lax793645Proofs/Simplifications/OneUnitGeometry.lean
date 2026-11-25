import Lax793645Proofs.Simplifications.OneFrameLaws
import Lax793645Proofs.Simplifications.QuadraticUnitTables
import Lax793645Proofs.Simplifications.JointSelectedChannels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneUnit (p : Shape) (n N : ℕ) := Bool→OneOrient p n N
abbrev OneUnitFull (p : Shape) (n : ℕ) := JointRay p n×UnitChannels p.h

variable {p : Shape} {n N : ℕ}

def oneUnitMap (x : OneUnit p n N) (e : Comp p.g) :
    OneUnitFull p n→ₗ[F]Vec (HyperbolicIdx N) :=
  ∑ i,(x i e).comp
    (((jointProjection i).comp (LinearMap.fst F _ _)).prod
      ((LinearMap.proj i).comp (LinearMap.snd F _ _)))

theorem one_unit_map_apply (x : OneUnit p n N) (e : Comp p.g)
    (a : JointRay p n) (c : UnitChannels p.h) :
    oneUnitMap x e (a,c)=∑ i,x i e (jointProjection i a,c i) := by
  simp only [oneUnitMap,LinearMap.sum_apply]
  rfl

theorem one_unit_map_primal (x : OneUnit p n N) (e : Comp p.g)
    (i : Bool) (a : Ray p n) :
    oneUnitMap x e (jointInjection i a,0)=onePrimal (x i e) a := by
  cases i <;> simp [one_unit_map_apply,joint_projection_injection,onePrimal,quadraticPrimalIn] <;>
    exact map_zero _

theorem one_unit_map_channel (x : OneUnit p n N) (e : Comp p.g)
    (i : Bool) (c : Hyperbolic p.h) :
    oneUnitMap x e (0,Pi.single i c)=x i e (0,c) := by
  cases i <;> simp [one_unit_map_apply] <;> exact map_zero _

def oneUnitActual (x y : OneUnit p n N) (e : Comp p.g) :
    OneUnitFull p n→ₗ[F]OneUnitFull p n→ₗ[F]F :=
  (hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂ (oneUnitMap x e) (oneUnitMap y e)

theorem one_unit_actual_reciprocal (x y : OneUnit p n N) (e : Comp p.g)
    (a b : OneUnitFull p n) : oneUnitActual x y e a b=oneUnitActual y x e b a := by
  change (hyperbolicMatrix N).toQuadraticForm'.polarBilin (oneUnitMap x e a) (oneUnitMap y e b)=
    (hyperbolicMatrix N).toQuadraticForm'.polarBilin (oneUnitMap y e b) (oneUnitMap x e a)
  exact binary_polar_symm _ _ _

theorem joint_endpoint_component (i : Bool) (x : Profile p n) (e : Comp p.g) :
    jointEndpointMap i x e=jointMatrixInjection i (x e) := by
  ext a b
  rcases a with ⟨a,u⟩
  rcases b with ⟨b,v⟩
  cases i <;> cases u <;> cases v <;>
    simp [jointEndpointMap,jointCutMap,jointCutEmbed,LinearMap.single_apply,
      Matrix.blockDiagonal_apply,jointMatrixInjection]

/-- A realized joint channel map computes the opposite endpoint functional
on every genuine cut profile, not merely on its selected atoms. -/
theorem one_unit_channel_contract (x y : OneUnit p n N)
    (M : Comp p.g→JointRay p n→ₗ[F]JointRay p n→ₗ[F]F)
    (D : Comp p.g→LinearMap.BilinForm F (UnitChannels p.h))
    (gA gB : Bool→Comp p.g→JointRay p n→ₗ[F]Hyperbolic p.h)
    (Q : Bool→JointProfile p n)
    (hcross : ∀ e a b,oneUnitActual x y e a b=
      unitQuadraticTable p.h (M e) (D e) (fun j=>gA j e) (fun i=>gB i e) a b)
    (hQ : ∀ j e a,hyperbolicQuadratic p.h (gA j e a)=(Q j e).toQuadraticForm' a)
    (i j : Bool) (v : Profile p n) (hv : v∈Xspace p n) :
    oneFunctional (y j) (oneMomentEmbed (x i) v)=
      jointMatrixFunctional (Q j) (jointEndpointMap i v) := by
  classical
  have he (e : Comp p.g) (a : Ray p n) (c : Hyperbolic p.h) :
      (hyperbolicMatrix N).toQuadraticForm'.polarBilin (onePrimal (x i e) a) (y j e (0,c))=
        (hyperbolicQuadratic p.h).polarBilin (gA j e (jointInjection i a)) c := by
    have hh:=hcross e (jointInjection i a,0) (0,Pi.single j c)
    change (hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (oneUnitMap x e _) (oneUnitMap y e _)=_ at hh
    rw [one_unit_map_primal,one_unit_map_channel,unit_quadratic_table_left] at hh
    exact hh
  have hc (e : Comp p.g) {W : Moment p n}
      (hW : W∈quadraticSquares (⊤ : Space (Ray p n))) :
      quadraticChannelFunctional (hyperbolicMatrix N).toQuadraticForm'
        (oneChannelX (y j e)) (oneChannelY (y j e))
        (quadraticMomentMap (onePrimal (x i e)) W)=
          mpair (Q j e) (jointMatrixInjection i W) := by
    induction hW using Submodule.span_induction with
    | mem W h =>
      obtain ⟨a,_,rfl⟩:=h
      rw [quadratic_moment_outer,joint_matrix_injection_outer,matrix_quadratic_outer]
      have hh:=quadratic_channel_cross_value p.h (hyperbolicMatrix N).toQuadraticForm'
        (onePrimal (x i e)) ((y j e).comp (LinearMap.inr F _ _))
        ((gA j e).comp (jointInjection i)) (he e) a
      exact hh.trans (hQ j e _)
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add,ha,hb]
    | smul c a _ ha => simp only [map_smul,ha]
  change (∑ e,_) = _
  rw [joint_matrix_functional_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [joint_endpoint_component]
  apply hc
  apply moment_square_span
  obtain ⟨w,hw,rfl⟩:=mem_X.mp hv
  exact (Wspace p n).add_mem (Wtag_le _ (hw _)) (Wtag_le _ (hw _))

end
end Lax793645Proofs.Simplifications
