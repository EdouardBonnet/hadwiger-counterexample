import Lax793645Proofs.Simplifications.OneUnitGeometry
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RealizationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

abbrev OneKeys (t : Tagging p I) (N : ℕ) := ∀ a,TagStar (t a)→Vec (HyperbolicIdx N)

def oneVolleyKeys (v : Volley p n I) (t : Tagging p I) (x : OneUnit p n N) : OneKeys t N :=
  fun a e=>onePrimal (x (v.obj a) e.val) (v.rayAt a)

theorem one_atom_share (v w : Volley p n I) (t : Tagging p I) (x y : OneUnit p n N)
    (hk : oneVolleyKeys v t x=oneVolleyKeys w t y) (a : I) :
    oneMomentEmbed (x (v.obj a)) (v.atomAt t a)=oneMomentEmbed (y (w.obj a)) (w.atomAt t a) := by
  classical
  funext e
  change quadraticMomentMap _ (atom p _ _ _ e)=quadraticMomentMap _ (atom p _ _ _ e)
  by_cases hs : inc e (t a)
  · simp only [atom_def,hs,ite_true,mom,quadratic_moment_outer]
    exact congrArg (fun v=>vecMulVec v v) (congrFun (congrFun hk a) ⟨e,hs⟩)
  · simp only [atom_def,hs,ite_false,map_zero]

theorem one_sum_share (v w : Volley p n I) (t : Tagging p I) (x y : OneUnit p n N)
    (hk : oneVolleyKeys v t x=oneVolleyKeys w t y) (i j : Bool) :
    oneMomentEmbed (x i) (v.sumAt t w.obj i j)=oneMomentEmbed (y j) (w.sumAt t v.obj j i) := by
  classical
  unfold Volley.sumAt
  rw [map_sum,map_sum,←Volley.shoots_swap v w]
  apply Finset.sum_congr rfl
  intro a ha
  have hi:=(Finset.mem_filter.mp ha).2
  rw [←hi.1,←hi.2]
  exact one_atom_share v w t x y hk a

/-- A matching single-vector key and realized quadratic channel demands
give the same four-hole conflict used by the graph-transfer theorem. -/
theorem one_unit_realized_conflicts (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (x y : OneUnit p n N) (hv : v.legal t) (hw : w.legal t)
    (hx : ∀ i,oneFrameLaw m (x i)) (hy : ∀ j,oneFrameLaw m (y j))
    (hk : oneVolleyKeys v t x=oneVolleyKeys w t y) (hrole : v.roleMatch w t)
    (M : Comp p.g→JointRay p n→ₗ[F]JointRay p n→ₗ[F]F)
    (D : Comp p.g→LinearMap.BilinForm F (UnitChannels p.h))
    (gA gB : Bool→Comp p.g→JointRay p n→ₗ[F]Hyperbolic p.h)
    (QA QB : Bool→JointProfile p n)
    (hcross : ∀ e a b,oneUnitActual x y e a b=
      unitQuadraticTable p.h (M e) (D e) (fun j=>gA j e) (fun i=>gB i e) a b)
    (hQA : ∀ j e a,hyperbolicQuadratic p.h (gA j e a)=(QA j e).toQuadraticForm' a)
    (hQB : ∀ i e b,hyperbolicQuadratic p.h (gB i e b)=(QB i e).toQuadraticForm' b)
    (hA : ∀ i j,∀ z∈Xspace p n,jointMatrixFunctional (QA j) (jointEndpointMap i z)=
      grad m (v.sumAt t w.obj i j) z)
    (hB : ∀ j i,∀ z∈Xspace p n,jointMatrixFunctional (QB i) (jointEndpointMap j z)=
      grad m (w.sumAt t v.obj j i) z) :
    (oneRawHoles m).conflict (x true,x false) (y true,y false) := by
  have hcross' (e : Comp p.g) (a b : OneUnitFull p n) :
      oneUnitActual y x e a b=unitQuadraticTable p.h (M e).flip (D e).flip
        (fun i=>gB i e) (fun j=>gA j e) a b := by
    rw [one_unit_actual_reciprocal,hcross,unit_quadratic_table_reciprocal]
  have hh (i j : Bool) : oneHole m (x i) (y j) := by
    refine ⟨hx i,hy j,v.sumAt t w.obj i j,w.sumAt t v.obj j i,
      v.sum_mem hv ..,w.sum_mem hw ..,one_sum_share v w t x y hk i j,?_,?_,hrole i j⟩
    · intro z hz
      exact (one_unit_channel_contract x y M D gA gB QA hcross hQA i j z hz).trans (hA i j z hz)
    · intro z hz
      exact (one_unit_channel_contract y x (fun e=>(M e).flip) (fun e=>(D e).flip)
        gB gA QB hcross' hQB j i z hz).trans (hB j i z hz)
  exact ⟨hh true true,hh true false,hh false true,hh false false⟩

end
end Lax793645Proofs.Simplifications
