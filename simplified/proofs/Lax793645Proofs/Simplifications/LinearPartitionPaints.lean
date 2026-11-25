import Lax793645Proofs.Simplifications.QueryCoordinateLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CommonPartitionRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {p : Shape} {N : ℕ}

def keyCoordinatesMap (t : Tagging p I) (N : ℕ) :
    Keys (p:=p) t N→ₗ[F] KeyCoordinates (KeySlots p t) N where
  toFun :=(queryCoordinateEquiv t N).symm
  map_add' x y := by funext ⟨u,b,i⟩; cases b <;> rfl
  map_smul' a x := by funext ⟨u,b,i⟩; cases b <;> rfl

def linearPartitionPaint (v : Template p I)
    (L : Keys (p:=p) v.t N→ₗ[F] Vec J) (φ : Wgt (Vec J)) (a : I→Vec J) :
    Template.Paint v N where
  coeff :=φ (∑ i,a i)
  flies i x :=L (Pi.single i x)=a i

/-- A test on linear equations is an exact finite sum of products of
unary cell indicators. The decomposition requires no regularity argument. -/
theorem linear_partition_mural (v : Template p I)
    (L : Keys (p:=p) v.t N→ₗ[F] Vec J) (φ : Wgt (Vec J)) :
    Template.mural v (linearPartitionPaint v L φ)=fun x=>φ (L x) := by
  funext x
  let a (i:I):=L (Pi.single i (x i))
  have he : ∑ i,a i=L x := by
    dsimp only [a]
    rw [←map_sum,Finset.univ_sum_single]
  have hi c : (∀ i,L (Pi.single i (x i))=c i) ↔ a=c:=funext_iff.symm
  unfold Template.mural Template.Paint.cost linearPartitionPaint prodW
  simp_rw [←ind_all,hi]
  rw [Finset.sum_eq_single a]
  · rw [ind_one rfl,mul_one,he]
  · intro c _ hc
    rw [ind_zero (Ne.symm hc),mul_zero]
  · simp

theorem linear_partition_design (v : Template p I)
    (L : Keys (p:=p) v.t N→ₗ[F] Vec J) (φ : Wgt (Vec J)) (hφ : ∀ a,|φ a|≤1) :
    Template.design v (fun x=>φ (L x)) 1 (Fintype.card (I→Vec J)) := by
  let E:=Fintype.equivFin (I→Vec J)
  let f (i:Fin (Fintype.card (I→Vec J))):=linearPartitionPaint v L φ (E.symm i)
  refine ⟨f,?_,fun i=>hφ _⟩
  have he : Template.mural v f=Template.mural v (linearPartitionPaint v L φ) := by
    funext x
    exact Equiv.sum_comp E.symm (fun a=>(linearPartitionPaint v L φ a).cost x)
  rw [he,linear_partition_mural]

theorem linear_key_test_design (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (P : Mat J (Fin N×Bool×KeySlots p v.t)) (φ : Wgt (Vec J)) (hφ : ∀ a,|φ a|≤1) :
    Template.design v (fun x=>φ (P*ᵥ(queryCoordinateEquiv v.t N).symm x)) 1
      (Fintype.card (I→Vec J)) :=
  linear_partition_design v (P.mulVecLin∘ₗkeyCoordinatesMap v.t N) φ hφ

end
end Lax793645Proofs.Simplifications
