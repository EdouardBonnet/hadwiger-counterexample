import Lax793645Proofs.Simplifications.QuadraticProtectedCuts
import Lax793645Proofs.Simplifications.JointBlockKernel

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev JointRay (p : Shape) (n : ℕ) := Vec (Row p n×Bool)
abbrev JointMoment (p : Shape) (n : ℕ) := Mat (Row p n×Bool) (Row p n×Bool)
abbrev JointProfile (p : Shape) (n : ℕ) := Comp p.g→JointMoment p n

def jointCutEmbed {p : Shape} {n : ℕ} (x : Bool→Profile p n) : JointProfile p n :=
  fun e=>blockDiagonal (fun i=>x i e)

variable {p : Shape} {n : ℕ} {I : Bool→Type}
  [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

/-- Simultaneous annihilator decomposition for both endpoints. Mixed
kernel relations, including shared pinned ambient vectors, are allowed.
Only a kernel vector supported on one endpoint's pins must vanish. -/
theorem joint_quadratic_cut_annihilator
    (l : ∀ i,I i→Tag p.g) (s : ∀ i,I i→Label p.b) (z : ∀ i,I i→Base p.g n)
    (hz : ∀ i j,allows (l i j) (z i j))
    (U : Bool→Space (Vec (SelIdx p.b p.j))) (V : Bool→Space (Vec (AIdx p.g n)))
    (hs : ∀ i,LinearIndependent F ((U i).mkQ∘fun j=>selV p.j (s i j)))
    (ht : ∀ i,LinearIndependent F ((V i).mkQ∘fun j=>baseV (z i j)))
    (P : Bool→Comp p.g→Space (Ray p n)) (K : Comp p.g→Space (JointRay p n))
    (hPL : ∀ i e,P i e≤tensorCross (U i) (V i))
    (hK : ∀ e,K e≤jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))
    (hKP : ∀ e i,Disjoint (K e) ((P i e).map (jointInjection i)))
    (R : ℕ)
    (hR : ∀ e,2*dim (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))≤R)
    (hP : ∀ i e,∀ v∈P i e,Matrix.rank (flattenMatrix.symm v)≤R^2+Fintype.card (I i)→
      v∈tensorRectangle (U i) (V i))
    (x : Bool→Profile p n) (hx : ∀ i,x i∈Xspace p n)
    (hquad : ∀ e,jointCutEmbed x e∈
      quadraticSquares (jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e))⊔
      quadraticCross (K e)) :
    ∃ (c : ∀ i,I i→F) (y : Bool→Profile p n),
      (∀ i,x i=(∑ j,c i j•atom p (l i j) (s i j) (z i j))+y i) ∧
      (∀ i,y i∈Xspace p n) ∧
      (∀ e,jointCutEmbed y e∈quadraticSquares (jointSpace (fun i=>P i e))) ∧
      ∀ i e,y i e∈quadraticSquares (P i e) := by
  classical
  let F₀ (e : Comp p.g):=jointSpace (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)
  let L:=jointSpace (fun i=>tensorCross (U i) (V i))
  let K' (i : Bool) (e : Comp p.g):=(K e).map (jointProjection i)
  have hK' (i : Bool) (e : Comp p.g) : K' i e≤P i e⊔selectedAtComponent (l i) (s i) (z i) e := by
    have hh:=Submodule.map_mono (f:=jointProjection i) (hK e)
    rwa [joint_space_projection] at hh
  have hquad' (i : Bool) : x i∈quadraticCutConstraints
      (fun e=>P i e⊔selectedAtComponent (l i) (s i) (z i) e) (K' i) := by
    rw [quadratic_cut_constraints_mem]
    intro e
    simpa only [jointCutEmbed,joint_matrix_block_diagonal] using
      joint_constraints_project _ _ (hquad e) i
  have hr (i : Bool) (e : Comp p.g) : (x i e).rank≤R := by
    have hh:=(joint_matrix_block_rank (jointCutEmbed x e) i).trans
      ((quadratic_annihilator_rank (F₀ e) (K e) (hK e) (hquad e)).trans (hR e))
    simpa only [jointCutEmbed,joint_matrix_block_diagonal] using hh
  have hsplit (i : Bool) := quadratic_cut_protected_residual (l i) (s i) (z i) (hz i)
    (U i) (V i) (hs i) (ht i) (P i) (K' i) (hPL i) (hK' i) R (hP i)
    (x i) (hx i) (hr i) (hquad' i)
  choose c y hxy hy hyl using hsplit
  let a (i : Bool) : Profile p n:=∑ j,c i j•atom p (l i j) (s i j) (z i j)
  have ha (i : Bool) (e : Comp p.g) : a i e∈quadraticSquares
      (P i e⊔selectedAtComponent (l i) (s i) (z i) e) := by
    simp only [a,Finset.sum_apply,Pi.smul_apply]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [atom_def]
    by_cases he : inc e (l i j)
    · rw [if_pos he]
      exact Submodule.subset_span ⟨point p (s i j) (z i j),Submodule.mem_sup_right
        (Submodule.subset_span ⟨j,he,rfl⟩),rfl⟩
    · simp [he]
  have hay (e : Comp p.g) : jointCutEmbed y e=jointCutEmbed x e-jointCutEmbed a e := by
    unfold jointCutEmbed
    rw [←Matrix.blockDiagonal_sub]
    congr 1
    funext i
    have hh:=congrFun (hxy i) e
    change x i e=a i e+y i e at hh
    change y i e=x i e-a i e
    rw [hh,add_sub_cancel_left]
  have hFi (e : Comp p.g) (i : Bool) :
      (P i e⊔selectedAtComponent (l i) (s i) (z i) e)⊓tensorCross (U i) (V i)=P i e := by
    exact pin_selected_inf (hPL i e)
      ((selected_tensor_disjoint_cross (U i) (V i) _ _ (hs i) (ht i)).mono_left
        (selected_at_component_le (l i) (s i) (z i) e))
  have hyq (e : Comp p.g) : jointCutEmbed y e∈quadraticSquares (jointSpace (fun i=>P i e)) := by
    have hmem : jointCutEmbed y e∈quadraticSquares (F₀ e)⊔quadraticCross (K e) := by
      rw [hay]
      exact Submodule.sub_mem _ (hquad e) (Submodule.mem_sup_left
        (joint_diagonal_squares _ _ (fun i=>ha i e)))
    have hh:=joint_block_kernel_residual
      (fun i=>P i e⊔selectedAtComponent (l i) (s i) (z i) e)
      (fun i=>tensorCross (U i) (V i)) (K e) (hK e)
      (fun i=>by rw [hFi e i]; exact hKP e i) (fun i=>y i e) hmem (fun i=>hyl i e)
    simpa only [jointCutEmbed,hFi] using hh
  refine ⟨c,y,hxy,hy,hyq,?_⟩
  intro i e
  simpa only [jointCutEmbed,joint_matrix_block_diagonal,joint_space_projection] using
    joint_block_squares (hyq e) i

end
end Lax793645Proofs.Simplifications
