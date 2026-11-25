import Lax793645Proofs.Simplifications.HighRankBatchWeights
import Lax793645Proofs.Simplifications.BlockRankCompletion

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {N : ℕ}

def diagonalBlock (M : Avenue I J) (i : I) : Mat J J := M.submatrix (fun j=>(i,j)) (fun j=>(i,j))

omit [DecidableEq J] in
/-- A block-diagonal Gram phase factors over the original query batches. -/
theorem diagonal_gram_product (M : Avenue I J)
    (hM : ∀ x y,x.1≠y.1→M x y=0) (x : Rack (I×J) N) :
    phasedBy M x=∏ i:I,phasedBy (diagonalBlock M i) (led i x) := by
  unfold phasedBy
  simp only [layer_form]
  change wsign (∑ a:I×J,∑ b:I×J,M a b*(x.1ᵀ*x.2) a b)=_
  simp only [Fintype.sum_prod_type]
  have he i u : (∑ j:I,∑ v:J,M (i,u) (j,v)*(x.1ᵀ*x.2) (i,u) (j,v))=
      ∑ v:J,M (i,u) (i,v)*(x.1ᵀ*x.2) (i,u) (i,v) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      simp only [hM (i,u) (j,_) hj.symm,zero_mul,Finset.sum_const_zero]
    · simp
  simp_rw [he]
  rw [wsign_sum]
  apply Finset.prod_congr rfl
  intro i _
  rfl

def blockCompletionCost (J : Type) [Fintype J] :=
  Fintype.card J*(1+4*Fintype.card J)

/-- A Fourier-small batch under every permitted within-batch phase remains
small under an arbitrary permitted Gram pattern, paying only its cross rank. -/
theorem low_rank_batch_weight (P : J→J→Prop) [DecidableRel P]
    (M : Avenue I J) (hM : ∀ x y,¬P x.2 y.2→M x y=0)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε)
    (hf : ∀ (A : Mat J J),(∀ u v,¬P u v→A u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (w : Wgt (KeyCoordinates (I×J) N)) :
    |avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*
      w ((rackCoordinates (I×J) N).symm x))|≤
      ε^Fintype.card I*bp ((N:ℝ)*blockCompletionCost J*peak M)*fourierNorm w := by
  obtain ⟨D,R,hDR,hD,hP,hR⟩ := patterned_block_rank_completion P M hM
  let g i z := phasedBy (diagonalBlock D i) z*f i z
  let v (x : KeyCoordinates (I×J) N) := wsign (gramPrimitive R x)*w x
  have hg i ξ : |linearFourier (fun z=>g i (rackCoordinates J N z)) ξ|≤ε := by
    apply hf (diagonalBlock D i) _ i ξ
    intro u v huv
    exact (hP (i,u) (i,v) huv).1
  have he x : phasedBy M x*(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)=
      (∏ i,g i (led i x))*v ((rackCoordinates (I×J) N).symm x) := by
    rw [hDR,layer_add,diagonal_gram_product D hD]
    dsimp only [g,v]
    rw [Finset.prod_mul_distrib]
    have hr : wsign (gramPrimitive R ((rackCoordinates (I×J) N).symm x))=phasedBy R x := rfl
    rw [hr]
    ring
  simp_rw [he]
  refine (rack_product_weight g ε hg v).trans ?_
  have hn : fourierNorm v≤bp ((N:ℝ)*blockCompletionCost J*peak M)*fourierNorm w := by
    refine (fourier_norm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((low_rank_gram_fourier_norm R).trans (bp_le ?_)) (fourier_norm_nonneg w))
    have hr : (R.rank:ℝ)≤(blockCompletionCost J:ℝ)*peak M := by exact_mod_cast hR
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N : (0:ℝ)≤N)]
  exact (mul_le_mul_of_nonneg_left hn (pow_nonneg hε _)).trans_eq (mul_assoc _ _ _).symm

end
end Lax793645Proofs.Simplifications
