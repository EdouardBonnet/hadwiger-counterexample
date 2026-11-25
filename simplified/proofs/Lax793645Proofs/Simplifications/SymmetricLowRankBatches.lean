import Lax793645Proofs.Simplifications.SymmetricBlockCompletion
import Lax793645Proofs.Simplifications.LowRankBatchWeights

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {N : ℕ}

def symmetricCompletionCost (J : Type) [Fintype J] :=
  (1+2*Fintype.card J)*blockCompletionCost J

/-- The low-rank batch estimate for symmetric Gram characters. The
within-batch hypotheses require only symmetric quadratic phases. -/
theorem symmetric_low_rank_batch_weight (P : J → J → Prop) [DecidableRel P]
    (hP : ∀ u v,P u v → P v u) (M : Avenue I J) (hs : Mᵀ=M)
    (hM : ∀ x y,¬P x.2 y.2 → M x y=0)
    (f : I → Wgt (Rack J N)) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ (A : Mat J J),Aᵀ=A → (∀ u v,¬P u v → A u v=0) → ∀ i ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ| ≤ ε)
    (w : Wgt (KeyCoordinates (I×J) N)) :
    |avg unif (fun x=>phasedBy M x*(∏ i,f i (led i x))*
      w ((rackCoordinates (I×J) N).symm x))| ≤
      ε^Fintype.card I*bp ((N:ℝ)*symmetricCompletionCost J*peak M)*fourierNorm w := by
  obtain ⟨D,R,hDR,hDs,_hRs,hD,hmask,hR⟩:=symmetric_patterned_block_completion P hP M hM hs
  let g i z:=phasedBy (diagonalBlock D i) z*f i z
  let v (x : KeyCoordinates (I×J) N):=wsign (gramPrimitive R x)*w x
  have hg i ξ : |linearFourier (fun z=>g i (rackCoordinates J N z)) ξ| ≤ ε := by
    apply hf (diagonalBlock D i) _ _ i ξ
    · ext u v
      exact congrFun (congrFun hDs (i,u)) (i,v)
    · intro u v huv
      exact (hmask (i,u) (i,v) huv).1
  have he x : phasedBy M x*(∏ i,f i (led i x))*w ((rackCoordinates (I×J) N).symm x)=
      (∏ i,g i (led i x))*v ((rackCoordinates (I×J) N).symm x) := by
    rw [hDR,layer_add,diagonal_gram_product D hD]
    dsimp only [g,v]
    rw [Finset.prod_mul_distrib]
    have hr : wsign (gramPrimitive R ((rackCoordinates (I×J) N).symm x))=phasedBy R x:=rfl
    rw [hr]
    ring
  simp_rw [he]
  refine (rack_product_weight g ε hg v).trans ?_
  have hn : fourierNorm v ≤ bp ((N:ℝ)*symmetricCompletionCost J*peak M)*fourierNorm w := by
    refine (fourier_norm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((low_rank_gram_fourier_norm R).trans (bp_le ?_)) (fourier_norm_nonneg w))
    have hr : (R.rank:ℝ) ≤ (symmetricCompletionCost J:ℝ)*peak M:=by exact_mod_cast hR
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  exact (mul_le_mul_of_nonneg_left hn (pow_nonneg hε _)).trans_eq (mul_assoc _ _ _).symm

end
end Lax793645Proofs.Simplifications
