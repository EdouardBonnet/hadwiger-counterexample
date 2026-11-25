import Lax793645Proofs.Simplifications.QuadraticRelativeSieve
import Lax793645Proofs.Simplifications.SimultaneousKernelSieve

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R G : Type} [Fintype I] [Fintype R] [Fintype G]
  [DecidableEq I] [DecidableEq R] [DecidableEq G] {N : ℕ}

theorem relative_quadratic_sieve_bound (d : ℕ) (z : Rack I N) :
    |relativeQuadraticSieve R d z| ≤ singleKernelSieveCost R d := by
  have hscaled : 0 ≤ bp (num R-num I)*binaryKernelCount (stackMatrixEquiv N z) ∧
      bp (num R-num I)*binaryKernelCount (stackMatrixEquiv N z) ≤ bp (num R) := by
    refine ⟨mul_nonneg (bp_pos _).le (binary_kernel_count_bounds _).1,?_⟩
    refine (mul_le_mul_of_nonneg_left (binary_kernel_count_bounds _).2 (bp_pos _).le).trans_eq ?_
    rw [←bp_add]
    congr 1
    ring
  exact kernel_sieve_bound d _ _ hscaled.1 hscaled.2

theorem single_sieve_cost_ge_one (d : ℕ) : 1 ≤ singleKernelSieveCost R d :=
  one_le_pow₀ (by linarith [bp_pos (num R)])

variable {K H : G → Type} [∀ i,Fintype (K i)] [∀ i,Fintype (H i)]
  [∀ i,DecidableEq (K i)] [∀ i,DecidableEq (H i)]

def quadraticRelationProduct (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i)) :
    Wgt (∀ i,Rack (K i) N):=prodW (fun i=>unifOn (quadraticRelation (L i) (Q i)))

/-- Simultaneous replacement of the physical-frame kernel tests, with
errors measured in the relation-conditioned product law. -/
theorem quadratic_product_sieve_error
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N)
    (f : Wgt (∀ i,Rack (K i) N)) (hf : ∀ x,|f x| ≤ 1)
    (d : ℕ) (B : ℝ) (hB : 1 ≤ B) (hc : ∀ i,singleKernelSieveCost (H i) d ≤ B) :
    |avg (quadraticRelationProduct L Q) (fun x=>f x*
      ((∏ i,ind ((stackMatrixEquiv N (x i)).mulVecLin.ker=(L i).mulVecLin.ker))-
        (∏ i,relativeQuadraticSieve (H i) d (x i))))| ≤
      B^Fintype.card G*∑ i,16*(d+2)*bp ((num (H i)+2)*d+
        ((d:ℝ)+1)*(4*num (H i)-N)) := by
  let μ i : Wgt (Rack (K i) N):=unifOn (quadraticRelation (L i) (Q i))
  have hμ i : IsLaw (μ i):=quadratic_relation_law (L i) (hL i) (Q i) (hN i)
  apply product_average_error (quadraticRelationProduct L Q) (prodW_law hμ).nz _ _ f hf B hB
  · intro i x
    exact (show |ind _| ≤ (1:ℝ) by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _).trans hB
  · intro i x
    exact (relative_quadratic_sieve_bound (R:=H i) d (x i)).trans (hc i)
  intro i
  change avg (prodW μ) (fun x=>|ind _-relativeQuadraticSieve (H i) d (x i)|) ≤ _
  rw [product_coordinate_average μ hμ i (fun z=>
    |ind ((stackMatrixEquiv N z).mulVecLin.ker=(L i).mulVecLin.ker)-
      relativeQuadraticSieve (H i) d z|)]
  apply l1_from_signed_tests
  intro w hw
  exact quadratic_original_columns_sieve_error (L i) (hL i) (Q i) (hN i) w hw d

theorem quadratic_product_exact_mass
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N) :
    1/(8:ℝ)^Fintype.card G ≤ pr (quadraticRelationProduct (N:=N) L Q)
      (fun x=>∀ i,(stackMatrixEquiv N (x i)).mulVecLin.ker=(L i).mulVecLin.ker) := by
  unfold quadraticRelationProduct
  rw [prodW_pr _ (fun i (z : Rack (K i) N)=>
    (stackMatrixEquiv N z).mulVecLin.ker=(L i).mulVecLin.ker)]
  have h:=Finset.prod_le_prod (s:=Finset.univ) (f:=fun _ : G=>(1:ℝ)/8)
    (fun _ _=>by norm_num) (fun i _=>quadratic_relation_exact_mass (L i) (hL i) (Q i) (hN i))
  simpa only [Finset.prod_const,card_univ,div_pow,one_pow] using h

theorem quadratic_product_conditioned_sieve
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec) (hN : ∀ i,2*num (H i)+2 ≤ N)
    (f : Wgt (∀ i,Rack (K i) N)) (hf : ∀ x,|f x| ≤ 1)
    (d : ℕ) (B : ℝ) (hB : 1 ≤ B) (hc : ∀ i,singleKernelSieveCost (H i) d ≤ B) :
    |avg (onW (quadraticRelationProduct L Q)
      (fun x=>∀ i,(stackMatrixEquiv N (x i)).mulVecLin.ker=(L i).mulVecLin.ker)) f| ≤
      (8:ℝ)^Fintype.card G*
        (|avg (quadraticRelationProduct L Q) (fun x=>f x*∏ i,relativeQuadraticSieve (H i) d (x i))|+
          B^Fintype.card G*∑ i,16*(d+2)*bp ((num (H i)+2)*d+
            ((d:ℝ)+1)*(4*num (H i)-N))) := by
  apply conditioned_sieve_bound _ _ _ _ _ _ (pow_pos (by norm_num) _)
    (quadratic_product_exact_mass L Q hL hN)
  simpa only [ind_all] using quadratic_product_sieve_error L Q hL hN f hf d B hB hc

end
end Lax793645Proofs.Simplifications
