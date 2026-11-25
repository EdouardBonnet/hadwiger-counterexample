import Lax793645Proofs.Simplifications.QuadraticGramCodes
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

theorem ordered_gram_quarter (N : ℕ) (G : Mat I I) (hN : 2*num I+2≤N) :
    unif G/4≤pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (gramGood G) := by
  have hsize : num I+num I≤num (Fin N) := by
    simp only [num,Fintype.card_fin] at *
    linarith
  have hg:=(gram_norm (U:=Fin N) G hsize).2
  have hs : bp (num I-num (Fin N))≤(1/2:ℝ) := by
    calc
      _≤bp (-1):=bp_le (by simp only [num,Fintype.card_fin] at *; have hz:=Nat.cast_nonneg (α:=ℝ) (Fintype.card I); linarith)
      _=_:=by norm_num [bp]
  have ht : bp (num I+num I-num (Fin N))≤(1/2:ℝ) := by
    calc
      _≤bp (-1):=bp_le (by simp only [num,Fintype.card_fin] at *; linarith)
      _=_:=by norm_num [bp]
  have hu : unif G=bp (-num I*num I) := by
    rw [unif_apply,card_space,dim_mat,←bp_neg]
    congr 1
    push_cast
    unfold num
    ring
  rw [hu]
  apply le_trans ?_ hg
  have hp : (1/2:ℝ)*(1/2)≤(1-bp (num I-num (Fin N)))*(1-bp (num I+num I-num (Fin N))):=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hp (bp_pos (-num I*num I)).le]

/-- Sharp normalization for quadratic Gram frames. Ordered Gram fibers
with the same quadratic code are summed before estimating their mass.
This avoids an exponential loss in the square of the query length. -/
theorem quadratic_gram_code_lower (N : ℕ)
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))] (M : Mat I I)
    (hN : 2*num I+2≤N) :
    unif (quadraticGramCode M)/4≤pr unif (quadraticGramGood
      (hyperbolicMatrix N).toQuadraticForm' M.toQuadraticForm') := by
  classical
  let U:=Mat (Fin N) I×Mat (Fin N) I
  let μ : Wgt U:=pairW unif unif
  let P (x : U):=Injective x.1.mulVec ∧Injective x.2.mulVec
  let v:=subW μ P
  let G (x : U):=x.1ᵀ*x.2
  have he (B : Mat I I) : mapW v G B=pr μ (gramGood B) := by
    change pr (subW μ P) (fun x=>G x=B)=_
    rw [pr_sub]
    congr 1
    funext x
    apply propext
    simp only [P,G,gramGood,and_comm,and_left_comm,and_assoc]
  have hc (B : Mat I I) : unif B≤4*mapW v G B := by
    rw [he]
    have hh:=ordered_gram_quarter N B hN
    linarith only [hh]
  have hf:=mapW_cap hc quadraticGramCode (quadraticGramCode M)
  rw [quadratic_gram_code_uniform,mapW_nested] at hf
  have hbound : mapW v (quadraticGramCode∘G) (quadraticGramCode M)≤
      pr unif (quadraticGramGood (hyperbolicMatrix N).toQuadraticForm' M.toQuadraticForm') := by
    change pr (subW μ P) (fun x=>quadraticGramCode (G x)=quadraticGramCode M)≤_
    rw [pr_sub,←probability_equiv (stackFrameEquiv (I:=I) N),pair_unif]
    refine pr_mono (pairW_law unif_law unif_law).nz ?_
    rintro x ⟨hp,hg⟩
    have hh:=paired_gram_quadratic N (G x) x ⟨rfl,hp⟩
    exact ⟨hh.1,hh.2.trans ((quadratic_gram_code_eq (G x) M).mp hg)⟩
  linarith only [hf,hbound]

theorem quadratic_gram_sharp_lower (N : ℕ)
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))] (M : Mat I I)
    (hN : 2*num I+2≤N) :
    bp (-(dim (QuadraticGramCode I):ℝ)-2)≤pr unif (quadraticGramGood
      (hyperbolicMatrix N).toQuadraticForm' M.toQuadraticForm') := by
  have hh:=quadratic_gram_code_lower N M hN
  rw [unif_apply,card_space,←bp_neg] at hh
  have he : bp (-(dim (QuadraticGramCode I):ℝ)-2)=bp (-(dim (QuadraticGramCode I):ℝ))/4 := by
    rw [bp_sub]
    norm_num [bp]
  rwa [he]

end
end Lax793645Proofs.Simplifications
