import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PointAtomVanishing
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PrimalChannelDecomposition

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function Finset Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Substitution of affine coordinates preserves the expected quadratic
degree, including on an affine fiber of a linear key partition. -/
theorem affine_quadratic_stocks (M : Mat J J) (P : Mat J I) (k : Vec J) :
    (fun x=>evmat M (P *ᵥ x+k) (P *ᵥ x+k))∈Stocks I 2 := by
  classical
  have hc (j : J) : (fun x=>(P *ᵥ x+k) j)∈Stocks I 1 := by
    have hh : (fun x=>(P *ᵥ x) j)∈Stocks I 1 := by
      have he : (fun x : Vec I=>(P *ᵥ x) j)=∑ i : I,P j i • (fun x=>x i) := by
        funext x
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
      rw [he]
      exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (stock_var i)
    exact Submodule.add_mem _ hh (stocks_one I 1 (k j))
  have hh:=pointPoly (mpair M) (fun x=>P *ᵥ x+k) 1 hc
  simpa only [mpair_outer] using hh

theorem polarize_unique {f : Vec I→F} {A B : Mat I I}
    (hA : polarize f A) (hB : polarize f B) : A=B := by
  apply Matrix.ext
  intro i j
  have h:=hA (Pi.single j 1) (Pi.single i 1)
  rw [hB (Pi.single j 1) (Pi.single i 1)] at h
  simpa only [add_right_inj,single_dotProduct,Matrix.mulVec_single,
    one_mul,mul_one,op_smul_eq_smul,one_smul,col_apply] using h.symm

omit [DecidableEq I] in
theorem polarize_add {f g : Vec I→F} {A B : Mat I I}
    (hf : polarize f A) (hg : polarize g B) : polarize (f+g) (A+B) := by
  intro x y
  simp only [Pi.add_apply,Matrix.add_mulVec,dotProduct_add]
  rw [show f (x+y)+g (x+y)+(f x+g x)=
      (f (x+y)+f x)+(g (x+y)+g x) by ring,hf,hg]
  ring

omit [DecidableEq I] in
theorem constant_polarize (a : F) : polarize (fun _ : Vec I=>a) 0 := by
  intro x y
  simp

/-- A tester with larger polar rank cannot be canceled by the quadratic
form of a bounded-rank matrix, after any affine change of variables.
The error bound is uniform in the fiber and its affine offset. -/
theorem tester_affine_disagreement (q : Vec I→F) (Q : Mat I I)
    (hq : q∈Stocks I 2) (hQ : polarize q Q)
    (M : Mat J J) (P : Mat J I) (k : Vec J) (a : F)
    (hr : 2*M.rank<Q.rank) :
    (1/4:ℝ)≤pr unif (fun x=>q x+evmat M (P *ᵥ x+k) (P *ᵥ x+k)+a≠0) := by
  classical
  let R:=fun x=>evmat M (P *ᵥ x+k) (P *ᵥ x+k)
  let B:=pullM P P (M+Mᵀ)
  have hR : polarize R B := by
    simpa only [zero_dotProduct,zero_add] using flare_affine M P k 0 (0 : Vec I)
  have hB : B.rank≤2*M.rank := by
    change (liftM Pᵀ Pᵀ (M+Mᵀ)).rank≤2*M.rank
    exact (rank_lift_le Pᵀ Pᵀ (M+Mᵀ)).trans
      ((mrk_add_le M Mᵀ).trans_eq (by rw [Matrix.rank_transpose]; omega))
  have he : ∃ x,q x+R x+a≠0 := by
    by_contra! hz
    have hh : q+R+(fun _=>a)=(fun _=>0) := funext hz
    have hp:=polarize_add (polarize_add hQ hR) (constant_polarize (I:=I) a)
    rw [hh,add_zero] at hp
    have hb:=polarize_unique hp (constant_polarize (I:=I) 0)
    have hQB : Q=B := by
      have : Q+B+B=0+B:=congrArg (·+B) hb
      simpa only [add_assoc,char_two,add_zero,zero_add] using this
    exact (not_lt_of_ge (hQB ▸ hB)) hr
  have hs : q+R+(fun _=>a)∈Stocks I 2 :=
    Submodule.add_mem _ (Submodule.add_mem _ hq (affine_quadratic_stocks M P k))
      (stocks_one I 2 a)
  have hh:=stocks_bound I 2 _ hs he
  norm_num [bp] at hh
  exact hh

end
end Lax793645Proofs.Simplifications
