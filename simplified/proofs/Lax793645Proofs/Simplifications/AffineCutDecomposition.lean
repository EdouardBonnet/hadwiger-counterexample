import Lax793645Proofs.Simplifications.AffineMomentIsolation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap Finset
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace RaySeparation
variable {v : Volley p n I} {a : Plan p n} (H : RaySeparation v a)

theorem read_moment (i : Bool) (j k : CallsAt v i) :
    matrixRead (H.read i) j (mom p (v.sel k.val) (v.par k.val)) =
      if k=j then 1 else 0 := by
  classical
  change matrixRead (H.read i) j (vecMulVec (v.rayAt k.val) (v.rayAt k.val))=_
  rw [matrixRead_outer,H.onKeys]
  by_cases h : k=j
  · subst k; simp
  simp [Pi.single_eq_of_ne (Ne.symm h),h]

theorem read_decomposition (i : Bool) (M z : Moment p n) (c : CallsAt v i → F)
    (hz : M=(∑ k : CallsAt v i,c k • mom p (v.sel k.val) (v.par k.val))+z)
    (hcol : colSp z ≤ H.space i) (j : CallsAt v i) :
    matrixRead (H.read i) j M=c j := by
  classical
  rw [hz,map_add,matrixRead_zero _ _ _ (H.vanishes i) z hcol,add_zero,map_sum]
  simp_rw [map_smul,H.read_moment]
  simp

end RaySeparation

/-- The cut annihilator splits into genuine selected atoms and a remainder
whose columns stay in the common protected spaces. No flat extension,
selector interpolation, or rank bound on the remainder is used. -/
theorem affine_split_orth (v : Volley p n I) {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {other : I → Bool} {mode : Bool}
    {q R : ℕ} (hb : v.bounded other) (ht : v.legal t)
    (ho : orth p C (v.frozen a t) b mode x) (hv : affineAvoids v a q)
    (hr : 2*planRank a+28 ≤ R) (hq : R^2+14 ≤ q) :
    ∃ (H : RaySeparation v a) (c : I → F) (y : Xpair p n),
      x=y+∑ j,c j • v.strike t ht j ∧
      orth p C (v.frozen a t) b mode y ∧
      ∀ i e,colSp ((y i).val e) ≤ H.space i := by
  classical
  obtain ⟨H,hH⟩ := affine_component_isolation v t a b C mode x other hb R q hr hq hv ho
  choose cc z hz hcol using hH
  have hconst (j : I) : ∃ c : F, ∀ e,
      matrixRead (H.read (v.obj j)) ⟨j,by simp [Volley.here]⟩ ((x (v.obj j)).val e)=
        if inc e (t j) then c else 0 :=
    linear_star_constant (x (v.obj j)).property (t j) _
      (fun e he => H.component_read_off_star t ho (v.obj j) _ e he)
  choose c hc using hconst
  let A := ∑ j,c j • v.strike t ht j
  refine ⟨H,c,x-A,(sub_add_cancel x A).symm,
    orth_sub ho (orth_sum _ _ (v.strike_orth t ht)),fun i e => ?_⟩
  have hcoef (j : CallsAt v i) : cc i e j=if inc e (t j.val) then c j.val else 0 := by
    rcases j with ⟨j,hj⟩
    have he : v.obj j=i := (Finset.mem_filter.mp hj).2
    subst i
    exact (H.read_decomposition _ _ _ _ (hz _ e) (hcol _ e) ⟨j,hj⟩).symm.trans (hc j e)
  have hA : (A i).val e=∑ j : CallsAt v i,cc i e j • mom p (v.sel j.val) (v.par j.val) := by
    rw [show (A i).val=_ from v.strike_here t ht c i,Finset.sum_apply]
    rw [←Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j hj
    change c j.val • v.atomAt t j.val e=_
    rw [hcoef,Volley.atomAt,atom_def]
    by_cases he : inc e (t j.val)
    · rw [if_pos he,if_pos he]
    rw [if_neg he,if_neg he,smul_zero,zero_smul]
  have hy : ((x-A) i).val e=z i e := by
    change (x i).val e-(A i).val e=z i e
    rw [hz,hA,add_sub_cancel_left]
  rw [hy]
  exact hcol i e

end
end Lax793645Proofs.Simplifications
