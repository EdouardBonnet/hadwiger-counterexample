/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.ResponseSolvability.
Changes: replace the flat-extension annihilator decomposition by protected
tensor spaces; remove the selector-degree assumption.
-/
import Lax793645Proofs.Simplifications.AffineCutDecomposition
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ResponseSolvability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Finset Submodule
open scoped BigOperators
noncomputable section

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

/-- Linear realization through protected tensor spaces. In particular, the
selector degree can be one when the two protected independence conditions hold. -/
theorem affine_realize_linear (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Plan p n) (t' B : Cross p n)
    (hb : v.bounded w.obj) (ht : v.legal t)
    (q R : ℕ) (hv : affineAvoids v a q)
    (hr : 2*planRank a+28 ≤ R) (hq : R^2+14 ≤ q)
    (hB : fitsTable a b B t') (hT : tableInj a b t')
    (hf : rowAgree (v.frozen a t) B (actual p x y))
    (hR : v.scalarRecipe w t m x a t') (hk : v.keys t x=w.keys t y)
    (hL : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (j : Bool) :
    ∃ C∈deltaSpace p (v.frozen a t) b j,
    ∃ P∈pureSpace p (v.frozen a t),
      obsPair p (chanInner p (channelOut p B j) (channelOut p B j))+
      obsPair p (chanDeriv p (channelOut p B j) C)+obsPair p P=
        combineF p (v.demand w t m j) := by
  classical
  let G := v.demand w t m j
  let K : OnForms p n := fun i => contract p B i j
  let CC := channelOut p B j
  have h1 (i : I) : G (v.obj i) (v.atomAt t i)=K (v.obj i) (v.atomAt t i) := by
    change grad m (v.sumAt t w.obj (v.obj i) j) _=contract p B _ _ _
    rw [frozen_contract_key v t hf,contract_actual,LinearMap.comp_apply,hS i j,
      v.atom_share w t x y hk]
    by_cases h : j=w.obj i
    · rw [if_pos h,h,ufun_self (hL _)]
    have hh : (!(w.obj i))=j := by cases j <;> cases e : w.obj i <;> simp_all
    rw [if_neg h,innerP,hh]; rfl
  have hg (z : Xpair p n) (h : orth p CC (v.frozen a t) b j z) :
      combineF p (G-K) z=0 := by
    obtain ⟨H,c,z,rfl,ho,hy⟩ := affine_split_orth v hb ht h hv hr hq
    have he (i : Bool) := H.residual_effective t B z ho (fits_inj hB hT) i (hy i)
    rw [map_add,map_sum]
    have h2 : combineF p (G-K) z=0 := by
      rw [combineF_val]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.sub_apply,LinearMap.sub_apply]
      exact sub_eq_zero.mpr ((hR.gradient i j _ (he i)).trans (fits_contract hB i j _ (he i)).symm)
    rw [h2,zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul,Volley.strike,combineF_single,Pi.sub_apply,LinearMap.sub_apply,
      h1 i,sub_self,smul_zero]
  obtain ⟨C,hC,P,hP,h⟩ := solve_by_dual _ hg
  rw [react_obsPair,map_sub] at h
  rw [obsPair_chan]
  refine ⟨C,hC,P,hP,?_⟩
  rw [add_assoc,h,add_sub_cancel]

end
end Lax793645Proofs.Simplifications
