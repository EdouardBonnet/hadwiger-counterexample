import Lax793645Proofs.Simplifications.AffinePinProtection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GroupedQueryIndependence

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

variable {I U V : Type} [Fintype I] [Fintype U] [Fintype V]
variable [DecidableEq I] [DecidableEq U] [DecidableEq V]

theorem uniform_quotient_failure (T : Space (Vec U)) :
    pr (unif : Wgt (Mat U I)) (fun M => ¬LinearIndependent F (T.mkQ ∘ M.col)) ≤
      bp (num I+(dim T:ℝ)-num U) := by
  classical
  let P (c : Vec I) (M : Mat U I) := c≠0 ∧ M*ᵥ c ∈ T
  have hsub : pr (unif : Wgt (Mat U I))
      (fun M => ¬LinearIndependent F (T.mkQ ∘ M.col)) ≤
      ∑ c : Vec I,pr unif (P c) := by
    apply (pr_mono unif_law.nz ?_).trans (pr_exists_le unif_law.nz P)
    intro M hM
    rw [Fintype.linearIndependent_iff] at hM
    push Not at hM
    obtain ⟨c,hc,i,hi⟩ := hM
    refine ⟨c,(fun he => hi (congrFun he i)),?_⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change T.mkQ (M*ᵥ c)=0
    have he : M*ᵥ c=∑ j,c j • M.col j := by
      ext u
      simp [Matrix.mulVec,dotProduct,mul_comm]
    rw [he,map_sum]
    simpa only [map_smul,Function.comp_apply] using hc
  have hp (c : Vec I) : pr (unif : Wgt (Mat U I)) (P c) ≤ bp ((dim T:ℝ)-num U) := by
    by_cases hc : c=0
    · simp only [P,hc,ne_eq,not_true,false_and,pr_false]
      exact (bp_pos _).le
    have hle : pr (unif : Wgt (Mat U I)) (P c) ≤
        ∑ y : T,pr unif (fun M : Mat U I => M*ᵥ c=y.val) := by
      apply (pr_mono unif_law.nz ?_).trans (pr_exists_le unif_law.nz _)
      intro M hM
      exact ⟨⟨_,hM.2⟩,rfl⟩
    have hpoint (y : T) : pr (unif : Wgt (Mat U I)) (fun M => M*ᵥ c=y.val) ≤ bp (-num U) := by
      have h := shift_pmax (unif_law (α:=Mat U I)).sub ⊤ (fun _ _ _ => rfl) hc y.val
      simpa only [dim,finrank_top,dim_vec,num] using h
    refine hle.trans ((Finset.sum_le_sum (fun y _ => hpoint y)).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,←bp_add]
    congr 1
  refine hsub.trans ((Finset.sum_le_sum (fun c _ => hp c)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,dim_vec,←bp_add,num]
  congr 1
  ring

theorem independent_mod_of_projection (P : Vec U →ₗ[F] Vec V)
    (T : Space (Vec U)) (v : I → Vec U)
    (h : LinearIndependent F ((T.map P).mkQ ∘ P ∘ v)) :
    LinearIndependent F (T.mkQ ∘ v) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  apply (Fintype.linearIndependent_iff.mp h) c ?_ i
  have hm : (∑ j,c j • v j) ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change T.mkQ (∑ j,c j • v j)=0
    simpa only [map_sum,map_smul,Function.comp_apply] using hc
  have he : (T.map P).mkQ (P (∑ j,c j • v j))=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,hm,rfl⟩
  simpa only [map_sum,map_smul,Function.comp_apply] using he

variable {p : Shape} {n : ℕ}

def baseFreeProjection : Vec (AIdx p.g n) →ₗ[F] Vec (Fin n) where
  toFun x j := x (some (Block.Z,j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem template_base_free (v : Template p I) (x : Inputs p n I) (i : I) :
    baseFreeProjection (baseV ((v.draw x).par i))=freePart p (x i) := by
  ext j
  exact if_pos (Flavor.keepZ _ _)

def templateFreeMatrix (x : Inputs p n I) : Mat (Fin n) I :=
  fun j i => freePart p (x i) j

theorem template_free_law (v : Template p I) (q : I → F)
    (hq : ∀ i,IsLaw (scopedBit p n (v.t i) (v.f i) (q i))) :
    mapW (v.state q n) templateFreeMatrix=unif := by
  classical
  let E : (I → Vec (Fin n)) ≃ Mat (Fin n) I :=
    ⟨fun x j i => x i j,fun x i j => x j i,fun _ => rfl,fun _ => rfl⟩
  have h := mapW_repeat (fun i => scopedBit p n (v.t i) (v.f i) (q i))
    (fun _ => freePart p)
  simp_rw [scopedZ_bit p n _ _ _ (hq _)] at h
  have he : mapW (v.state q n) (fun x i => freePart p (x i))=unif :=
    h.trans (Eq.symm draws_unif)
  change mapW _ (E ∘ (fun (x : Inputs p n I) i => freePart p (x i)))=_
  rw [←mapW_nested,he,unif_equiv]

/-- Uniform rejection bound for the actual query-input law. It holds before
any orientation or status acceptance and therefore pays no leaf density cap. -/
theorem template_base_rejection (v : Template p I) (q : I → F)
    (hq : ∀ i,IsLaw (scopedBit p n (v.t i) (v.f i) (q i)))
    (T : Space (Vec (AIdx p.g n))) :
    pr (v.state q n) (fun x => ¬LinearIndependent F
      (T.mkQ ∘ (fun i => baseV ((v.draw x).par i)))) ≤
      bp (num I+(dim T:ℝ)-(n:ℝ)) := by
  classical
  let P : Vec (AIdx p.g n) →ₗ[F] Vec (Fin n) := baseFreeProjection
  let S := T.map P
  have hsub : pr (v.state q n) (fun x => ¬LinearIndependent F
      (T.mkQ ∘ (fun i => baseV ((v.draw x).par i)))) ≤
      pr (v.state q n) (fun x => ¬LinearIndependent F (S.mkQ ∘ (templateFreeMatrix x).col)) := by
    apply pr_mono (prodW_law hq).nz
    intro x hx hh
    apply hx
    apply independent_mod_of_projection P T _
    have he : (P ∘ fun i => baseV ((v.draw x).par i))=(templateFreeMatrix x).col := by
      funext i
      exact template_base_free v x i
    simpa only [←Function.comp_assoc,he] using hh
  rw [←mapW_pr (v.state q n) (templateFreeMatrix (p:=p) (n:=n))
    (fun M : Mat (Fin n) I => ¬LinearIndependent F (S.mkQ ∘ M.col)),
    template_free_law v q hq] at hsub
  refine hsub.trans ((uniform_quotient_failure S).trans (bp_le ?_))
  have hdim : dim S ≤ dim T := Submodule.finrank_map_le _ _
  have hc : (dim S:ℝ) ≤ dim T := by exact_mod_cast hdim
  simp only [num,Fintype.card_fin]
  linarith

end
end Lax793645Proofs.Simplifications
