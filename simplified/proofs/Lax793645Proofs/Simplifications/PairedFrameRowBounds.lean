import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MixedImageBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixQuotients
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FrameIntersectionCosts
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProductCoordinateReplacement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Submodule Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {U I J : Type} [Fintype U] [DecidableEq U]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem transverse_dual (P : Mat U I) (η : Vec U) (hη : η∉colSp P) :
    ∃ u : Vec U,Pᵀ*ᵥu=0 ∧ η⬝ᵥu=1 := by
  have hh : η∉annih (annih (colSp P)):=by rwa [annih_annih]
  rw [annih_mem] at hh
  push Not at hh
  obtain ⟨u,hu,hne⟩:=hh
  refine ⟨u,?_,(bit_cases (η⬝ᵥu)).resolve_left hne⟩
  ext i
  change (P.col i)⬝ᵥu=0
  rw [dotProduct_comm]
  exact (annih_mem u (colSp P)).mp hu _ (colSp_mem (P:=P) i)

theorem transverse_row_shift (P : Mat U I) (η : Vec U) (hη : η∉colSp P)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec) (x : Vec J) :
    ∃ A : Mat U I,Pᵀ*A=0 ∧ J₀ᵀ*ᵥ(Aᵀ*ᵥη)=x := by
  obtain ⟨u,hu,he⟩:=transverse_dual P η hη
  obtain ⟨L,hL⟩:=mat_left_inv hJ
  let A:=vecMulVec u (Lᵀ*ᵥx)
  refine ⟨A,?_,?_⟩
  · rw [show Pᵀ*A=vecMulVec (Pᵀ*ᵥu) (Lᵀ*ᵥx) from mul_vecMulVec _ _ _,hu]
    simp
  · dsimp only [A]
    rw [transpose_vecMulVec,vecMulVec_mulVec,show u⬝ᵥη=1 from (dotProduct_comm _ _).trans he]
    simp only [MulOpposite.op_one,one_smul]
    rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,hL,Matrix.transpose_one,Matrix.one_mulVec]

theorem weak_transverse_row (C : Mat I I → Prop) (P : Mat U I)
    (hc : ∃ Q : Mat U I,C (Pᵀ*Q)) (η : Vec U) (hη : η∉colSp P)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec) :
    mapW (weakMinus C P) (fun Q => J₀ᵀ*ᵥ(Qᵀ*ᵥη)) = unif := by
  rw [←unifOn_true (A:=Vec J)]
  refine uniform_orbit _ hc (fun _ _ => trivial) ?_
  intro y z _ _
  obtain ⟨A,hA,he⟩:=transverse_row_shift P η hη J₀ hJ (z-y)
  let E : Mat U I ≃ Mat U I := ⟨(·+A),(·+A),add_polar A,add_polar A⟩
  refine ⟨E,?_,?_⟩
  · intro Q
    change C (Pᵀ*Q) ↔ C (Pᵀ*(Q+A))
    rw [Matrix.mul_add,hA,add_zero]
  · intro Q
    change J₀ᵀ*ᵥ(Qᵀ*ᵥη)=y ↔ J₀ᵀ*ᵥ((Q+A)ᵀ*ᵥη)=z
    rw [transpose_add,Matrix.add_mulVec,Matrix.mulVec_add,he]
    constructor
    · intro h; rw [h,add_sub_cancel]
    · intro h
      apply add_right_cancel (b:=z-y)
      rw [h,add_sub_cancel]

theorem weak_transverse_row_pr (C : Mat I I → Prop) (P : Mat U I)
    (hc : ∃ Q : Mat U I,C (Pᵀ*Q)) (η : Vec U) (hη : η∉colSp P)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec) (θ : Vec J) :
    pr (weakMinus C P) (fun Q => J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ) = bp (-num J) := by
  change mapW (weakMinus C P) (fun Q => J₀ᵀ*ᵥ(Qᵀ*ᵥη)) θ = _
  rw [weak_transverse_row C P hc η hη J₀ hJ,unif_apply,card_space,dim_vec,bp_neg]

theorem conditioned_transverse_row (C : Mat I I → Prop) (hc : ∃ M,C M)
    (P : Mat U I) (hP : Injective P.mulVec) (hu : 2*num I-num U≤-1)
    (η : Vec U) (hη : η∉colSp P) (J₀ : Mat I J)
    (hJ : Injective J₀.mulVec) (θ : Vec J) :
    pr (unifOn (fun Q => FramesAt C (P,Q)))
      (fun Q => J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ) ≤ 2*bp (-num J) := by
  have hex : ∃ Q : Mat U I,C (Pᵀ*Q) := by
    obtain ⟨M,hM⟩:=hc
    obtain ⟨Q,hQ⟩:=gramL_surj I hP M
    change Pᵀ*Q=M at hQ
    exact ⟨Q,hQ.symm ▸ hM⟩
  exact (pr_cap (minus_le_weak hc P hP hu) _).trans_eq
    (congrArg (2*·) (weak_transverse_row_pr C P hex η hη J₀ hJ θ))

theorem injection_span_hit (hu : num I-num U≤-1) (η : Vec U) (hη : η≠0) :
    pr (unifOn (fun P : Mat U I => Injective P.mulVec))
      (fun P => η∈colSp P) ≤ 2*bp (num I+1-num U) := by
  have hh : ∀ P : Mat U I,η∈colSp P →
      ¬Disjoint (colSp P) (Submodule.span F {η}) := by
    intro P hP hd
    exact hη ((Submodule.disjoint_def.mp hd) η hP (Submodule.subset_span (by simp)))
  have hd : dim (Submodule.span F {η})=1 := by
    exact finrank_span_singleton hη
  refine (pr_cap (plus_le_unif hu) _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (pr_mono unif_subLaw.nz hh).trans ?_
  simpa only [hd,Nat.cast_one] using (any_span_hit (J:=I) (Submodule.span F {η}))

theorem frames_pr_slice (C : Mat I I → Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x) (p : (Mat U I×Mat U I)→Prop) :
    pr (unifOn (FramesAt C)) p =
      avg (unifOn (fun P : Mat U I=>Injective P.mulVec))
        (fun P=>pr (unifOn (fun Q=>FramesAt C (P,Q))) (fun Q=>p (P,Q))) := by
  simp only [pr,avg,Fintype.sum_prod_type]
  simp_rw [unifOn_slice (FramesAt C),plus_marginal hc]
  simp only [Finset.mul_sum,mul_assoc]

theorem frames_transverse_row (C : Mat I I → Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x) (hu : 2*num I-num U≤-1)
    (ξ η : Vec U) (hη : η≠0) (J₀ : Mat I J) (hJ : Injective J₀.mulVec)
    (θ : Vec J) :
    pr (unifOn (FramesAt C))
      (fun x=>J₀ᵀ*ᵥ(x.1ᵀ*ᵥξ)+J₀ᵀ*ᵥ(x.2ᵀ*ᵥη)=θ)
      ≤2*bp (-num J)+2*bp (num I+1-num U) := by
  have hce : ∃ M,C M := by obtain ⟨x,hx⟩:=hc; exact ⟨_,hx.1⟩
  have hip : ∃ P : Mat U I,Injective P.mulVec := by
    obtain ⟨x,hx⟩:=hc; exact ⟨x.1,hx.2.1⟩
  have hp : num I-num U≤-1 := by
    have hi : 0≤num I:=Nat.cast_nonneg _
    linarith only [hu,hi]
  rw [frames_pr_slice C hc]
  have hb (P : Mat U I) :
      pr (unifOn (fun Q=>FramesAt C (P,Q)))
        (fun Q=>J₀ᵀ*ᵥ(Pᵀ*ᵥξ)+J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ)
        ≤2*bp (-num J)+ind (η∈colSp P) := by
    by_cases hP : Injective P.mulVec
    · by_cases hh : η∈colSp P
      · refine (pr_le_tot (unifOn_sub _).nz).trans ((unifOn_sub _).total.trans ?_)
        rw [ind_one hh]
        have hh : 0≤bp (-num J):=(bp_pos _).le
        linarith
      · rw [ind_zero hh,add_zero]
        have he (Q : Mat U I) :
            J₀ᵀ*ᵥ(Pᵀ*ᵥξ)+J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ ↔
              J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ-J₀ᵀ*ᵥ(Pᵀ*ᵥξ) := by
          rw [eq_sub_iff_add_eq,add_comm]
        simp_rw [he]
        exact conditioned_transverse_row C hce P hP hu η hh J₀ hJ _
    · have hz : unifOn (fun Q=>FramesAt C (P,Q))=0 := by
        funext Q
        apply unifOn_carried
        exact fun h=>hP h.2.1
      rw [hz]
      have hz' : pr (0 : Wgt (Mat U I))
          (fun Q=>J₀ᵀ*ᵥ(Pᵀ*ᵥξ)+J₀ᵀ*ᵥ(Qᵀ*ᵥη)=θ)=0 := by simp [pr,avg]
      rw [hz']
      exact add_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (ind_nonneg _)
  refine (avg_mono (unifOn_sub _).nz hb).trans ?_
  rw [avg_add,(unifOn_law hip).avg_const]
  exact add_le_add le_rfl (injection_span_hit hp η hη)

theorem unif_nonzero_row (ξ : Vec U) (hξ : ξ≠0)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec) (θ : Vec J) :
    pr (unif : Wgt (Mat U I)) (fun P=>J₀ᵀ*ᵥ(Pᵀ*ᵥξ)=θ)=bp (-num J) := by
  have hh : ξ∉colSp (0 : Mat U I) := by simpa using Ne.symm hξ
  have hh':=weak_transverse_row_pr (fun _ : Mat I I=>True) (0 : Mat U I)
    ⟨0,trivial⟩ ξ hh J₀ hJ θ
  simpa only [weakMinus,unifOn_true] using hh'

/-- A mixed plus/minus row has exponentially small point masses, uniformly
in every feasible Gram prescription. -/
theorem frames_nonzero_row (C : Mat I I → Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x)
    (hu : 2*num I-num U≤-1) (hroom : num I+num J≤num U)
    (ξ η : Vec U) (hne : ξ≠0 ∨ η≠0) (J₀ : Mat I J)
    (hJ : Injective J₀.mulVec) (θ : Vec J) :
    pr (unifOn (FramesAt C))
      (fun x=>J₀ᵀ*ᵥ(x.1ᵀ*ᵥξ)+J₀ᵀ*ᵥ(x.2ᵀ*ᵥη)=θ)≤6*bp (-num J) := by
  by_cases hη : η=0
  · subst η
    have hξ : ξ≠0:=hne.resolve_right (not_not.mpr rfl)
    simp only [Matrix.mulVec_zero,add_zero]
    have he:=mapW_pr (unifOn (FramesAt (U:=U) C)) Prod.fst
      (fun P=>J₀ᵀ*ᵥ(Pᵀ*ᵥξ)=θ)
    rw [plus_marginal hc] at he
    rw [←he]
    have hp : num I-num U≤-1 := by
      have hi : 0≤num I:=Nat.cast_nonneg _
      linarith only [hu,hi]
    have hb:=(pr_cap (plus_le_unif hp) (fun P : Mat U I=>J₀ᵀ*ᵥ(Pᵀ*ᵥξ)=θ))
    rw [unif_nonzero_row ξ hξ J₀ hJ θ] at hb
    exact hb.trans (by have hh:0≤bp (-num J):=(bp_pos _).le; linarith only [hh])
  · refine (frames_transverse_row C hc hu ξ η hη J₀ hJ θ).trans ?_
    have hh : bp (num I+1-num U)≤2*bp (-num J) := by
      calc
        _≤bp (1-num J):=bp_le (by linarith only [hroom])
        _=2*bp (-num J):=by rw [sub_eq_add_neg,bp_add,bp_one]
    linarith only [hh]

theorem independent_sum_point_cap {E A V : Type} [Fintype E] [DecidableEq E]
    [Fintype A] [AddCommGroup V] (w : E→Wgt A) (hw : ∀ e,IsLaw (w e))
    (f : E→A→V) (e : E) (c : ℝ) (h : ∀ y,pr (w e) (fun x=>f e x=y)≤c) (θ : V) :
    pr (prodW w) (fun x=>(∑ i,f i (x i))=θ)≤c := by
  unfold pr
  rw [update_avg w e _ (hw e)]
  apply IsLaw.avg_le (prodW_law hw)
  intro x
  have he (y : A) : (∑ i,f i (update x e y i))=
      f e y+∑ i∈Finset.univ.erase e,f i (x i) := by
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ e),update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [update_of_ne (Finset.mem_erase.mp hi).1]
  simp_rw [he,show ∀ y : A,
      f e y+(∑ i∈Finset.univ.erase e,f i (x i))=θ ↔
        f e y=θ-(∑ i∈Finset.univ.erase e,f i (x i)) from fun _=>eq_sub_iff_add_eq.symm]
  exact h _

end
end Lax793645Proofs.Simplifications
