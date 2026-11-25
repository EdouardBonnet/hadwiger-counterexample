import Lax793645Proofs.Simplifications.PairedFrameRowBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Submodule Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E U I J : Type} [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def mixedFrameRow (J₀ : Mat I J) (v : E→Vec U×Vec U)
    (o : E→Mat U I×Mat U I) : Vec J :=
  ∑ e,(J₀ᵀ*ᵥ((o e).1ᵀ*ᵥ(v e).1)+J₀ᵀ*ᵥ((o e).2ᵀ*ᵥ(v e).2))

def mixedFrameRowLinear (J₀ : Mat I J) (o : E→Mat U I×Mat U I) :
    (E→Vec U×Vec U)→ₗ[F]Vec J where
  toFun v:=mixedFrameRow J₀ v o
  map_add' v w:=by
    simp only [mixedFrameRow,Pi.add_apply,Prod.fst_add,Prod.snd_add,Matrix.mulVec_add]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    abel
  map_smul' a v:=by
    rcases bit_cases a with h|h <;> subst a <;> simp [mixedFrameRow]

theorem independent_frame_row (C : Mat I I→Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x)
    (hu : 2*num I-num U≤-1) (hroom : num I+num J≤num U)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec)
    (v : E→Vec U×Vec U) (hv : v≠0) (θ : Vec J) :
    pr (prodW (fun _ : E=>unifOn (FramesAt C)))
      (fun o=>mixedFrameRow J₀ v o=θ)≤6*bp (-num J) := by
  obtain ⟨e,he⟩ : ∃ e,v e≠0 := Function.ne_iff.mp hv
  have hne : (v e).1≠0 ∨ (v e).2≠0 := by
    by_contra! hh
    exact he (Prod.ext hh.1 hh.2)
  exact independent_sum_point_cap _ (fun _=>unifOn_law hc)
    (fun i x=>J₀ᵀ*ᵥ(x.1ᵀ*ᵥ(v i).1)+J₀ᵀ*ᵥ(x.2ᵀ*ᵥ(v i).2)) e _
    (fun y=>frames_nonzero_row C hc hu hroom (v e).1 (v e).2 hne J₀ hJ y) θ

/-- A fixed frequency space pulls back injectively with an explicit raw
exception. The frequency space is chosen before the frame orientation. -/
theorem independent_frame_rank (C : Mat I I→Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x)
    (hu : 2*num I-num U≤-1) (hroom : num I+num J≤num U)
    (J₀ : Mat I J) (hJ : Injective J₀.mulVec)
    (H : Space (E→Vec U×Vec U)) :
    pr (prodW (fun _ : E=>unifOn (FramesAt C)))
      (fun o=>¬Injective ((mixedFrameRowLinear J₀ o).comp H.subtype))
        ≤6*bp ((dim H:ℝ)-num J) := by
  let w : Wgt (E→Mat U I×Mat U I):=prodW (fun _ : E=>unifOn (FramesAt C))
  have hw : IsLaw w:=prodW_law (fun _=>unifOn_law hc)
  let P (v : H) (o : E→Mat U I×Mat U I) :=
    v≠0 ∧ mixedFrameRow J₀ v.val o=0
  have hsub (o : E→Mat U I×Mat U I)
      (h : ¬Injective ((mixedFrameRowLinear J₀ o).comp H.subtype)) : ∃ v,P v o := by
    by_contra! hh
    apply h
    intro x y hxy
    have he : ((mixedFrameRowLinear J₀ o).comp H.subtype) (x-y)=0 := by
      rw [map_sub,hxy,sub_self]
    have hz : x-y=0 := by
      by_contra hn
      exact hh (x-y) ⟨hn,he⟩
    exact sub_eq_zero.mp hz
  have hp (v : H) : pr w (P v)≤6*bp (-num J) := by
    by_cases hv : v=0
    · simp only [P,hv,ne_eq,not_true_eq_false,false_and,pr_false]
      exact mul_nonneg (by norm_num) (bp_pos _).le
    · have hv' : v.val≠0:=fun h=>hv (Subtype.ext h)
      simpa only [P,hv,ne_eq,not_false_eq_true,true_and] using
        independent_frame_row C hc hu hroom J₀ hJ v.val hv' 0
  refine ((pr_mono hw.nz hsub).trans (pr_exists_le hw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun v _=>hp v).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,bp_sub,bp_neg]
  ring

theorem capped_frame_rank {T : Type} [Fintype T] (C : Mat I I→Prop)
    (hc : ∃ x : Mat U I×Mat U I,FramesAt C x)
    (hu : 2*num I-num U≤-1) (hroom : num I+num J≤num U)
    (J₀ : T→Mat I J) (hJ : ∀ t,Injective (J₀ t).mulVec)
    (H : Space (E→Vec U×Vec U)) (ρ : Wgt (E→Mat U I×Mat U I))
    (a : ℝ) (ha : 0≤a)
    (hρ : ∀ o,ρ o≤a*prodW (fun _ : E=>unifOn (FramesAt C)) o) :
    pr ρ (fun o=>∃ t,¬Injective ((mixedFrameRowLinear (J₀ t) o).comp H.subtype))
      ≤a*(Fintype.card T:ℝ)*(6*bp ((dim H:ℝ)-num J)) := by
  refine (pr_cap hρ _).trans ?_
  have hw:=prodW_law (fun _ : E=>unifOn_law hc)
  have hh:=pr_exists_le hw.nz
    (fun t o=>¬Injective ((mixedFrameRowLinear (J₀ t) o).comp H.subtype))
  have hh':=hh.trans (Finset.sum_le_sum
    (fun t _=>independent_frame_rank C hc hu hroom (J₀ t) (hJ t) H))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh'
  exact (mul_le_mul_of_nonneg_left hh' ha).trans_eq (by ring)

variable {p : Shape} {n N : ℕ}

def selectorFreeColumns (p : Shape) (n : ℕ) (s : Label p.b) : Mat (Full p n) (Fin n) :=
  embedMat (Sum.inl : Row p n→Full p n)*blockRay p n s Block.Z

theorem selector_free_columns_injective (p : Shape) (n : ℕ) (s : Label p.b) :
    Injective (selectorFreeColumns p n s).mulVec :=
  inj_comp_mat _ _ (embedMat_inj Sum.inl_injective) (blockRay_inj p n s Block.Z)

/-- The rank repair uses the prepared endpoint marginal cap, prior to
restricting to leaves or to a compatible pair of leaves. -/
theorem prepared_linear_rank (m : Mixer p n) (hN : 2*num (Full p n)-N≤-1)
    (H : Space (Comp p.g→Vec (Fin N)×Vec (Fin N)))
    (ρ : Wgt (Orient p n N)) (hρ : ∀ o,ρ o≤bp ((n:ℝ)/32)*raw m N o) :
    pr ρ (fun o=>∃ s : Label p.b,
      ¬Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
        ≤6*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32) := by
  have hroom : num (Full p n)+num (Fin n)≤num (Fin N) := by
    have hh:=(selectorFreeColumns p n (0 : Label p.b)).rank_le_card_height
    rw [mrk_inj.mp (selector_free_columns_injective p n 0)] at hh
    have hn : num (Fin n)≤num (Full p n):=by exact_mod_cast hh
    simp only [num,Fintype.card_fin] at hN hn ⊢
    linarith only [hN,hn]
  have hc : ∃ x : Oframe p n N,FramesAt (gramCond m) x :=
    framesAt_exists (gramCond_exists m) (by
      simp only [num,Fintype.card_fin] at hN ⊢
      linarith only [hN])
  have hu : 2*num (Full p n)-num (Fin N)≤-1 := by simpa only [num,Fintype.card_fin] using hN
  have hh:=capped_frame_rank (gramCond m) hc hu hroom
    (selectorFreeColumns p n) (selector_free_columns_injective p n) H ρ
    (bp ((n:ℝ)/32)) (bp_pos _).le hρ
  refine hh.trans_eq ?_
  rw [card_space,dim_vec]
  simp only [num,Fintype.card_fin]
  calc
    _=6*(bp ((n:ℝ)/32)*bp (p.b:ℝ)*bp ((dim H:ℝ)-n)):=by ring
    _=6*bp ((n:ℝ)/32+p.b+((dim H:ℝ)-n)):=by rw [bp_add,bp_add]
    _=_:=by congr 1; congr 1; ring

theorem prepared_linear_rank_calendar (p : Shape) (R : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,∀ N : ℕ,∀ (m : Mixer p n),
      2*num (Full p n)-N≤-1 →
      ∀ H : Space (Comp p.g→Vec (Fin N)×Vec (Fin N)),dim H≤R →
      ∀ ρ : Wgt (Orient p n N),
      (∀ o,ρ o≤bp ((n:ℝ)/32)*raw m N o) →
      pr ρ (fun o=>∃ s : Label p.b,
        ¬Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
          ≤bp (-(n:ℝ)/2) := by
  filter_upwards [Filter.eventually_ge_atTop (64*(R+p.b+4))] with n hn N m hN H hH ρ hρ
  refine (prepared_linear_rank m hN H ρ hρ).trans ?_
  have hR : (dim H:ℝ)≤R:=by exact_mod_cast hH
  have hn' : 64*((R:ℝ)+p.b+4)≤n:=by exact_mod_cast hn
  calc
    _≤bp (3:ℝ)*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32):=
      mul_le_mul_of_nonneg_right (by
        change (6:ℝ)≤bp ((3:ℕ):ℝ)
        rw [bp_nat]
        norm_num) (bp_pos _).le
    _=bp (3+((dim H:ℝ)+p.b-31*(n:ℝ)/32)):=(bp_add _ _).symm
    _≤bp (-(n:ℝ)/2):=bp_le (by linarith only [hR,hn'])

/-- The common predictor coordinates may grow with the dimension.
The exception remains exponential as long as their actual frequency
dimension is at most `n / 4`. This does not assert full rank on a capped leaf. -/
theorem prepared_growing_linear_rank_calendar (p : Shape) :
    ∀ᶠ n : ℕ in Filter.atTop,∀ N : ℕ,∀ (m : Mixer p n),
      2*num (Full p n)-N≤-1 →
      ∀ H : Space (Comp p.g→Vec (Fin N)×Vec (Fin N)),dim H≤n/4 →
      ∀ ρ : Wgt (Orient p n N),
      (∀ o,ρ o≤bp ((n:ℝ)/32)*raw m N o) →
      pr ρ (fun o=>∃ s : Label p.b,
        ¬Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
          ≤bp (-(n:ℝ)/2) := by
  filter_upwards [Filter.eventually_ge_atTop (64*(p.b+4))] with n hn N m hN H hH ρ hρ
  refine (prepared_linear_rank m hN H ρ hρ).trans ?_
  have hdim : 4*dim H≤n := by omega
  have hdim' : 4*(dim H:ℝ)≤n := by exact_mod_cast hdim
  have hn' : 64*((p.b:ℝ)+4)≤n := by exact_mod_cast hn
  calc
    _≤bp (3:ℝ)*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32):=
      mul_le_mul_of_nonneg_right (by
        change (6:ℝ)≤bp ((3:ℕ):ℝ)
        rw [bp_nat]
        norm_num) (bp_pos _).le
    _=bp (3+((dim H:ℝ)+p.b-31*(n:ℝ)/32)):=(bp_add _ _).symm
    _≤bp (-(n:ℝ)/2):=bp_le (by linarith only [hdim',hn'])

end
end Lax793645Proofs.Simplifications
