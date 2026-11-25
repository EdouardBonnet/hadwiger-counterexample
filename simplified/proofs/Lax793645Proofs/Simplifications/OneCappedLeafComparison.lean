import Lax793645Proofs.Simplifications.OneDirectCappedFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

theorem one_query_weight_bound (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ w : Wgt (Inputs p n I))
    (hD : ∀ x,|D x|≤1) (hψ : ∀ x,|ψ x|≤1) (b : ℝ)
    (hw : inputFourierNorm w≤b) (o : OneUnit p n N) :
    |avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w x)|≤b := by
  have hb : 0≤b:=(fourier_norm_nonneg _).trans hw
  refine (abs_avg_le unif_law.nz).trans (unif_law.avg_le (fun x=>?_))
  have hx : |w x|≤b:=by
    have hh:=fourier_norm_point (fun z=>w (inputCoordinates p n I z))
      ((inputCoordinates p n I).symm x)
    simpa only [LinearEquiv.apply_symm_apply] using hh.trans hw
  rw [abs_mul,abs_mul]
  exact (mul_le_mul (mul_le_mul (hD _) (hψ x) (abs_nonneg _) (by norm_num))
    hx (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem one_query_mean_from_exception (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (π : Wgt (OneUnit p n N)) (hπ : IsLaw π)
    (w : OneUnit p n N→Wgt (Inputs p n I)) (b ε : ℝ) (hε : 0≤ε)
    (hD : ∀ x,|D x|≤1) (hψ : ∀ x,|ψ x|≤1)
    (hw : ∀ o,inputFourierNorm (w o)≤b) :
    avg π (fun o=>|avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w o x)|)≤
      ε+b*pr π (oneQueryWeightBad v D ψ b ε) := by
  have hp o : |avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w o x)|≤
      ε+b*ind (oneQueryWeightBad v D ψ b ε o) := by
    by_cases ho : oneQueryWeightBad v D ψ b ε o
    · rw [ind_one ho,mul_one]
      exact (one_query_weight_bound v D ψ (w o) hD hψ b (hw o) o).trans (by linarith only [hε])
    · rw [ind_zero ho,mul_zero,add_zero]
      exact le_of_not_gt (fun hh=>ho ⟨w o,hw o,hh⟩)
  exact (avg_mono hπ.nz hp).trans_eq (by rw [avg_add,avg_mul',hπ.avg_const]; rfl)

/-- The proposed leaf-uniform comparison, in an adaptive-weight form.
All construction parameters precede the Fourier cutoff. -/
theorem one_capped_leaf_comparison (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c b ε : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3 ≤ M*n →
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
      IsLaw π → (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw mixer (M*n) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → oneOwnPart v.t q x) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      ∀ w : OneUnit p n (M*n)→Wgt (Inputs p n I),
      (∀ o,inputFourierNorm (w o)≤b) →
      avg π (fun o=>|avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w o x)|)≤ε := by
  obtain ⟨δ,hδ,hcal⟩:=one_direct_capped_leaf_fourier v M hM c b (ε/2) hb (half_pos hε)
  have he : Tendsto (fun n : ℕ=>b*bp (-(n:ℝ))) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,one_mul,neg_mul,mul_zero] using
      (((bp_tendsto_zero (a:=1) (by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul b)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal,he.eventually (eventually_le_nhds (half_pos hε))]
    with n hn hsmall mixer hN q D ψ π hπ hcap hD hsup hF hψ w hw
  have hx:=hn mixer hN q D ψ π hπ.nz hcap hD hsup hF hψ
  have hm:=one_query_mean_from_exception v D ψ π hπ w b (ε/2) (half_pos hε).le hD hψ hw
  have hh:=mul_le_mul_of_nonneg_left hx hb
  linarith only [hm,hh,hsmall]

end
end Lax793645Proofs.Simplifications
