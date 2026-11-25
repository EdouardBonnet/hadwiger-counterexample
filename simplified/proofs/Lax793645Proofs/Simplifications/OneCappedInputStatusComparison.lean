import Lax793645Proofs.Simplifications.OneQueryFilteredComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {p : Shape}

/-- Conditioning the nominal input on fixed finite tester data costs only
its fixed density cap. No leaf or compatibility mass is divided out. -/
theorem one_capped_input_status_comparison (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L ε : ℝ) (hL : 0<L) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3 ≤ M*n →
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (κ ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
      IsLaw π → (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw mixer (M*n) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → oneOwnPart v.t q x) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      (∀ x,0≤κ x) → (∀ x,κ x≤L*unif x) →
      ∀ (χ : Inputs p n I→A) (G : OneUnit p n (M*n)→A→(I→F)→ℝ),
      (∀ o a b,|G o a b|≤1) →
      avg π (fun o=>|avg κ (fun x=>D (oneTemplateCoordinates v o x)*ψ x*
        G o (χ x) (oneQueryPValues v o x))|)≤ε := by
  obtain ⟨δ,hδ,hcal⟩:=one_capped_filtered_comparison (A:=A) v M hM c (ε/L) (div_pos hε hL)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal] with n hn mixer hN q D κ ψ π hπ hcap hD hsup hFour hψ hκ hκcap χ G hG
  let ψ' (x : Inputs p n I):=(κ x/(L*unif x))*ψ x
  have hu x : (0:ℝ)<unif (α:=Inputs p n I) x:=by rw [unif_apply]; positivity
  have hp x : |ψ' x|≤1 := by
    have hd : 0≤κ x/(L*unif x):=div_nonneg (hκ x) (mul_pos hL (hu x)).le
    have hupper : κ x/(L*unif x)≤1:=(div_le_one (mul_pos hL (hu x))).mpr (hκcap x)
    dsimp only [ψ']
    rw [abs_mul,abs_of_nonneg hd]
    exact (mul_le_mul hupper (hψ x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hh:=hn mixer hN q D ψ' π hπ hcap hD hsup hFour hp χ G hG
  have he o : avg κ (fun x=>D (oneTemplateCoordinates v o x)*ψ x*G o (χ x) (oneQueryPValues v o x))=
      L*avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ' x*G o (χ x) (oneQueryPValues v o x)) := by
    unfold avg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [ψ']
    field_simp [(hu x).ne',hL.ne']
  simp_rw [he,abs_mul,abs_of_pos hL,avg_mul']
  exact (mul_le_mul_of_nonneg_left hh hL.le).trans_eq (by field_simp)

end
end Lax793645Proofs.Simplifications
