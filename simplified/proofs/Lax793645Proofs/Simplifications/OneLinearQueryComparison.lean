import Lax793645Proofs.Simplifications.LinearSupportedTests
import Lax793645Proofs.Simplifications.OneCappedLeafComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Matrix
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A bounded key test is approximated by a bounded function of a fixed
number of linear equations, simultaneously for every capped leaf and
orientation-dependent Fourier-bounded input weight. -/
theorem one_linear_query_comparison {I : Type} [Fintype I] [DecidableEq I]
    {p : Shape} (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c B b ε : ℝ) (hB : 0<B) (hb : 0≤b) (hε : 0<ε) :
    ∃ k : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (q : I→F) (U : Wgt (KeyCoordinates (KeySlots p v.t) (M*n))),
      (∀ x,|U x|≤B) →
      ∃ r : ℕ,r≤k ∧ ∃ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
        ∃ φ : Wgt (Vec (Fin r)),(∀ y,|φ y|≤B) ∧
        ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3 ≤ M*n →
        ∀ (ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
        (∀ x,|ψ x|≤1) → IsLaw π →
        (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw mixer (M*n) o) →
        ∀ w : OneUnit p n (M*n)→Wgt (Inputs p n I),
        (∀ o,inputFourierNorm (w o)≤b) →
        avg π (fun o=>|avg unif (fun x=>
          (U (oneTemplateCoordinates v o x)-φ (P*ᵥoneTemplateCoordinates v o x))*
            ind (oneOwnPart v.t q (oneTemplateCoordinates v o x))*
            ψ x*w o x)|)≤ε := by
  obtain ⟨δ,hδ,hcal⟩:=one_capped_leaf_comparison v M hM c b (ε/(2*B)) hb (by positivity)
  obtain ⟨k,hk⟩:=linear_supported_test B ((2*B)*δ) hB.le (by positivity)
  refine ⟨k,?_⟩
  filter_upwards [hcal] with n hn q U hU
  let K (x : KeyCoordinates (KeySlots p v.t) (M*n)):=oneOwnPart v.t q x
  obtain ⟨r,hr,P,φ,hφ,hF⟩:=hk _ K U hU
  refine ⟨r,hr,P,φ,hφ,fun mixer hN ψ π hψ hπ hcap w hw=>?_⟩
  let D (x : KeyCoordinates (KeySlots p v.t) (M*n)):=((U x-φ (P*ᵥx))*ind (K x))/(2*B)
  have hnorm x : |D x|≤1:=by
    dsimp only [D]
    rw [abs_div,abs_mul,abs_of_nonneg (ind_nonneg _),abs_of_pos (show 0<2*B by positivity)]
    apply (div_le_one (by positivity)).mpr
    have hh : |U x-φ (P*ᵥx)|≤2*B:=
      (abs_sub _ _).trans (by linarith only [hU x,hφ (P*ᵥx)])
    exact (mul_le_mul_of_nonneg_right hh (ind_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (ind_le_one _) (by positivity)).trans_eq (mul_one _))
  have hsup x (hx : D x≠0) : K x:=by
    by_contra hh
    apply hx
    dsimp only [D]
    rw [ind_zero hh,mul_zero,zero_div]
  have hfourier ξ : |linearFourier D ξ|≤δ:=by
    have he : linearFourier D ξ=linearFourier (fun x=>(U x-φ (P*ᵥx))*ind (K x)) ξ/(2*B):=by
      unfold linearFourier D
      rw [←avg_div]
      apply avg_congr
      intro x _
      ring
    rw [he,abs_div,abs_of_pos (show 0<2*B by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    exact (hF ξ).trans_eq (mul_comm _ _)
  have hcomp:=hn mixer hN q D ψ π hπ hcap hnorm hsup hfourier hψ w hw
  have he o : avg unif (fun x=>(U (oneTemplateCoordinates v o x)-φ (P*ᵥoneTemplateCoordinates v o x))*
      ind (K (oneTemplateCoordinates v o x))*ψ x*w o x)=
      (2*B)*avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w o x):=by
    rw [←avg_mul']
    apply avg_congr
    intro x _
    dsimp only [D]
    field_simp
  change avg π (fun o=>|avg unif (fun x=>(U (oneTemplateCoordinates v o x)-φ (P*ᵥoneTemplateCoordinates v o x))*
      ind (K (oneTemplateCoordinates v o x))*ψ x*w o x)|)≤_
  simp only [he,abs_mul,abs_of_pos (show 0<2*B by positivity),avg_mul']
  exact (mul_le_mul_of_nonneg_left hcomp (by positivity)).trans_eq (by field_simp)

end
end Lax793645Proofs.Simplifications
