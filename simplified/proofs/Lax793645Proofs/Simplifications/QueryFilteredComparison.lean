import Lax793645Proofs.Simplifications.QueryStatusWeights
import Lax793645Proofs.Simplifications.LinearQueryComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  {p : Shape} {n N : ℕ}

def queryPValues (v : Template p I) (o : UnitType p n N) (x : Inputs p n I) : I→F :=
  fun i=>innerP p o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i) (x i))

theorem query_p_weights_eq (v : Template p I) (a : I→F)
    (o : UnitType p n N) (x : Inputs p n I) :
    queryPWeights v a o x=ind (queryPValues v o x=a) := by
  rw [query_p_weights_indicator]
  congr 1
  exact propext funext_iff.symm

theorem finite_status_expansion (v : Template p I) (χ : Inputs p n I→A)
    (F : UnitType p n N→A→(I→F)→ℝ) (o : UnitType p n N) (x : Inputs p n I) :
    F o (χ x) (queryPValues v o x)=
      ∑ a:A,∑ b:I→HadwigerCounterexample.F,
        ind (χ x=a)*(F o a b*queryPWeights v b o x) := by
  simp_rw [query_p_weights_eq]
  rw [Finset.sum_eq_single (χ x)]
  · rw [Finset.sum_eq_single (queryPValues v o x)]
    · simp [ind]
    · intro b _ hb
      simp [ind,Ne.symm hb]
    · simp
  · intro a _ ha
    simp [ind,Ne.symm ha]
  · simp

/-- Any finite input classification fixed within the leaf is permitted.
Only its p-bit part depends on the sampled orientation. The filter on
the combined status may depend on the whole orientation. -/
theorem filtered_comparison_sum (v : Template p I) (π : Wgt (UnitType p n N))
    (hπ : IsLaw π) (D : Wgt (KeyCoordinates (KeySlots p v.t) N))
    (ψ : Wgt (Inputs p n I)) (hψ : ∀ x,|ψ x|≤1)
    (χ : Inputs p n I→A) (F : UnitType p n N→A→(I→HadwigerCounterexample.F)→ℝ)
    (hF : ∀ o a b,|F o a b|≤1) (ε : ℝ)
    (h : ∀ (ψ' : Wgt (Inputs p n I)),(∀ x,|ψ' x|≤1) →
      ∀ w : UnitType p n N→Wgt (Inputs p n I),
        (∀ o,inputFourierNorm (w o)≤bp (num I*(tagDegree p.g*p.h:ℕ))) →
        avg π (fun o=>|avg unif (fun x=>D (templateKeyCoordinates v o x)*ψ' x*w o x)|)≤ε) :
    avg π (fun o=>|avg unif (fun x=>D (templateKeyCoordinates v o x)*ψ x*
      F o (χ x) (queryPValues v o x))|)≤num A*num (I→HadwigerCounterexample.F)*ε := by
  let ψ' (a:A) (x : Inputs p n I):=ψ x*ind (χ x=a)
  let w (a:A) (b:I→HadwigerCounterexample.F) (o : UnitType p n N)
      (x : Inputs p n I):=F o a b*queryPWeights v b o x
  have hw a b o : inputFourierNorm (w a b o)≤bp (num I*(tagDegree p.g*p.h:ℕ)) := by
    unfold inputFourierNorm w
    rw [fourier_norm_smul]
    exact (mul_le_mul (hF o a b) (query_p_weights_norm v b o)
      (fourier_norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hp a x : |ψ' a x|≤1:=by
    dsimp only [ψ']
    rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
    exact (mul_le_mul (hψ x) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he o x : D (templateKeyCoordinates v o x)*ψ x*F o (χ x) (queryPValues v o x)=
      ∑ a:A,∑ b:I→HadwigerCounterexample.F,
        D (templateKeyCoordinates v o x)*ψ' a x*w a b o x := by
    rw [finite_status_expansion v χ F o x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [ψ',w]
    ring
  simp_rw [he,avg_sum]
  refine (avg_mono hπ.nz (fun o=>(Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun a _=>Finset.abs_sum_le_sum_abs _ _)))).trans ?_
  rw [avg_sum]
  simp_rw [avg_sum]
  refine (Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>h (ψ' a) (hp a) (w a b) (hw a b)))).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
  ring

/-- The capped-leaf estimate for the actual finite-status filtering
interface, including nominal joint predicates of arbitrary complexity. -/
theorem capped_filtered_comparison (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)) (π : Wgt (UnitType p n (M*n))),
      IsLaw π → (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw mixer (M*n)) (raw mixer (M*n)) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → ownPart v.t q (queryFromCoordinates v.t (M*n) x)) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      ∀ (χ : Inputs p n I→A) (F : UnitType p n (M*n)→A→(I→HadwigerCounterexample.F)→ℝ),
      (∀ o a b,|F o a b|≤1) →
      avg π (fun o=>|avg unif (fun x=>D (templateKeyCoordinates v o x)*ψ x*
        F o (χ x) (queryPValues v o x))|)≤ε := by
  let C:=num A*num (I→F)
  have hC : 0<C := by dsimp [C,num]; positivity
  obtain ⟨δ,hδ,hcal⟩:=capped_leaf_comparison v M hM c
    (bp (num I*(tagDegree p.g*p.h:ℕ))) (ε/C) (bp_pos _).le (div_pos hε hC)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal] with n hn mixer hN q D ψ π hπ hcap hD hsup hFour hψ χ F hF
  have hh:=filtered_comparison_sum v π hπ D ψ hψ χ F hF (ε/C)
    (fun ψ' hψ' w hw=>hn mixer hN q D ψ' π hπ hcap hD hsup hFour hψ' w hw)
  exact hh.trans_eq (by change C*(ε/C)=ε; field_simp)

end
end Lax793645Proofs.Simplifications
