import Lax793645Proofs.Simplifications.LinearCommonOverlap
import Lax793645Proofs.Simplifications.LinearPartitionGeometry

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ]

/-- Common equations are selected using only the independent leaf law
and the leaf partitions. Both densities and both tables may subsequently
be selected using the complete pair of leaves. -/
theorem linear_adaptive_overlap (μ : Wgt Λ) (hμ : IsLaw μ)
    (r : Λ→ℕ) (P : ∀ l,Mat (Fin (r l)) I) (R : ℕ) (hR : ∀ l,r l≤R)
    (η : ℝ) (hη : 0<η) :
    ∃ s : ℕ,(s:ℝ)≤R*bp R/η ∧ ∃ C : Mat (Fin s) I,
      ∀ (ν : Wgt (Vec I)),IsLaw ν → ∀ γ : ℝ,0≤γ →
      (∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ) →
      ∀ B ε : ℝ,0≤B → 0≤ε →
      ∀ (d e : Λ×Λ→Wgt (Vec I))
        (φ : ∀ l : Λ×Λ,Wgt (Vec (Fin (r l.1))))
        (ψ : ∀ l : Λ×Λ,Wgt (Vec (Fin (r l.2)))),
      (∀ l x,0≤d l x) → (∀ l x,0≤e l x) →
      (∀ l x,0≤φ l x ∧ φ l x≤B) → (∀ l x,0≤ψ l x ∧ ψ l x≤B) →
      (∀ l,lcost ν (fun x=>φ l (P l.1*ᵥx)) (d l)≤ε) →
      (∀ l,lcost ν (fun x=>ψ l (P l.2*ᵥx)) (e l)≤ε) →
      (∀ l x,0≤banner ν C.mulVec (d l) x ∧ banner ν C.mulVec (d l) x≤B) →
      (∀ l x,0≤banner ν C.mulVec (e l) x ∧ banner ν C.mulVec (e l) x≤B) →
      avg (pairW μ μ) (fun l=>dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e l)))≤
        avg (pairW μ μ) (fun l=>dip ν (d l) (e l))+4*B*ε+
          (2*γ*(B*bp R)^2+4*B*γ*bp s*(B*bp R))+B^2*η := by
  obtain ⟨H,hs,hrare⟩ := shared_leaf_frequencies μ hμ (fun l => frequencySpace (P l)) R
    (fun l => (frequency_space_dimension (P l)).trans (by simpa only [Fintype.card_fin] using hR l)) η hη
  let s := dim H
  let C : Mat (Fin s) I := (pack H)ᵀ
  have hspace : frequencySpace C = H := frequency_space_matrix H
  refine ⟨s,hs,C,fun ν hν γ hγ hbias B ε hB hε d e φ ψ hd he hφ hψ hfd hge hpd hpe=>?_⟩
  let bad (l : Λ×Λ) := ¬ frequencySpace (P l.1) ⊓ frequencySpace (P l.2) ≤ H
  let F₀:=B*bp (R:ℝ)
  let err:=4*B*ε+(2*γ*F₀^2+4*B*γ*bp (s:ℝ)*F₀)
  have hF : 0≤F₀:=mul_nonneg hB (bp_pos _).le
  have herr : 0≤err:=by
    have hbs : 0<bp (s:ℝ):=bp_pos _
    dsimp only [err]
    positivity
  have hφnorm l : fourierNorm (fun x=>φ l (P l.1*ᵥx))≤F₀ := by
    refine (linear_bounded_fourier_norm (P l.1) (φ l) B
      (fun x=>by rw [abs_of_nonneg (hφ l x).1]; exact (hφ l x).2)).trans ?_
    rw [num,card_space,dim_vec,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_right (bp_le (by exact_mod_cast hR l.1)) hB).trans_eq (mul_comm _ _)
  have hψnorm l : fourierNorm (fun x=>ψ l (P l.2*ᵥx))≤F₀ := by
    refine (linear_bounded_fourier_norm (P l.2) (ψ l) B
      (fun x=>by rw [abs_of_nonneg (hψ l x).1]; exact (hψ l x).2)).trans ?_
    rw [num,card_space,dim_vec,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_right (bp_le (by exact_mod_cast hR l.2)) hB).trans_eq (mul_comm _ _)
  have hpoint l : dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e l))≤
      dip ν (d l) (e l)+err+B^2*ind (bad l) := by
    have ha : 0≤dip ν (d l) (e l):=avg_nonneg hν.nz (fun x=>mul_nonneg (hd l x) (he l x))
    by_cases hbad : bad l
    · rw [ind_one hbad,mul_one]
      have hh : dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e l))≤B^2 := by
        apply hν.avg_le
        intro x
        exact (mul_le_mul (hpd l x).2 (hpe l x).2 (hpe l x).1 hB).trans_eq (pow_two B).symm
      linarith only [hh,ha,herr]
    · rw [ind_zero hbad,mul_zero,add_zero]
      have hcommon : frequencySpace (P l.1) ⊓ frequencySpace (P l.2) ≤ frequencySpace C := by
        rw [hspace]
        exact not_not.mp hbad
      have hh := linear_actual_projected_overlap ν hν γ hγ hbias
        (P l.1) (P l.2) C hcommon (φ l) (ψ l) B hB (hφ l) (hψ l) (d l) (e l)
        (hd l) (he l) (fun x => by rw [abs_of_nonneg (hpe l x).1]; exact (hpe l x).2)
      have hcost:=mul_le_mul_of_nonneg_left (add_le_add (hfd l) (hge l))
        (show 0≤2*B from mul_nonneg (by norm_num) hB)
      have hprod:=mul_le_mul (hφnorm l) (hψnorm l) (fourier_norm_nonneg _) hF
      have hsum:=add_le_add (hφnorm l) (hψnorm l)
      have hb1:=mul_le_mul_of_nonneg_left hprod
        (show 0≤2*γ from mul_nonneg (by norm_num) hγ)
      have hb2:=mul_le_mul_of_nonneg_left hsum
        (show 0≤2*B*γ*num (Vec (Fin s)) from
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hγ) (Nat.cast_nonneg _))
      have hcard : num (Vec (Fin s))=bp (s:ℝ):=by rw [num,card_space,dim_vec,Fintype.card_fin]
      rw [hcard] at hh hb2
      dsimp only [err]
      nlinarith only [hh,hcost,hb1,hb2]
  have hh:=avg_mono (pairW_law hμ hμ).nz hpoint
  rw [avg_add,avg_add,(pairW_law hμ hμ).avg_const,avg_mul'] at hh
  have hr : B^2*pr (pairW μ μ) bad≤B^2*η:=mul_le_mul_of_nonneg_left hrare (sq_nonneg _)
  change B^2*avg (pairW μ μ) (fun x=>ind (bad x))≤B^2*η at hr
  dsimp only [err,F₀] at hh
  linarith only [hh,hr]

end
end Lax793645Proofs.Simplifications
