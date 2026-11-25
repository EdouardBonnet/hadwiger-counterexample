import Lax793645Proofs.Simplifications.LinearAdaptiveOverlap
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ]

theorem rebate_complement {A C : Type} [Fintype A] [Fintype C]
    (ν : Wgt A) (hν : ∀ x,0≤ν x) (P : A→C) (f g : Wgt A) (B : ℝ) :
    rebate ν f (fun x=>B-g x) P= -rebate ν f g P := by
  rw [rebate_calc ν f _ P hν,rebate_calc ν f g P hν]
  have hh:=cash_orth ν hν P f (fun _=>B)
  have hz : dip ν (fun x=>f x-banner ν P f x) (fun _=>B)=0 := by
    rw [dip_sub]
    simpa only [Function.comp_def,sub_self] using congrArg (dip ν f (fun _=>B)-·) hh
  have he : dip ν (fun x=>f x-banner ν P f x) (fun x=>B-g x)=
      dip ν (fun x=>f x-banner ν P f x) (fun _=>B)-dip ν (fun x=>f x-banner ν P f x) g := by
    unfold dip
    simp only [mul_sub,avg_sub]
  rw [he,hz,zero_sub]

/-- The uniform adaptive overlap estimate also controls absolute
projection error. A pair-dependent complement selects its sign. -/
theorem linear_adaptive_rebate (μ : Wgt Λ) (hμ : IsLaw μ)
    (r : Λ→ℕ) (P : ∀ l,Mat (Fin (r l)) I) (R : ℕ) (hR : ∀ l,r l≤R)
    (η : ℝ) (hη : 0<η) :
    ∃ s : ℕ,(s:ℝ)≤R*bp R/η ∧ ∃ C : Mat (Fin s) I,
      ∀ (ν : Wgt (Vec I)),IsLaw ν → ∀ γ : ℝ,0≤γ →
      (∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ) →
      ∀ B ε : ℝ,0≤B → 0≤ε →
      ∀ (d e : Λ×Λ→Wgt (Vec I))
        (φ : ∀ l : Λ×Λ,Wgt (Vec (Fin (r l.1))))
        (ψ : ∀ l : Λ×Λ,Wgt (Vec (Fin (r l.2)))),
      (∀ l x,0≤d l x ∧ d l x≤B) → (∀ l x,0≤e l x ∧ e l x≤B) →
      (∀ l x,0≤φ l x ∧ φ l x≤B) → (∀ l x,0≤ψ l x ∧ ψ l x≤B) →
      (∀ l,lcost ν (fun x=>φ l (P l.1*ᵥx)) (d l)≤ε) →
      (∀ l,lcost ν (fun x=>ψ l (P l.2*ᵥx)) (e l)≤ε) →
      avg (pairW μ μ) (fun l=>|rebate ν (d l) (e l) C.mulVec|)≤
        4*B*ε+(2*γ*(B*bp R)^2+4*B*γ*bp s*(B*bp R))+B^2*η := by
  obtain ⟨s,hs,C,hC⟩:=linear_adaptive_overlap μ hμ r P R hR η hη
  refine ⟨s,hs,C,fun ν hν γ hγ hbias B ε hB hε d e φ ψ hd he hφ hψ hf hg=>?_⟩
  let neg (l:Λ×Λ):=rebate ν (d l) (e l) C.mulVec≤0
  let e' (l:Λ×Λ) (x:Vec I):=if neg l then e l x else B-e l x
  let ψ' (l:Λ×Λ) (x:Vec (Fin (r l.2))):=if neg l then ψ l x else B-ψ l x
  have he' l x : 0≤e' l x ∧ e' l x≤B := by
    dsimp only [e']
    split
    · exact he l x
    · constructor <;> linarith only [(he l x).1,(he l x).2]
  have hψ' l x : 0≤ψ' l x ∧ ψ' l x≤B := by
    dsimp only [ψ']
    split
    · exact hψ l x
    · constructor <;> linarith only [(hψ l x).1,(hψ l x).2]
  have hg' l : lcost ν (fun x=>ψ' l (P l.2*ᵥx)) (e' l)≤ε := by
    have hh x : |ψ' l (P l.2*ᵥx)-e' l x|=|ψ l (P l.2*ᵥx)-e l x| := by
      dsimp only [ψ',e']
      split
      · rfl
      · rw [show B-ψ l (P l.2*ᵥx)-(B-e l x)= -(ψ l (P l.2*ᵥx)-e l x) from by ring,abs_neg]
    simpa only [lcost,hh] using hg l
  have hproj (f : Wgt (Vec I)) (hf : ∀ x,0≤f x ∧ f x≤B) (x) :
      0≤banner ν C.mulVec f x ∧ banner ν C.mulVec f x≤B := by
    refine ⟨book_nonneg ν C.mulVec hν f (fun x=>(hf x).1) _,?_⟩
    exact (le_abs_self _).trans (cashbook_bound ν hν.nz C.mulVec f B hB
      (fun x=>by rw [abs_of_nonneg (hf x).1]; exact (hf x).2) _)
  have hh:=hC ν hν γ hγ hbias B ε hB hε d e' φ ψ'
    (fun l x=>(hd l x).1) (fun l x=>(he' l x).1) hφ hψ' hf hg'
    (fun l=>hproj (d l) (hd l)) (fun l=>hproj (e' l) (he' l))
  have hid l : dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e' l))-
      dip ν (d l) (e' l)=|rebate ν (d l) (e l) C.mulVec| := by
    have hr : dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e' l))-
        dip ν (d l) (e' l)= -rebate ν (d l) (e' l) C.mulVec := by unfold rebate; ring
    rw [hr]
    by_cases hn : neg l
    · simp only [e',if_pos hn]
      exact (abs_of_nonpos hn).symm
    · simp only [e',if_neg hn]
      rw [rebate_complement ν hν.nz,neg_neg,abs_of_nonneg (le_of_not_ge hn)]
  rw [show (fun l=>|rebate ν (d l) (e l) C.mulVec|)=
    (fun l=>dip ν (banner ν C.mulVec (d l)) (banner ν C.mulVec (e' l))-dip ν (d l) (e' l))
    from funext (fun l=>(hid l).symm),avg_sub]
  linarith only [hh]

end
end Lax793645Proofs.Simplifications
