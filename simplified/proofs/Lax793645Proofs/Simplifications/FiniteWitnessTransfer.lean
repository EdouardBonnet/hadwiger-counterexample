import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RareLeafEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
open scoped BigOperators
noncomputable section
variable {A B J : Type} [Fintype A] [Fintype B] [Fintype J]

def substantialWitness (μ : Wgt A) (ν : Wgt B) (P : J → A → Prop) (Q : J → B → Prop) (β : ℝ) :=
  ∃ j, 2*β ≤ pr μ (P j) ∧ 2*β ≤ pr ν (Q j)

theorem finite_witness_bound (μ : Wgt A) (ν : Wgt B) (hμ : IsLaw μ) (hν : IsLaw ν)
    (Good : A×B → Prop) (P : J → A → Prop) (Q : J → B → Prop)
    (hcover : ∀ x, pairW μ ν x ≠ 0 → Good x → ∃ j, P j x.1 ∧ Q j x.2)
    (β : ℝ) (hβ : 0 ≤ β) :
    pr (pairW μ ν) Good ≤ 2*β*Fintype.card J+ind (substantialWitness μ ν P Q β) := by
  classical
  by_cases hs : substantialWitness μ ν P Q β
  · rw [ind_one hs]
    exact (pr_le_tot (pairW_law hμ hν).nz).trans ((pairW_law hμ hν).total.le.trans
      (le_add_of_nonneg_left (by positivity)))
  rw [ind_zero hs,add_zero]
  have hp j : pr μ (P j)*pr ν (Q j) ≤ 2*β := by
    by_cases h : 2*β ≤ pr μ (P j)
    · have h' : pr ν (Q j) ≤ 2*β := (lt_of_not_ge (fun h' => hs ⟨j,h,h'⟩)).le
      exact (mul_le_mul ((pr_le_tot hμ.nz).trans hμ.total.le) h'
        (pr_nonneg hν.nz) zero_le_one).trans_eq (one_mul _)
    · have h' : pr μ (P j) ≤ 2*β := (lt_of_not_ge h).le
      exact (mul_le_mul h' ((pr_le_tot hν.nz).trans hν.total.le)
        (pr_nonneg hν.nz) (by positivity)).trans_eq (mul_one _)
  refine ((pr_on_mono (pairW_law hμ hν).nz hcover).trans
    (pr_exists_le (pairW_law hμ hν).nz _)).trans ?_
  simp_rw [pairW_pr]
  exact (Finset.sum_le_sum fun j _ => hp j).trans_eq (by simp; ring)

theorem finite_witness_with_floor (μ : Wgt A) (ν : Wgt B) (hμ : IsLaw μ) (hν : IsLaw ν)
    (Compatible Secure : A×B → Prop) (P : J → A → Prop) (Q : J → B → Prop)
    (γ : ℝ) (hfloor : 0 < pr (pairW μ ν) Compatible → γ≤pr (pairW μ ν) Compatible)
    (hcover : ∀ x, pairW μ ν x ≠ 0 → Compatible x ∧ Secure x → ∃ j, P j x.1 ∧ Q j x.2)
    (β : ℝ) (hβ : 0 ≤ β) (hsize : 2*β*Fintype.card J ≤ γ/2) :
    pr (pairW μ ν) Compatible ≤
      2*pr (pairW μ ν) (fun x => Compatible x ∧ ¬Secure x) +
        ind (substantialWitness μ ν P Q β) := by
  classical
  by_cases hs : substantialWitness μ ν P Q β
  · rw [ind_one hs]
    exact (pr_le_tot (pairW_law hμ hν).nz).trans ((pairW_law hμ hν).total.le.trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num) (pr_nonneg (pairW_law hμ hν).nz))))
  rw [ind_zero hs,add_zero]
  by_cases hc : 0 < pr (pairW μ ν) Compatible
  · have h := finite_witness_bound μ ν hμ hν (fun x => Compatible x ∧ Secure x) P Q hcover β hβ
    rw [ind_zero hs,add_zero] at h
    have hp : pr (pairW μ ν) Compatible ≤
        pr (pairW μ ν) (fun x => Compatible x ∧ Secure x) +
        pr (pairW μ ν) (fun x => Compatible x ∧ ¬Secure x) :=
      (pr_mono (pairW_law hμ hν).nz (fun _ h => by tauto)).trans (pr_or_le (pairW_law hμ hν).nz)
    linarith only [h,hsize,hp,hfloor hc]
  · exact (le_of_not_gt hc).trans (mul_nonneg (by norm_num) (pr_nonneg (pairW_law hμ hν).nz))

theorem finite_witness_rare (μ : Wgt A) (ν : Wgt B) (hμ : IsLaw μ) (hν : IsLaw ν)
    (Compatible Secure : A×B → Prop) (P : J → A → Prop) (Q : J → B → Prop)
    (hconst : 0 < pr (pairW μ ν) Compatible → pr (pairW μ ν) Compatible=1)
    (hcover : ∀ x, pairW μ ν x ≠ 0 → Compatible x ∧ Secure x → ∃ j, P j x.1 ∧ Q j x.2)
    (β : ℝ) (hβ : 0 ≤ β) (hsize : 2*β*Fintype.card J ≤ 1/2) :
    pr (pairW μ ν) Compatible ≤
      2*pr (pairW μ ν) (fun x => Compatible x ∧ ¬Secure x) +
        ind (substantialWitness μ ν P Q β) :=
  finite_witness_with_floor μ ν hμ hν Compatible Secure P Q 1
    (fun hp=>(hconst hp).ge) hcover β hβ hsize

end
end Lax793645Proofs.Simplifications
