/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.ReservedLabels.
Changes: allow any fixed deletion budget, including the span-exclusion
budget for degree-one selectors, instead of the former constant 100.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ReservedLabels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open StatusAnalysis.Club StatusAnalysis.Guild
open scoped BigOperators
noncomputable section

variable {I : Grid → Type} {A B : Rates} {L : Type} [DecidableEq L]
variable (C : Congress I A B L)

def richAt (budget : ℕ) :=
  ∀ i : Grid,∀ s : Straps L,sizeB s budget → ∀ y : View (A i.1) (B i.2),∃ j,
    (C i).zone s j ∧ view _ _ ((C i).writes j)=y

theorem richAt_covers {budget : ℕ} (h : richAt C budget) (s : Straps L)
    (hs : sizeB s budget) (i : Grid) : coverBase (chapter C s i) := by
  intro y
  obtain ⟨j,hj,hy⟩ := h i s hs y
  exact ⟨⟨_,(C i).band_write s hj⟩,hy⟩

set_option maxHeartbeats 900000 in
/-- Eight possible losses of kernel dimension suffice to stabilize all four
scalar spans against arbitrary deletions of the prescribed fixed size. -/
theorem stable_at_budget (budget : ℕ) (h : richAt C (9*budget)) :
    ∃ s : Straps L,sizeB s (8*budget) ∧
      ∀ i : Grid,∀ t : Straps L,sizeB t budget →
        (C i).band (s⊔t)=chapter C s i := by
  classical
  have hh (k : ℕ) (hk : k ≤ 8) (t : Straps L)
      (ht : sizeB t ((8-k)*budget)) (hb : excess C t ≤ k) :
      ∃ s : Straps L,sizeB s (8*budget) ∧
        ∀ i : Grid,∀ u : Straps L,sizeB u budget →
          (C i).band (s⊔u)=chapter C s i := by
    induction k generalizing t with
    | zero =>
      refine ⟨t,ht,fun i u hu => ?_⟩
      let v := t⊔u
      have he : sizeB v (9*budget) := fun side => (Finset.card_union_le ..).trans
        ((Nat.add_le_add (ht side) (hu side)).trans (by omega))
      have hz (i : Grid) : overage (chapter C t i)=0 := by
        have hh : overage (chapter C t i) ≤ 0 :=
          (Finset.single_le_sum (s:=Finset.univ) (fun i _ => Nat.zero_le (overage (chapter C t i)))
            (Finset.mem_univ i)).trans hb
        exact Nat.eq_zero_of_le_zero hh
      exact eq_of_le_of_not_lt (chapter_mono C le_sup_left i) (fun hx =>
        Nat.not_lt_zero _ ((overage_lt hx (richAt_covers C h v he i)).trans_eq (hz i)))
    | succ k ih =>
      have hT : sizeB t (8*budget) := fun side => (ht side).trans
        (Nat.mul_le_mul_right budget (Nat.sub_le 8 (k+1)))
      by_cases hE : ∃ u : Straps L,sizeB u budget ∧ ∃ i : Grid,
          chapter C (t⊔u) i < chapter C t i
      · obtain ⟨u,hu,i,hU⟩ := hE
        let s := t⊔u
        have hstep : (8-(k+1))*budget+budget=(8-k)*budget := by
          have he : 8-k=(8-(k+1))+1 := by omega
          rw [he,Nat.add_mul,Nat.one_mul]
        have he : sizeB s ((8-k)*budget) := fun side => (Finset.card_union_le ..).trans
          ((Nat.add_le_add (ht side) (hu side)).trans_eq hstep)
        apply ih (by omega) s he
        have hsmall : sizeB s (9*budget) := fun side => (he side).trans
          ((Nat.mul_le_mul_right budget (Nat.sub_le 8 k)).trans (by omega))
        have hdrop : excess C s < excess C t := by
          unfold excess
          have h1 := overage_lt hU (richAt_covers C h s hsmall i)
          exact Finset.sum_lt_sum (fun i _ => overage_mono (chapter_mono C le_sup_left i))
            ⟨i,Finset.mem_univ _,h1⟩
        omega
      exact ⟨t,hT,fun i u hu => eq_of_le_of_not_lt
        (chapter_mono C (s:=t) (t:=t⊔u) le_sup_left i)
        (fun hx => hE ⟨u,hu,i,hx⟩)⟩
  exact hh 8 (Nat.le_refl _) ⊥ (by intro side; simp) (excess_bound C _)

end
end Lax793645Proofs.Simplifications
