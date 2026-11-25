/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.GreedyExposures.
Changes: archive namespace and imports. A finite subset minimum replaces greedy exposure.
See references/upstream-construction.json.
-/
import Lax793645Proofs.Simplifications.FiniteSubsetExposure

namespace Lax793645Proofs.Upstream.OAI

/-! # Greedy Exposures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I : Type} [DecidableEq I]

def price (f : I → Ambient p N) (S : Cov p N) (W : Finset I) :=
  W.sup (fun i => tax p S (matter p (f i)))

private theorem sum_charge_sign (f : I → Ambient p N) (W : Finset I) (i : Bool) :
    cdSign p (arrange p f W) i ≤ ∑ j∈W,epoch p (f j) := by
  classical
  induction W using Finset.induction with
  | empty =>
    have h : cdSign p (N:=N) ⊥ i=0 := Finset.sum_eq_zero fun e _ => finrank_bot ..
    rw [arrange,Finset.sup_empty,Finset.sum_empty,h]
  | insert x W hx hi =>
    rw [show arrange p f (insert x W)=matter p (f x)⊔arrange p f W from Finset.sup_insert,
      Finset.sum_insert hx]
    calc cdSign p _ i ≤ cdSign p (matter p (f x)) i+cdSign p (arrange p f W) i := by
                          unfold cdSign
                          rw [← Finset.sum_add_distrib]
                          exact Finset.sum_le_sum fun i _ =>
                            Submodule.finrank_add_le_finrank_add_finrank ..
         _ ≤ _ := by rw [matter_dim]; exact add_le_add (le_refl _) hi

theorem arrange_bound (f : I→Ambient p N) (W : Finset I) (k : ℕ) (h : ∀ i ∈ W,epoch p (f i) ≤ k)
    (i : Bool) :
    cdSign p (arrange p f W) i ≤ W.card*k :=
  (sum_charge_sign f W i).trans ((Finset.sum_le_sum fun j hj => h j hj).trans_eq (by simp))

theorem sparse_covered (f : I→ Ambient p N) (W : Finset I)
    (m b r : ℕ) (hW : W.card=2^m*(2*b))
    (hb : 1 ≤ b) (hm : 16*r < m) (hf : ∀ i∈W,epoch p (f i) ≤ r)
    (h : 2 * epoch p (∑ i∈W,f i) ≤ b) :
    ∃ E T : Finset I,E⊆ W ∧ T⊆ W ∧ Disjoint E T ∧ T.card=b ∧
      ∀ i∈T,covered p (arrange p f E) (f i) := by
  classical
  let D (A : Finset I) := cdim p (arrange p f A)
  have hmono : Monotone D := fun _ _ h => cdim_mono (Finset.sup_mono h)
  have hbound : D W ≤ 2*r*W.card := by
    dsimp only [D]
    rw [cdim_sign]
    have h₁ := arrange_bound f W r hf true
    have h₂ := arrange_bound f W r hf false
    simpa only [two_mul,Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.add_le_add h₁ h₂
  obtain ⟨E,R,hE,hD,hR,hmargin⟩ :=
    Lax793645Proofs.Simplifications.subset_with_small_marginals W D hmono
      (2*b) m r (by omega) hW hm hbound
  let S := arrange p f E
  let P (i : I) := ¬ covered p S (f i)
  let J := R.filter P
  have hZ :
      epoch p (∑ i∈R,erased p S (f i)) ≤ epoch p (∑ i∈W,f i) := by
    have hh : ∑ i∈E,erased p S (f i) = 0 := Finset.sum_eq_zero fun i hi =>
      covered_part (S:=S) (show matter p (f i) ≤
        E.sup (fun j => matter p (f j)) from (@Finset.le_sup _ _ _ _ _ (fun j => matter p (f j)) _ hi))
    have h1 : (∑ i∈R, erased p S (f i))=erased p S (∑ i∈W,f i) := by
      rw [hE,Finset.sum_union hD,map_add,map_sum,map_sum,hh,zero_add]
    rw [h1]; exact epoch_erased ..
  have hu : J.card≤ ∑ i∈R,epoch p (erased p S (f i)) := by
    calc J.card = ∑ i∈R, (if P i then (1:ℕ) else 0) := by rw [←Finset.sum_filter]; simp [J]
         _ ≤ _ := Finset.sum_le_sum fun j _ => by
                   split
                   · rename_i hh
                     exact Nat.one_le_iff_ne_zero.mpr (fun h => hh ((epoch_eq_zero _).mp h))
                   exact Nat.zero_le _
  have hfull : arrange p f W = S ⊔ arrange p f R := by rw [hE,arrange,Finset.sup_union]; rfl
  have hmargin' (i) (hi : i ∈ R) :
      4*(R.card*tax p S (matter p (f i))) ≤ 4*tax p S (arrange p f R)+R.card := by
    have hh := hmargin i hi
    change 4*(R.card*(cdim p (arrange p f (insert i E)) - cdim p S)) ≤
      4*(cdim p (arrange p f W)-cdim p S)+R.card at hh
    rw [show arrange p f (insert i E) = S ⊔ matter p (f i) from
      Finset.sup_insert.trans (sup_comm _ _),hfull] at hh
    exact hh
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup R
    (Finset.card_pos.mp (show 0 < R.card by omega)) (fun i => tax p S (matter p (f i)))
  have hL := hmargin' i hi
  have hp : (∑ j ∈ R, tax p S (matter p (f j))) ≤ R.card*tax p S (matter p (f i)) := by
    refine (Finset.sum_le_sum (g:=fun _ => tax p S (matter p (f i))) (fun j hj => ?_)).trans_eq (by simp)
    exact (Finset.le_sup (f:=fun j => tax p S (matter p (f j))) hj).trans_eq hmax
  have ht := (epoch_charge f S R).2
  have hb' : b≤ (R\ J).card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset P _)]
    change b ≤ R.card-J.card
    have heq : J.card≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  obtain ⟨T,hT,hb'⟩ := Finset.exists_subset_card_eq hb'
  have hz : T ⊆ R := hT.trans Finset.sdiff_subset
  refine ⟨E,T,hE.symm ▸ Finset.subset_union_left,hE.symm ▸ hz.trans Finset.subset_union_right,
    Disjoint.mono_right hz hD,hb',fun i hi => ?_⟩
  exact Classical.byContradiction fun h =>
    (Finset.mem_sdiff.mp (hT hi)).2 (Finset.mem_filter.mpr ⟨hz hi,h⟩)

end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
