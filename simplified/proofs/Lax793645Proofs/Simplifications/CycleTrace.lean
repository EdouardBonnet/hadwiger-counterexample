import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! Trace normalization and shared-tester room for the proposed odd cycle.
These statements concern trace bits, never a canonical matrix representative.
The rank-to-edge-support and private-block hypotheses must be supplied by the
new geometry before applying them to marked profiles. -/
namespace Lax793645Proofs.Simplifications
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V]

def ones (t : V → Bool) : Finset V := Finset.univ.filter fun v => t v = true
def majorityZero (t : V → Bool) : Prop := 2*(ones t).card < Fintype.card V
def complement (t : V → Bool) : V → Bool := fun v => !(t v)

theorem ones_complement (t : V → Bool) :
    (ones t).card + (ones (complement t)).card = Fintype.card V := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun v => t v = true)
  simpa [ones, complement] using h

theorem majority_complement_exclusive (t : V → Bool) :
    majorityZero t → ¬majorityZero (complement t) := by
  have := ones_complement t
  unfold majorityZero
  omega

theorem majority_choice (t : V → Bool) (hodd : Odd (Fintype.card V)) :
    majorityZero t ∨ majorityZero (complement t) := by
  obtain ⟨k, hk⟩ := hodd
  have := ones_complement t
  unfold majorityZero
  omega

def normalizeTrace (t : V → Bool) : V → Bool := by
  classical
  exact if majorityZero t then t else complement t

theorem normalized_majority (t : V → Bool) (hodd : Odd (Fintype.card V)) :
    majorityZero (normalizeTrace t) := by
  classical
  unfold normalizeTrace
  split_ifs with h
  · exact h
  · exact (majority_choice t hodd).resolve_left h

theorem majority_unique {s t : V → Bool} (hs : majorityZero s) (ht : majorityZero t)
    (he : s = t ∨ s = complement t) : s = t := by
  rcases he with h | h
  · exact h
  · subst s
    exact False.elim (majority_complement_exclusive t ht hs)

/-- Equal edge traces propagate along the cycle with one edge removed. -/
theorem edge_trace_difference_constant {g : ℕ} (s t : Fin (g+1) → Bool)
    (he : ∀ i : Fin g, Bool.xor (s i.castSucc) (s i.succ) =
      Bool.xor (t i.castSucc) (t i.succ)) :
    ∀ i, Bool.xor (s i) (t i) = Bool.xor (s 0) (t 0) := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := he i
    have hlocal : Bool.xor (s i.succ) (t i.succ) =
        Bool.xor (s i.castSucc) (t i.castSucc) := by
      generalize s i.castSucc = a, s i.succ = b, t i.castSucc = c, t i.succ = d at *
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all
    exact hlocal.trans ih

theorem edge_trace_same_or_complement {g : ℕ} (s t : Fin (g+1) → Bool)
    (he : ∀ i : Fin g, Bool.xor (s i.castSucc) (s i.succ) =
      Bool.xor (t i.castSucc) (t i.succ)) : s = t ∨ s = complement t := by
  have h := edge_trace_difference_constant s t he
  cases h0 : Bool.xor (s 0) (t 0) with
  | false =>
    left
    funext i
    have hi := h i
    rw [h0] at hi
    cases hs : s i <;> cases ht : t i <;> simp_all
  | true =>
    right
    funext i
    have hi := h i
    rw [h0] at hi
    change s i = !(t i)
    cases hs : s i <;> cases ht : t i <;> simp_all

theorem normalized_edge_trace_unique {g : ℕ} (s t : Fin (g+1) → Bool)
    (hs : majorityZero s) (ht : majorityZero t)
    (he : ∀ i : Fin g, Bool.xor (s i.castSucc) (s i.succ) =
      Bool.xor (t i.castSucc) (t i.succ)) : s = t :=
  majority_unique hs ht (edge_trace_same_or_complement s t he)

/-- At most one ordinary contribution is charged to each owned clockwise edge. -/
theorem ordinary_support_bound {E : Type*} [Fintype E] (o : V → Bool)
    (edges : Finset E) (clockwise : V → E) (hinj : Function.Injective clockwise)
    (howned : ∀ v, o v = true → clockwise v ∈ edges) :
    (ones o).card ≤ edges.card := by
  classical
  exact Finset.card_le_card_of_injOn clockwise
    (fun v hv => howned v (Finset.mem_filter.mp hv).2)
    (fun _ _ _ _ h => hinj h)

/-- This is the shared-tester bound needed in place of sparse representatives. -/
theorem shared_support_bound (t o : V → Bool) (D : ℕ)
    (ht : majorityZero t) (ho : (ones o).card ≤ 2*D) :
    (ones (fun v => Bool.xor (t v) (o v))).card ≤ (Fintype.card V-1)/2 + 2*D := by
  classical
  have hsub : ones (fun v => Bool.xor (t v) (o v)) ⊆ ones t ∪ ones o := by
    intro v hv
    simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at *
    cases h1 : t v <;> cases h2 : o v <;> simp_all
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold majorityZero at ht
  omega

theorem retained_tester_room (t o : V → Bool) (D : ℕ)
    (hodd : Odd (Fintype.card V)) (ht : majorityZero t) (ho : (ones o).card ≤ 2*D) :
    (Fintype.card V+1)/2-2*D ≤
      (ones (complement (fun v => Bool.xor (t v) (o v)))).card := by
  have h := shared_support_bound t o D ht ho
  have hc := ones_complement (fun v => Bool.xor (t v) (o v))
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Prefix-sum routing in characteristic two; the omitted cycle edge has value zero. -/
def routePrefix (d : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := ∑ j ∈ Finset.range i, d j

theorem routePrefix_step (d : ℕ → ZMod 2) (i : ℕ) :
    routePrefix d i + routePrefix d (i+1) = d i := by
  simp only [routePrefix, Finset.sum_range_succ]
  have h (x : ZMod 2) : x+x=0 := CharTwo.add_self_eq_zero x
  rw [← add_assoc, h, zero_add]

theorem routePrefix_closes (d : ℕ → ZMod 2) (g : ℕ)
    (hzero : ∑ i ∈ Finset.range g, d i = 0) : routePrefix d g = routePrefix d 0 := by
  simpa [routePrefix] using hzero

/-- The actual cycle-cut kernel calculation works in every binary vector space. -/
theorem cycle_cut_difference_constant {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {g : ℕ} (w w' : Fin (g+1) → W)
    (hcut : ∀ i : Fin g, w i.castSucc+w i.succ = w' i.castSucc+w' i.succ) :
    ∀ i, w i+w' i = w 0+w' 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hc (z : W) : z+z=0 := ZModModule.add_self z
    calc
      w i.succ+w' i.succ = (w i.castSucc+w i.castSucc)+(w i.succ+w' i.succ) := by
        rw [hc, zero_add]
      _ = w i.castSucc+(w i.castSucc+w i.succ)+w' i.succ := by abel
      _ = w i.castSucc+(w' i.castSucc+w' i.succ)+w' i.succ := by rw [hcut i]
      _ = w i.castSucc+w' i.castSucc := by simp only [add_assoc, hc, add_zero]
      _ = w 0+w' 0 := ih

/-- The shared gradient demand has zero sum on an odd number of vertices. -/
theorem shared_demand_zero (a : V → ZMod 2) (hodd : Odd (Fintype.card V)) :
    (∑ l, ((∑ t, a t)+a l)) = 0 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, add_smul, mul_smul, two_smul, CharTwo.add_self_eq_zero, zero_add, one_smul]
  exact CharTwo.add_self_eq_zero _

end
end Lax793645Proofs.Simplifications
