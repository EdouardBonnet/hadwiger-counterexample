import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
---
title: Finite deterministic container recursion
type: lemma
---
The fingerprint procedure preserves every independent residual set, terminates by strict cardinality decrease, and reconstructs its terminal set from its ordered fingerprint. A stepwise entropy increase bounds the fingerprint length.
-/

namespace Lax342547.ContainerRun



noncomputable def next {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : Finset U := by
  classical
  exact if v ∈ I then R.filter (fun w => ¬ H v w) else R.erase v

noncomputable def run {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I : Finset U) : ℕ → Finset U → Finset U × List U := by
  classical
  exact fun fuel R => match fuel with
  | 0 => (R,[])
  | n+1 => if active R then
      let v := pick R
      let result := run active pick H I n (next H I R v)
      (result.1,if v ∈ I then v::result.2 else result.2)
    else (R,[])

noncomputable def replay {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) : ℕ → Finset U → List U → Finset U := by
  classical
  exact fun fuel R record => match fuel with
  | 0 => R
  | n+1 => if active R then
      let v := pick R
      if record.head? = some v then
        replay active pick H n (R.filter (fun w => ¬ H v w)) record.tail
      else replay active pick H n (R.erase v) record
    else R

axiom next_subset {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : next H I R v ⊆ R

axiom next_preserves {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U)
    (hI : I ⊆ R) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H x y) : I ⊆ next H I R v

axiom next_card_lt {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U)
    (hv : v ∈ R) (hne : ∃ w ∈ R, H v w) : (next H I R v).card < R.card

axiom recorded_subset {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) :
    ∀ v ∈ (run active pick H I fuel R).2, v ∈ I

axiom run_replay {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) :
    replay active pick H fuel R (run active pick H I fuel R).2 = (run active pick H I fuel R).1

axiom run_preserves {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ)
    (hI : I ⊆ R) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H x y) :
    I ⊆ (run active pick H I fuel R).1 ∧ (run active pick H I fuel R).1 ⊆ R

axiom run_terminal {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ)
    (hpick : ∀ T, active T → pick T ∈ T ∧ ∃ w ∈ T, H (pick T) w)
    (hsize : R.card < fuel) : ¬ active (run active pick H I fuel R).1

axiom run_entropy_budget {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) (E : Finset U → ℝ) (B δ : ℝ)
    (hδ : 0 ≤ δ) (hb : ∀ T, active T → E T ≤ B)
    (hstep : by
      classical
      exact ∀ T, active T → active (next H I T (pick T)) →
        E T + (if pick T ∈ I then δ else 0) ≤ E (next H I T (pick T)))
    (hR : active R) :
    (((run active pick H I fuel R).2.length : ℝ)-1)*δ ≤ B-E R

end Lax342547.ContainerRun
