import Lax342547.ContainerRun
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Lax342547Proofs.ContainerRun
open Lax342547.ContainerRun

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.ContainerRun.next_subset
---
-/
theorem next_subset {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : next H I R v ⊆ R := by
  classical
  unfold next
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.erase_subset _ _

/--
---
conclusion: Lax342547.ContainerRun.next_preserves
---
-/
theorem next_preserves {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U)
    (hI : I ⊆ R) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H x y) : I ⊆ next H I R v := by
  classical
  unfold next
  split_ifs with hv
  · intro x hx
    exact Finset.mem_filter.mpr ⟨hI hx,hind v hv x hx⟩
  · intro x hx
    exact Finset.mem_erase.mpr ⟨(fun heq => hv (heq ▸ hx)),hI hx⟩

/--
---
conclusion: Lax342547.ContainerRun.next_card_lt
---
-/
theorem next_card_lt {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U)
    (hv : v ∈ R) (hne : ∃ w ∈ R, H v w) : (next H I R v).card < R.card := by
  classical
  unfold next
  split_ifs
  · apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    obtain ⟨w,hw,hH⟩ := hne
    exact ⟨w,hw,not_not.mpr hH⟩
  · exact Finset.card_erase_lt_of_mem hv

/--
---
conclusion: Lax342547.ContainerRun.recorded_subset
---
-/
theorem recorded_subset {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) :
    ∀ v ∈ (run active pick H I fuel R).2, v ∈ I := by
  classical
  induction fuel generalizing R with
  | zero => simp [run]
  | succ n ih =>
    by_cases ha : active R
    · simp only [run,ha,ite_true]
      by_cases hv : pick R ∈ I
      · simp only [hv,ite_true,List.mem_cons]
        intro v h
        rcases h with rfl|h
        · exact hv
        · exact ih _ _ h
      · simp only [hv,ite_false]
        exact ih _
    · simp [run,ha]

/--
---
conclusion: Lax342547.ContainerRun.run_replay
---
-/
theorem run_replay {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) :
    replay active pick H fuel R (run active pick H I fuel R).2 = (run active pick H I fuel R).1 := by
  classical
  induction fuel generalizing R with
  | zero => rfl
  | succ n ih =>
    by_cases ha : active R
    · by_cases hv : pick R ∈ I
      · simpa [run,replay,ha,hv,next] using ih (next H I R (pick R))
      · have hhead : (run active pick H I n (next H I R (pick R))).2.head? ≠ some (pick R) := by
          intro hh
          have hm : pick R ∈ (run active pick H I n (next H I R (pick R))).2 := by
            cases he : (run active pick H I n (next H I R (pick R))).2 with
            | nil => simp [he] at hh
            | cons a l =>
              have heq : a = pick R := by simpa [he] using hh
              simp [heq]
          exact hv (Lax342547.ContainerRun.recorded_subset active pick H I _ n _ hm)
        have hhead' : (run active pick H I n (R.erase (pick R))).2.head? ≠ some (pick R) := by
          simpa [next,hv] using hhead
        simpa [run,replay,ha,hv,next,hhead'] using ih (next H I R (pick R))
    · simp [run,replay,ha]

/--
---
conclusion: Lax342547.ContainerRun.run_preserves
---
-/
theorem run_preserves {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ)
    (hI : I ⊆ R) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H x y) :
    I ⊆ (run active pick H I fuel R).1 ∧ (run active pick H I fuel R).1 ⊆ R := by
  classical
  induction fuel generalizing R with
  | zero => exact ⟨hI,Finset.Subset.refl _⟩
  | succ n ih =>
    by_cases ha : active R
    · have hh := ih (next H I R (pick R)) (Lax342547.ContainerRun.next_preserves H I R (pick R) hI hind)
      simp only [run,ha,ite_true]
      exact ⟨hh.1,Finset.Subset.trans hh.2 (Lax342547.ContainerRun.next_subset H I R (pick R))⟩
    · simpa [run,ha] using And.intro hI (Finset.Subset.refl R)

/--
---
conclusion: Lax342547.ContainerRun.run_terminal
---
-/
theorem run_terminal {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ)
    (hpick : ∀ T, active T → pick T ∈ T ∧ ∃ w ∈ T, H (pick T) w)
    (hsize : R.card < fuel) : ¬ active (run active pick H I fuel R).1 := by
  classical
  induction fuel generalizing R with
  | zero => omega
  | succ n ih =>
    by_cases ha : active R
    · have hc := Lax342547.ContainerRun.next_card_lt H I R (pick R) (hpick R ha).1 (hpick R ha).2
      have hh := ih (next H I R (pick R)) (by omega)
      simpa [run,ha] using hh
    · simp [run,ha]


/--
---
conclusion: Lax342547.ContainerRun.run_entropy_budget
---
-/
theorem run_entropy_budget {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ) (E : Finset U → ℝ) (B δ : ℝ)
    (hδ : 0 ≤ δ) (hb : ∀ T, active T → E T ≤ B)
    (hstep : by
      classical
      exact ∀ T, active T → active (next H I T (pick T)) →
        E T + (if pick T ∈ I then δ else 0) ≤ E (next H I T (pick T)))
    (hR : active R) :
    (((run active pick H I fuel R).2.length : ℝ)-1)*δ ≤ B-E R := by
  classical
  induction fuel generalizing R with
  | zero =>
    simp only [run,List.length_nil,Nat.cast_zero,zero_sub,neg_one_mul]
    linarith [hb R hR]
  | succ n ih =>
    let T := next H I R (pick R)
    by_cases hT : active T
    · have hh := ih T hT
      have hs := hstep R hR hT
      by_cases hv : pick R ∈ I
      · simp only [run,hR,ite_true,hv,List.length_cons,Nat.cast_add,Nat.cast_one]
        simp only [hv,ite_true] at hs
        change (((run active pick H I n T).2.length : ℝ)+1-1)*δ ≤ B-E R
        nlinarith
      · simp only [run,hR,ite_true,hv,ite_false]
        simp only [hv,ite_false,add_zero] at hs
        exact hh.trans (sub_le_sub_left hs B)
    · have hempty : (run active pick H I n T).2 = [] := by
        cases n <;> simp [run,hT]
      simp only [run,hR,ite_true]
      change (((if pick R ∈ I then pick R::(run active pick H I n T).2
        else (run active pick H I n T).2).length : ℝ)-1)*δ ≤ B-E R
      rw [hempty]
      split_ifs <;> simp only [List.length_nil,List.length_cons,zero_add,Nat.cast_zero,Nat.cast_one]
      · linarith [hb R hR]
      · linarith [hb R hR]

end Lax342547Proofs.ContainerRun

