import Lax793645Proofs.Simplifications.ClippedExposure

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {S X : Type*} [Fintype S] [Fintype X]

def forecast (π : Wgt S) (K : S → Wgt X) : Wgt X := mixW π K

/-- Bayes update; an impossible observation leaves the prior unchanged. -/
def bayes (π : Wgt S) (K : S → Wgt X) (y : X) : Wgt S := by
  classical
  exact if forecast π K y=0 then π else normW (fun s => π s*K s y)

theorem forecast_law {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) : IsLaw (forecast π K) := mixW_law hπ hK

theorem bayes_law {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (y : X) : IsLaw (bayes π K y) := by
  classical
  unfold bayes
  split_ifs with hz
  · exact hπ
  · apply normW_law (fun s => mul_nonneg (hπ.nz s) ((hK s).nz y))
    change 0 < forecast π K y
    exact lt_of_le_of_ne ((forecast_law hπ hK).nz y) (Ne.symm hz)

theorem bayes_weight {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (y : X) (s : S) :
    forecast π K y*bayes π K y s=π s*K s y := by
  classical
  unfold bayes
  split_ifs with hz
  · have ht : π s*K s y ≤ forecast π K y :=
      Finset.single_le_sum (fun z _ => mul_nonneg (hπ.nz z) ((hK z).nz y)) (Finset.mem_univ s)
    have hn := mul_nonneg (hπ.nz s) ((hK s).nz y)
    rw [hz] at ht ⊢
    linarith
  · change forecast π K y * ((π s*K s y)/forecast π K y)=_
    exact mul_div_cancel₀ _ hz

def nextJoint (π : Wgt S) (K : S → Wgt X) (y x : X) : ℝ :=
  avg π (fun s => K s y*K s x)

theorem nextJoint_nonneg {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (y x : X) : 0 ≤ nextJoint π K y x :=
  avg_nonneg hπ.nz fun s => mul_nonneg ((hK s).nz y) ((hK s).nz x)

theorem nextJoint_row (π : Wgt S) {K : S → Wgt X} (hK : ∀ s, IsLaw (K s)) (y : X) :
    (∑ x, nextJoint π K y x)=forecast π K y := by
  unfold nextJoint
  rw [← avg_sum]
  simp only [← Finset.mul_sum]
  change avg π (fun s => K s y*tot (K s))=forecast π K y
  simp only [(hK _).total,mul_one]
  rfl

theorem nextJoint_col (π : Wgt S) {K : S → Wgt X} (hK : ∀ s, IsLaw (K s)) (x : X) :
    (∑ y, nextJoint π K y x)=forecast π K x := by
  simp only [nextJoint,mul_comm (K _ _) (K _ x)]
  exact nextJoint_row π hK x

theorem bayes_forecast {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (y x : X) :
    forecast π K y*forecast (bayes π K y) K x=nextJoint π K y x := by
  change forecast π K y*(∑ s, bayes π K y s*K s x)=∑ s, π s*(K s y*K s x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← mul_assoc,bayes_weight hπ hK]
  ring

theorem bayes_posterior {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (y : X) (hy : forecast π K y ≠ 0) :
    forecast (bayes π K y) K = posterior (nextJoint π K) (forecast π K) y := by
  funext x
  apply (eq_div_iff hy).mpr
  simpa [mul_comm] using bayes_forecast hπ hK y x

theorem bayes_average {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (f : Wgt S) :
    avg (forecast π K) (fun y => avg (bayes π K y) f)=avg π f := by
  unfold avg
  simp_rw [Finset.mul_sum,← mul_assoc,bayes_weight hπ hK]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [← Finset.sum_mul,← Finset.mul_sum]
  change π s*tot (K s)*f s=π s*f s
  rw [(hK s).total,mul_one]

def historyState (π : Wgt S) (K : S → Wgt X) : List X → Wgt S
  | [] => π
  | y::h => bayes (historyState π K h) K y

theorem historyState_law {π : Wgt S} {K : S → Wgt X} (hπ : IsLaw π)
    (hK : ∀ s, IsLaw (K s)) (h : List X) : IsLaw (historyState π K h) := by
  induction h with
  | nil => exact hπ
  | cons y h ih => exact bayes_law ih hK y

theorem forecast_exposure (q : Wgt X) (π : Wgt S) (K : S → Wgt X)
    (hq : IsLaw q) (hπ : IsLaw π) (hK : ∀ s, IsLaw (K s))
    (C : X → X → Prop) (hzero : ∀ s y x, C y x → K s y*K s x=0)
    (A : X → Prop) (γ κ : ℝ) (hγ : 0 ≤ γ)
    (b : ℕ) (hb : 0 < b) (hκ : κ ≤ (2:ℝ)^b*γ)
    (hcap : ∀ x, A x → forecast π K x ≤ κ*q x) :
    (retainedConflict (forecast π K) A C-γ)/2 ≤
      clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) (forecast π K) -
      avg (forecast π K) (fun y => clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ)
        (forecast (bayes π K y) K)) := by
  have hz (y x : X) (h : C y x) : nextJoint π K y x=0 := by
    simp only [nextJoint,hzero _ y x h,avg_zero]
  have he := retained_exposure_joint q (forecast π K) (nextJoint π K)
    hq (forecast_law hπ hK) (nextJoint_nonneg hπ hK) (nextJoint_row π hK)
    (nextJoint_col π hK) C hz A γ κ hγ b hb hκ hcap
  have ha : avg (forecast π K)
      (clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) ∘ posterior (nextJoint π K) (forecast π K)) =
      avg (forecast π K) (fun y => clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ)
        (forecast (bayes π K y) K)) := by
    apply avg_congr
    intro y hy
    rw [bayes_posterior hπ hK y hy]
    rfl
  rwa [ha] at he

theorem forecast_drop_nonneg {I : Type*} [Fintype I]
    (q : Wgt X) (a : I → ℝ) {π : Wgt S} {K : S → Wgt X}
    (hπ : IsLaw π) (hK : ∀ s, IsLaw (K s)) :
    0 ≤ clippedPotential q a (forecast π K)-
      avg (forecast π K) (fun y => clippedPotential q a (forecast (bayes π K y) K)) := by
  apply sub_nonneg.mpr
  unfold clippedPotential
  rw [avg_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [avg_sum]
  apply Finset.sum_le_sum
  intro x _
  exact clipped_coordinate_jensen (forecast π K) (fun y => forecast (bayes π K y) K)
    (forecast_law hπ hK) (fun x => bayes_average hπ hK (fun s => K s x)) x (a i*q x)

/-- A finite tree telescope. The bad-sample probability is a martingale under
the original posterior laws, so it is never necessary to condition on goodness. -/
theorem tree_budget (law : List X → Wgt X) (hlaw : ∀ h, IsLaw (law h))
    (V B : List X → ℝ) (hV : ∀ h, 0 ≤ V h) (δ C : ℝ) (L : ℕ)
    (hB : ∀ h, avg (law h) (fun y => B (y::h))=B h)
    (hstep : ∀ h, h.length < L →
      δ-C*B h ≤ V h-avg (law h) (fun y => V (y::h))) :
    (L:ℝ)*(δ-C*B []) ≤ V [] := by
  have hi : ∀ r h, h.length+r ≤ L → (r:ℝ)*(δ-C*B h) ≤ V h := by
    intro r
    induction r with
    | zero => intro h hh; simpa using hV h
    | succ r ih =>
      intro h hh
      have ha := avg_mono (hlaw h).nz (fun y => ih (y::h) (by simp only [List.length_cons]; omega))
      have he : avg (law h) (fun y => (r:ℝ)*(δ-C*B (y::h))) =
          (r:ℝ)*(δ-C*B h) := by
        rw [avg_mul',avg_sub,(hlaw h).avg_const,avg_mul',hB]
      rw [he] at ha
      have hs := hstep h (by omega)
      push_cast
      linarith
  exact hi L [] (by simp)

/-- All possible histories, including prefixes. The bound avoids a separate
factor for the number of exposure stages. -/
def shortHistories [DecidableEq X] : ℕ → Finset (List X)
  | 0 => {[]}
  | n+1 => insert [] (Finset.univ.biUnion (fun y => (shortHistories n).image (List.cons y)))

theorem mem_shortHistories [DecidableEq X] (h : List X) (n : ℕ) :
    h ∈ shortHistories n ↔ h.length ≤ n := by
  induction n generalizing h with
  | zero => simp [shortHistories]
  | succ n ih =>
    cases h with
    | nil => simp [shortHistories]
    | cons y h => simp [shortHistories,ih]

theorem card_shortHistories [DecidableEq X] (n : ℕ) :
    (shortHistories (X:=X) n).card ≤ (Fintype.card X+1)^n := by
  induction n with
  | zero => simp [shortHistories]
  | succ n ih =>
    have hn : 1 ≤ (shortHistories (X:=X) n).card :=
      Finset.one_le_card.mpr ⟨[], (mem_shortHistories [] n).mpr (by simp)⟩
    calc
      (shortHistories (X:=X) (n+1)).card ≤
          (Finset.univ.biUnion (fun y : X => (shortHistories n).image (List.cons y))).card+1 :=
        Finset.card_insert_le _ _
      _ ≤ (∑ _y : X, (shortHistories (X:=X) n).card)+1 := by
        gcongr
        exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
      _ ≤ (Fintype.card X+1)*(shortHistories (X:=X) n).card := by simp; nlinarith
      _ ≤ (Fintype.card X+1)*(Fintype.card X+1)^n := Nat.mul_le_mul_left _ ih
      _ = (Fintype.card X+1)^(n+1) := by rw [pow_succ, Nat.mul_comm]

end
end Lax793645Proofs.Simplifications
