import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Tactic

/-! Finite clipped-probability potential. The posterior mixture identity and the
zero posterior on conflicts are explicit hypotheses; no conditioning on a good
sample event is hidden in the statement. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {X I : Type*} [Fintype X] [Fintype I]

def clippedPotential (q : Wgt X) (a : I → ℝ) (σ : Wgt X) : ℝ :=
  ∑ i, ∑ x, min (σ x) (a i * q x)

theorem clippedPotential_bounds (q σ : Wgt X) (a : I → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hσ : IsLaw σ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ clippedPotential q a σ ∧ clippedPotential q a σ ≤ Fintype.card I := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun x _ =>
      le_min (hσ.nz x) (mul_nonneg (ha i) (hq x))
  · calc
      clippedPotential q a σ ≤ ∑ _i : I, ∑ x, σ x :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = Fintype.card I := by change (∑ _i : I, tot σ) = _; simp [hσ.total]

theorem clipped_coordinate_jensen (σ : Wgt X) (τ : X → Wgt X) (hσ : IsLaw σ)
    (hmean : ∀ x, avg σ (fun y => τ y x) = σ x) (x : X) (c : ℝ) :
    avg σ (fun y => min (τ y x) c) ≤ min (σ x) c := by
  apply le_min
  · exact (avg_mono hσ.nz fun y => min_le_left (τ y x) c).trans_eq (hmean x)
  · exact (avg_mono hσ.nz fun y => min_le_right (τ y x) c).trans_eq
      (hσ.avg_const c)

theorem clipped_coordinate_drop (σ : Wgt X) (τ : X → Wgt X) (hσ : IsLaw σ)
    (C : X → X → Prop) (hkill : ∀ y x, C y x → τ y x = 0)
    (x : X) (c : ℝ) (hc : 0 ≤ c) (hcx : c ≤ σ x) :
    c * pr σ (fun y => C y x) ≤
      min (σ x) c - avg σ (fun y => min (τ y x) c) := by
  have hpoint (y : X) : min (τ y x) c ≤ (1-ind (C y x))*c := by
    by_cases h : C y x
    · rw [hkill y x h, ind_one h, min_eq_left hc]; ring_nf; exact le_rfl
    · rw [ind_zero h]; simp
  have he := avg_mono hσ.nz hpoint
  have heq : avg σ (fun y => (1-ind (C y x))*c) =
      c - c * pr σ (fun y => C y x) := by
    simp only [avg, pr, sub_mul, one_mul, mul_sub, Finset.sum_sub_distrib,
      ← mul_assoc, ← Finset.sum_mul]
    have ht : ∑ y, σ y = 1 := hσ.total
    rw [ht]
    ring
  rw [heq] at he
  rw [min_eq_right hcx]
  linarith

/-- Threshold coverage is the only fact needed about the dyadic scales. The
conclusion even counts conflicts with all first units, rather than only retained
first units. Thus it implies the proposed bound for `conflict ∩ A²`. -/
theorem clipped_exposure (q σ : Wgt X) (a : I → ℝ) (τ : X → Wgt X)
    (hq : IsLaw q) (hσ : IsLaw σ) (ha : ∀ i, 0 ≤ a i)
    (hmean : ∀ x, avg σ (fun y => τ y x) = σ x)
    (C : X → X → Prop) (hkill : ∀ y x, C y x → τ y x = 0)
    (A : X → Prop) (γ κ : ℝ) (hγ : 0 ≤ γ)
    (hcap : ∀ x, A x → σ x ≤ κ*q x)
    (hcover : ∀ x, γ*q x ≤ σ x → σ x ≤ κ*q x →
      ∃ i, a i*q x ≤ σ x ∧ σ x ≤ 2*(a i*q x)) :
    (∑ x, σ x * ind (A x) * pr σ (fun y => C y x)) - γ ≤
      2*(clippedPotential q a σ - avg σ (clippedPotential q a ∘ τ)) := by
  classical
  let gap (i : I) (x : X) := min (σ x) (a i*q x) -
    avg σ (fun y => min (τ y x) (a i*q x))
  have hn (i : I) (x : X) : 0 ≤ gap i x :=
    sub_nonneg.mpr (clipped_coordinate_jensen σ τ hσ hmean x (a i*q x))
  have hp (x : X) : 0 ≤ pr σ (fun y => C y x) := pr_nonneg hσ.nz
  have hp1 (x : X) : pr σ (fun y => C y x) ≤ 1 :=
    (pr_le_tot hσ.nz).trans_eq hσ.total
  have hpoint (x : X) : σ x * ind (A x) * pr σ (fun y => C y x) ≤
      2*(∑ i, gap i x) + γ*q x := by
    by_cases hx : A x
    · rw [ind_one hx, mul_one]
      by_cases hlo : γ*q x ≤ σ x
      · obtain ⟨i, hi, hi2⟩ := hcover x hlo (hcap x hx)
        have hdrop := clipped_coordinate_drop σ τ hσ C hkill x (a i*q x)
          (mul_nonneg (ha i) (hq.nz x)) hi
        have hs : gap i x ≤ ∑ j, gap j x :=
          Finset.single_le_sum (fun j _ => hn j x) (Finset.mem_univ i)
        have hm := mul_le_mul_of_nonneg_right hi2 (hp x)
        have hqg := mul_nonneg hγ (hq.nz x)
        change _ ≤ gap i x at hdrop
        nlinarith
      · have hm := mul_le_mul_of_nonneg_left (hp1 x) (hσ.nz x)
        have hs : 0 ≤ ∑ i, gap i x := Finset.sum_nonneg fun i _ => hn i x
        linarith
    · rw [ind_zero hx, mul_zero, zero_mul]
      exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hn i x))
        (mul_nonneg hγ (hq.nz x))
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  have hg : (∑ x, ∑ i, gap i x) =
      clippedPotential q a σ - avg σ (clippedPotential q a ∘ τ) := by
    rw [Finset.sum_comm]
    change (∑ i, ∑ x, gap i x) = clippedPotential q a σ -
      avg σ (fun y => ∑ i, ∑ x, min (τ y x) (a i*q x))
    simp only [gap, Finset.sum_sub_distrib, clippedPotential,
      avg_sum]
  have ht : ∑ x, q x = 1 := hq.total
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ht, mul_one, hg] at hs
  linarith

/-- The arithmetic conversion from retained mass to an average potential drop. -/
theorem exposure_drop_from_retention {ε α D : ℝ} (hε : 0 ≤ ε)
    (hα : α ≤ 1) (hD : 0 ≤ D) (hlarge : 1/4 ≤ α → ε/64 ≤ D) :
    ε/48*(α-1/4) ≤ D := by
  by_cases h : 1/4 ≤ α
  · have := hlarge h
    nlinarith
  · have : ε/48*(α-1/4) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    exact this.trans hD

/-- A finite telescoping obstruction: bounded potential cannot fund this many
steps at a fixed positive average price. -/
theorem exposure_budget (V : ℕ → ℝ) (L : ℕ) (b δ : ℝ)
    (hstart : V 0 ≤ b) (hend : 0 ≤ V L)
    (hstep : ∀ t < L, δ ≤ V t - V (t+1)) : (L:ℝ)*δ ≤ b := by
  have hsum : ∀ t ≤ L, (t:ℝ)*δ ≤ V 0 - V t := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have hi := ih (by omega)
      have hs := hstep t (by omega)
      push_cast
      nlinarith
  have := hsum L le_rfl
  linarith

/-- Dyadic coverage, including endpoints of the intervals. -/
theorem dyadic_bracket (γ x : ℝ) (b : ℕ) (hb : 0 < b)
    (hlo : γ ≤ x) (hhi : x ≤ (2:ℝ)^b*γ) :
    ∃ i : Fin b, (2:ℝ)^i.val*γ ≤ x ∧ x ≤ 2*((2:ℝ)^i.val*γ) := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hz : b=0
    · subst b
      refine ⟨0, ?_, ?_⟩
      · simpa using hlo
      · simpa using hhi
    · by_cases hm : x ≤ (2:ℝ)^b*γ
      · obtain ⟨i, hi, hi'⟩ := ih (by omega) hm
        exact ⟨i.castSucc, hi, hi'⟩
      · refine ⟨Fin.last b, (le_of_not_ge hm), ?_⟩
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi

def posterior (P : X → X → ℝ) (σ : Wgt X) (y x : X) : ℝ := P y x / σ y

theorem posterior_mixture (P : X → X → ℝ) (σ : Wgt X)
    (hP : ∀ y x, 0 ≤ P y x) (hrow : ∀ y, ∑ x, P y x = σ y)
    (hcol : ∀ x, ∑ y, P y x = σ x) :
    ∀ x, avg σ (fun y => posterior P σ y x) = σ x := by
  intro x
  rw [avg]
  calc
    (∑ y, σ y * posterior P σ y x) = ∑ y, P y x := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hz : σ y=0
      · have hle := Finset.single_le_sum (fun j _ => hP y j) (Finset.mem_univ x)
        rw [hrow y, hz] at hle
        have hp0 : P y x=0 := le_antisymm hle (hP y x)
        simp [posterior, hz, hp0]
      · exact mul_div_cancel₀ (P y x) hz
    _ = σ x := hcol x

/-- The proposed finite lemma, now starting with the joint table rather than
assuming the conditional-law identity. The joint need not be independent or
pointwise symmetric; equal marginals are enough. -/
theorem dyadic_exposure_joint (q σ : Wgt X) (P : X → X → ℝ)
    (hq : IsLaw q) (hσ : IsLaw σ)
    (hP : ∀ y x, 0 ≤ P y x) (hrow : ∀ y, ∑ x, P y x = σ y)
    (hcol : ∀ x, ∑ y, P y x = σ x)
    (C : X → X → Prop) (hzero : ∀ y x, C y x → P y x = 0)
    (A : X → Prop) (γ κ : ℝ) (hγ : 0 ≤ γ)
    (b : ℕ) (hb : 0 < b) (hκ : κ ≤ (2:ℝ)^b*γ)
    (hcap : ∀ x, A x → σ x ≤ κ*q x) :
    (∑ x, σ x * ind (A x) * pr σ (fun y => C y x)) - γ ≤
      2*(clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) σ -
        avg σ (clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) ∘ posterior P σ)) := by
  apply clipped_exposure q σ _ _ hq hσ (fun i => by positivity)
    (posterior_mixture P σ hP hrow hcol) C
    (fun y x h => by simp [posterior, hzero y x h]) A γ κ hγ hcap
  intro x hlo hhi
  have hi : σ x ≤ (2:ℝ)^b*(γ*q x) := by
    have hm := mul_le_mul_of_nonneg_right hκ (hq.nz x)
    nlinarith
  obtain ⟨i, hl, hu⟩ := dyadic_bracket (γ*q x) (σ x) b hb hlo hi
  exact ⟨i, by simpa [mul_assoc] using hl, by simpa [mul_assoc] using hu⟩

def retainedConflict (σ : Wgt X) (A : X → Prop) (C : X → X → Prop) : ℝ :=
  ∑ x, ∑ y, σ x*σ y*ind (A x ∧ A y ∧ C y x)

theorem retainedConflict_le (σ : Wgt X) (hσ : ∀ x, 0 ≤ σ x)
    (A : X → Prop) (C : X → X → Prop) :
    retainedConflict σ A C ≤ ∑ x, σ x*ind (A x)*pr σ (fun y => C y x) := by
  unfold retainedConflict pr avg
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have h := mul_le_mul_of_nonneg_left
    (ind_mono (fun h : A x ∧ A y ∧ C y x => And.intro h.1 h.2.2))
    (mul_nonneg (hσ x) (hσ y))
  simp only [ind_and] at h ⊢
  convert h using 1
  ring

/-- Precisely the displayed conflict-on-A² inequality in the proposal. -/
theorem retained_exposure_joint (q σ : Wgt X) (P : X → X → ℝ)
    (hq : IsLaw q) (hσ : IsLaw σ)
    (hP : ∀ y x, 0 ≤ P y x) (hrow : ∀ y, ∑ x, P y x = σ y)
    (hcol : ∀ x, ∑ y, P y x = σ x)
    (C : X → X → Prop) (hzero : ∀ y x, C y x → P y x = 0)
    (A : X → Prop) (γ κ : ℝ) (hγ : 0 ≤ γ)
    (b : ℕ) (hb : 0 < b) (hκ : κ ≤ (2:ℝ)^b*γ)
    (hcap : ∀ x, A x → σ x ≤ κ*q x) :
    (retainedConflict σ A C-γ)/2 ≤
      clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) σ -
        avg σ (clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) ∘ posterior P σ) := by
  have h := dyadic_exposure_joint q σ P hq hσ hP hrow hcol C hzero A γ κ hγ b hb hκ hcap
  have hr := retainedConflict_le σ hσ.nz A C
  linarith

end
end Lax793645Proofs.Simplifications
