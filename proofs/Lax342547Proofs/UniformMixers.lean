import Lax342547.UniformMixers
import Lax342547.BinaryMixers
import Lax342547.UnaryMixers

namespace Lax342547Proofs.UniformMixers

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw
open Lax342547.UniformMixers
open scoped ENNReal

theorem exists_of_bad_lt_one {Ω : Type} (p : PMF Ω) (P : Ω → Prop)
    (h : p.toOuterMeasure {x | ¬ P x} < 1) : ∃ x, P x := by
  by_contra hnone
  have hall : ∀ x, ¬ P x := not_exists.mp hnone
  have heq : {x | ¬ P x} = Set.univ := by ext x; simp [hall]
  rw [heq] at h
  simp only [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe, lt_self_iff_false] at h

theorem constant_ratio_lt_one (C n : ℕ) (hC : C ≤ n) : (C : ℝ≥0∞) / 2 ^ n < 1 := by
  apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))).mpr
  rw [one_mul]
  exact_mod_cast hC.trans_lt n.lt_two_pow_self

/--
---
conclusion: Lax342547.UniformMixers.exists_uniform_mixers
---
The unary and indexed-binary bad events share the same matrix-family
probability space. Their sum is at most (C_unary+C_binary)/2^n<1 above
the stated threshold. Choose a family outside their union, then choose
sharp matrices outside their own bad event. Restriction to the always
retained blocks supplies every flavor's binary bound for these choices.
-/
theorem exists_uniform_mixers (k b degree J K s₀ : ℕ) (hk : 0 < k) (hd : 1 ≤ degree)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀)
    (n : ℕ) (hn : threshold k b degree J K s₀ ≤ n)
    (r₀ : ℕ) (hr : 2 * r₀ ≤ n) (D : Testers (k := k) (b := b) (degree := degree) hr) :
    ∃ L : Index (Component (Tag k)) J → Moment k n b degree,
      ∃ M : Fin b → Matrix (Fin n) (Fin n) Binary,
        Lax342547.UnaryMixers.UniformUnary D K s₀ L ∧
          Lax342547.BinaryMixers.UniformBinary hr hd L M := by
  classical
  let F := Index (Component (Tag k)) J
  let p := PMF.uniformOfFintype (F → Moment k n b degree)
  let C := Lax342547.UnaryMixers.threshold k b degree J K s₀
  let B := 2 ^ (2 * b + 2 * Fintype.card F)
  have hn50 : 50 ≤ n := (le_max_left _ _).trans hn
  have hCB : C + B ≤ n := by
    have h := (le_max_right _ _).trans hn
    change C + B + 2 ^ (2 * b + 2) ≤ n at h
    exact (Nat.le_add_right _ _).trans h
  have hsharp : 2 ^ (2 * b + 2) ≤ n := by
    have h := (le_max_right _ _).trans hn
    change C + B + 2 ^ (2 * b + 2) ≤ n at h
    exact (Nat.le_add_left _ _).trans h
  have hu := (Lax342547.UnaryMixers.simultaneous_failure_bound (J := J) (K := K) hk D s₀).trans
    (Lax342547.UnaryMixers.failureBound_le_geometric k n b degree J K s₀ hmargin)
  have hb := Lax342547.BinaryMixers.mixer_failure_bound (k := k) (b := b) (F := F) hd hn50
  have hjoint : p.toOuterMeasure {L | ¬ (Lax342547.UnaryMixers.Good D K s₀ L ∧
      Lax342547.BinaryMixers.MixerGood L)} < 1 := by
    have heq : {L : F → Moment k n b degree | ¬ (Lax342547.UnaryMixers.Good D K s₀ L ∧
        Lax342547.BinaryMixers.MixerGood L)} =
        {L | ¬ Lax342547.UnaryMixers.Good D K s₀ L} ∪ {L | ¬ Lax342547.BinaryMixers.MixerGood L} := by
      ext L
      change ¬ (_ ∧ _) ↔ ¬ _ ∨ ¬ _
      exact not_and_or
    rw [heq]
    calc
      _ ≤ p.toOuterMeasure {L | ¬ Lax342547.UnaryMixers.Good D K s₀ L} +
          p.toOuterMeasure {L | ¬ Lax342547.BinaryMixers.MixerGood L} :=
        MeasureTheory.measure_union_le _ _
      _ ≤ (C : ℝ≥0∞) / 2 ^ n + (B : ℝ≥0∞) / 2 ^ n := by
        apply add_le_add hu
        simpa only [Lax342547.BinaryMixers.failureBound, B, Nat.cast_pow, Nat.cast_ofNat] using hb
      _ = ((C + B : ℕ) : ℝ≥0∞) / 2 ^ n := by rw [Nat.cast_add, ENNReal.add_div]
      _ < 1 := constant_ratio_lt_one _ _ hCB
  obtain ⟨L, hLu, hLb⟩ := exists_of_bad_lt_one p _ hjoint
  have hs := Lax342547.BinaryMixers.sharp_failure_bound (b := b) hn50
  have hslt : (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | ¬ Lax342547.BinaryMixers.SharpGood M} < 1 := by
    apply hs.trans_lt
    simpa only [Lax342547.BinaryMixers.failureBound, mul_one, Nat.cast_pow, Nat.cast_ofNat] using
      constant_ratio_lt_one _ _ hsharp
  obtain ⟨M, hM⟩ := exists_of_bad_lt_one _ _ hslt
  exact ⟨L, M, Lax342547.UnaryMixers.uniform_of_good D L hLu,
    Lax342547.BinaryMixers.uniform_of_restrictions hr hd L M hLb hM⟩

/--
---
conclusion: Lax342547.UniformMixers.paper_parameters
---
All factors in the paper's displayed A are natural numbers, so 4⌈A⌉
is 40(K+1)p_*(g²+5). This exceeds the profile-count slope. Taking J to
be 101(s₀+K²+1) gives the paper's strict mixer-budget inequality.
-/
theorem paper_parameters (k b degree K : ℕ) :
    (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ paperS₀ k b degree K ∧
      100 * (paperS₀ k b degree K + K ^ 2 + 1) < paperJ k b degree K := by
  constructor
  · let p := ∑ j ∈ Finset.range (degree + 1), b.choose j
    have h : p * ((2 * k + 1) ^ 2 + 3) * K ≤ p * ((2 * k + 1) ^ 2 + 5) * (K + 1) := by
      gcongr <;> omega
    refine h.trans ?_
    change p * ((2 * k + 1) ^ 2 + 5) * (K + 1) ≤ 40 * (K + 1) * p * ((2 * k + 1) ^ 2 + 5)
    calc
      _ ≤ 40 * (p * ((2 * k + 1) ^ 2 + 5) * (K + 1)) := Nat.le_mul_of_pos_left _ (by decide)
      _ = _ := by ring
  · unfold paperJ
    omega

/--
---
conclusion: Lax342547.UniformMixers.exists_paper_mixers
---
Instantiate the simultaneous theorem with the paper's mixer parameters.
For every sufficiently large n it supplies all unary row-space and
polar-rank conclusions and every ordered binary parity bound, before
any unit law is quantified over.
-/
theorem exists_paper_mixers (k b degree K : ℕ) (hk : 0 < k) (hd : 1 ≤ degree) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ L : Index (Component (Tag k)) (paperJ k b degree K) → Moment k n b degree,
        ∃ M : Fin b → Matrix (Fin n) (Fin n) Binary,
          Lax342547.UnaryMixers.UniformUnary D K (paperS₀ k b degree K) L ∧
            Lax342547.BinaryMixers.UniformBinary hr hd L M := by
  refine ⟨threshold k b degree (paperJ k b degree K) K (paperS₀ k b degree K), ?_⟩
  intro n hn r₀ hr D
  exact Lax342547.UniformMixers.exists_uniform_mixers k b degree (paperJ k b degree K) K (paperS₀ k b degree K)
    hk hd (Lax342547.UniformMixers.paper_parameters k b degree K).1 n hn r₀ hr D

end Lax342547Proofs.UniformMixers
