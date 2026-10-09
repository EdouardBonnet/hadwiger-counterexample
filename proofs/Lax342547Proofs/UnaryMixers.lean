import Lax342547.UnaryMixers
import Lax342547Proofs.UnaryRowLaw
import Lax342547Proofs.CoordinateCounts

namespace Lax342547Proofs.UnaryMixers

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw Lax342547.UnaryMixers
open scoped ENNReal

theorem test_count_le (k n b degree K : ℕ) :
    Fintype.card (Test k n b degree K) ≤ testCountBound k n b degree K := by
  classical
  have hc := ProfileCounting.card_concrete_profiles k n b degree K
  rw [← Nat.card_eq_fintype_card, Test, Nat.card_prod, Nat.card_prod]
  have htag : Nat.card (Tag k) = 2 * k + 1 := by
    rw [Nat.card_eq_fintype_card]
    simp [Tag]
  have hlabel : Nat.card (Fin b → Binary) = 2 ^ b := by
    rw [Nat.card_eq_fintype_card]
    simp [Binary]
  rw [htag, hlabel]
  calc
    _ ≤ ((K + 1) ^ Fintype.card (Component (Tag k)) *
        2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K)) * ((2 * k + 1) * 2 ^ b) :=
      Nat.mul_le_mul_right _ hc
    _ = _ := by unfold testCountBound; ring

theorem bad_eq_union {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (s₀ : ℕ) :
    {M : Index (Component (Tag k)) J → Moment k n b degree | ¬ Good D K s₀ M} =
      ⋃ t : Test k n b degree K, {M | t.1.val ≠ 0 ∧ UnaryBad D t.1.val t.2.1 t.2.2 s₀ M} := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Good]
  constructor
  · intro h
    push Not at h
    obtain ⟨x, hx, hK, l, s, hbad⟩ := h
    exact ⟨(⟨x, hK⟩, l, s), hx, hbad⟩
  · rintro ⟨⟨x, l, s⟩, hx, hbad⟩ h
    exact h x.val hx x.property l s hbad

/--
---
conclusion: Lax342547.UnaryMixers.simultaneous_failure_bound
---
Take the finite union over the actual low-rank profile space, tags,
and labels. The profile-count bound controls the number of tests, and
each event already includes every fixing of the non-Z coordinates.
-/
theorem simultaneous_failure_bound {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr) (s₀ : ℕ) :
    (PMF.uniformOfFintype (Index (Component (Tag k)) J → Moment k n b degree)).toOuterMeasure
      {M | ¬ Good D K s₀ M} ≤ failureBound k n b degree J K s₀ := by
  classical
  let p := PMF.uniformOfFintype (Index (Component (Tag k)) J → Moment k n b degree)
  let B : ℝ≥0∞ :=
    2 ^ (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)) / 2 ^ ((s₀ + 1) * n)
  have htest (t : Test k n b degree K) :
      p.toOuterMeasure {M | t.1.val ≠ 0 ∧ UnaryBad D t.1.val t.2.1 t.2.2 s₀ M} ≤ B := by
    by_cases hx : t.1.val = 0
    · simp [hx]
    · simpa only [hx, ne_eq, not_false_eq_true, true_and] using
        UnaryRowLaw.unary_failure_probability (J := J) hk D t.1.val hx t.1.property t.2.1 t.2.2 s₀
  rw [bad_eq_union]
  calc
    _ ≤ ∑ t : Test k n b degree K,
        p.toOuterMeasure {M | t.1.val ≠ 0 ∧ UnaryBad D t.1.val t.2.1 t.2.2 s₀ M} :=
      MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure _
    _ ≤ ∑ _t : Test k n b degree K, B := Finset.sum_le_sum (fun t _ => htest t)
    _ = (Fintype.card (Test k n b degree K) : ℝ≥0∞) * B := by simp
    _ ≤ (testCountBound k n b degree K : ℝ≥0∞) * B :=
      mul_le_mul_left (by exact_mod_cast test_count_le k n b degree K) B
    _ = failureBound k n b degree J K s₀ := rfl

/--
---
conclusion: Lax342547.UnaryMixers.exists_of_failureBound_lt_one
---
If every mixer choice failed, the bad event would be the whole finite
probability space and would have mass one. The explicit union bound
below one therefore leaves a simultaneous successful choice.
-/
theorem exists_of_failureBound_lt_one {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr) (s₀ : ℕ)
    (hsmall : failureBound k n b degree J K s₀ < 1) :
    ∃ M : Index (Component (Tag k)) J → Moment k n b degree, Good D K s₀ M := by
  classical
  by_contra hn
  have hall : ∀ M : Index (Component (Tag k)) J → Moment k n b degree, ¬ Good D K s₀ M :=
    not_exists.mp hn
  have h := simultaneous_failure_bound (J := J) (K := K) hk D s₀
  have heq : {M : Index (Component (Tag k)) J → Moment k n b degree | ¬ Good D K s₀ M} = Set.univ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hall M
  rw [heq] at h
  simp only [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe] at h
  exact (not_lt_of_ge h) hsmall

/--
---
conclusion: Lax342547.UnaryMixers.failureBound_lt_one
---
Substitute the proved coordinate count. The numerator is C times
2^(a n), with C independent of n and a the displayed profile-count
slope. The denominator exponent is at least (a+1)n. For n≥C, the
elementary inequality n<2^n makes the resulting bound strictly below one.
-/
theorem failureBound_lt_one (k n b degree J K s₀ : ℕ)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀)
    (hn : threshold k b degree J K s₀ ≤ n) :
    failureBound k n b degree J K s₀ < 1 := by
  let a := (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K
  let q := 2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)
  have hcount := (CoordinateCounts.coordinate_dimensions k n b degree).2.2
  have he : Fintype.card (Coordinate k n b degree) * K + K * K + q =
      ((∑ j ∈ Finset.range (degree + 1), b.choose j) * K + K * K + q) + a * n := by
    rw [hcount]
    dsimp [a]
    ring
  have hnum : testCountBound k n b degree K * 2 ^ q =
      threshold k b degree J K s₀ * 2 ^ (a * n) := by
    unfold testCountBound threshold
    rw [show (((K + 1) ^ Fintype.card (Component (Tag k)) *
        2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K)) * (2 * k + 1) * 2 ^ b) * 2 ^ q =
        ((K + 1) ^ Fintype.card (Component (Tag k)) * (2 * k + 1) * 2 ^ b) *
          (2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K) * 2 ^ q) by ring]
    rw [← pow_add, he, pow_add]
    dsimp [q]
    ring
  have hNat : testCountBound k n b degree K * 2 ^ q < 2 ^ ((s₀ + 1) * n) := calc
    _ = threshold k b degree J K s₀ * 2 ^ (a * n) := hnum
    _ < 2 ^ n * 2 ^ (a * n) := Nat.mul_lt_mul_of_pos_right
      (hn.trans_lt n.lt_two_pow_self) (by positivity)
    _ = 2 ^ ((a + 1) * n) := by rw [← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right n (Nat.add_le_add_right hmargin 1))
  unfold failureBound
  rw [← mul_div_assoc]
  apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))).mpr
  rw [one_mul]
  exact_mod_cast hNat

/--
---
conclusion: Lax342547.UnaryMixers.exists_for_large_n
---
Use the explicit threshold, independent of n and of the tester family.
The finite union bound then yields mixers satisfying every unary test
for each n above that threshold, before any unit law is introduced.
-/
theorem exists_for_large_n (k b degree J K s₀ : ℕ) (hk : 0 < k)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ M : Index (Component (Tag k)) J → Moment k n b degree, Good D K s₀ M := by
  refine ⟨threshold k b degree J K s₀, ?_⟩
  intro n hn r₀ hr D
  exact exists_of_failureBound_lt_one hk D s₀ (failureBound_lt_one k n b degree J K s₀ hmargin hn)

/--
---
conclusion: Lax342547.UnaryMixers.exists_uniform_unary
---
Choose simultaneous successful unary mixers above the explicit
threshold. For each profile, tag, and label, use its factorization to
define the bounded row space before any non-Z values are specified.
The row-space dependence and polar-rank bound then hold for every
allowed fixing with that same space.
-/
theorem exists_uniform_unary (k b degree J K s₀ : ℕ) (hk : 0 < k)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ M : Index (Component (Tag k)) J → Moment k n b degree, UniformUnary D K s₀ M := by
  obtain ⟨n₀, hn₀⟩ := exists_for_large_n k b degree J K s₀ hk hmargin
  refine ⟨n₀, ?_⟩
  intro n hn r₀ hr D
  obtain ⟨M, hM⟩ := hn₀ n hn r₀ hr D
  refine ⟨M, ?_⟩
  intro x hx hK l s
  have hf (e : Component (Tag k)) :=
    SymmetricFactorization.symmetric_factorization (x.val e) (ProfileCounting.profile_transpose x e)
  choose Z H hZ hHsym hH hfactor using hf
  refine ⟨Lax342547.UnaryMixer.zRowSpace Z (leftMixers M) (rightMixers M) l s,
    UnaryMixer.row_space_dimension Z (leftMixers M) (rightMixers M) l s hK, ?_⟩
  intro z hz
  constructor
  · apply Nat.le_of_not_gt
    intro hbad
    exact hM x hx hK l s ⟨z, hz, hbad⟩
  · intro u v hrows
    exact UnaryMixer.unary_depends_on_rows D x Z H hfactor (leftMixers M) (rightMixers M)
      l s z hz u v hrows

end Lax342547Proofs.UnaryMixers
