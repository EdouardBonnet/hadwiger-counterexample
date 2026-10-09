import Lax342547.BinaryMixers
import Lax342547Proofs.BinaryMixer

namespace Lax342547Proofs.BinaryMixers

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.Atoms Lax342547.AtomDirections Lax342547.BinaryMixer Lax342547.BinaryMixers
open scoped ENNReal

/--
---
conclusion: Lax342547.BinaryMixers.uniform_of_restrictions
---
A parity involving an indexed mixer retains its free-direction rank,
even with either self-Gram order added. A parity using only self-Gram
evaluations retains its sharp-direction rank. Every flavor contains
both blocks, so the same choices work for all tags and flavors.
-/
theorem uniform_of_restrictions {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (hL : MixerGood L) (hM : SharpGood M) : UniformBinary hr hd L M := by
  classical
  intro s t hst l m f g a b' c d habcd
  by_cases hab : ∃ j, a j ≠ 0 ∨ b' j ≠ 0
  · have h := BinaryMixer.block_rank_le (ambientParity L a b' (selfGram hr hd M) c d)
      s t l m f g free (Atoms.flavor_coordinates l f).2.2 (Atoms.flavor_coordinates m g).2.2
    rw [BinaryMixer.parity_free_block] at h
    exact (hL s t hst a b' hab).trans (Nat.mul_le_mul_left 5 h)
  · have ha (j : F) : a j = 0 := by simpa using fun h => hab ⟨j, Or.inl h⟩
    have hb (j : F) : b' j = 0 := by simpa using fun h => hab ⟨j, Or.inr h⟩
    have h := BinaryMixer.block_rank_le (c • selfGram hr hd M + d • (selfGram hr hd M).transpose)
      s t l m f g sharp (Atoms.flavor_coordinates l f).2.1 (Atoms.flavor_coordinates m g).2.1
    rw [BinaryMixer.selfGram_parity_sharp_block] at h
    simpa only [ambientParity, ha, hb, zero_smul, add_zero, Finset.sum_const_zero, zero_add] using
      (hM s t hst c d (habcd.resolve_left hab)).trans (Nat.mul_le_mul_left 5 h)

theorem square_exponent_gap (n : ℕ) (hn : 50 ≤ n) :
    n + (n + n) * (n / 5) ≤ n * n := by
  have h : 2 * (n / 5) + 1 ≤ n := by omega
  nlinarith

theorem half_exponent_gap (n : ℕ) (hn : 50 ≤ n) :
    n + (n / 2 + n / 2) * (n / 5) ≤ (n / 2) * (n / 2) := by
  have h : 2 * (n / 5) + 4 ≤ n / 2 := by omega
  have hn' : n ≤ 4 * (n / 2) := by omega
  nlinarith

theorem ratio_le_inverse (n e d : ℕ) (h : n + e ≤ d) :
    (2 : ℝ≥0∞) ^ e / 2 ^ d ≤ 1 / 2 ^ n := by
  calc
    _ ≤ (2 : ℝ≥0∞) ^ e / 2 ^ (n + e) := by
      apply ENNReal.div_le_div_left
      exact pow_le_pow_right₀ (by norm_num) h
    _ = _ := by
      rw [pow_add]
      simpa only [one_mul] using
        (ENNReal.mul_div_mul_right (c := (2 : ℝ≥0∞) ^ e) 1 (2 ^ n) (by simp) (by simp))

theorem mixer_test_bound {k n b degree : ℕ} {F : Type} [Fintype F] [DecidableEq F]
    (hd : 1 ≤ degree) (hn : 50 ≤ n) (s t : Fin b → Binary) (hst : s ≠ t)
    (a b' : F → Binary) (hab : ∃ j, a j ≠ 0 ∨ b' j ≠ 0) :
    (PMF.uniformOfFintype (F → Moment k n b degree)).toOuterMeasure
      {L | 5 * (Lax342547.OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank < n} ≤ 1 / (2 : ℝ≥0∞) ^ n := by
  have hdir := AtomDirections.distinct_directions_injective (k := k) (n := n) hd s t hst free
    (by intro i j h; simpa [free] using h)
  calc
    _ ≤ (PMF.uniformOfFintype (F → Moment k n b degree)).toOuterMeasure
        {L | (Lax342547.OrderedMixerLaw.familyParity (blockDirections s free)
          (blockDirections t free) a b' L).rank ≤ n / 5} := by
      apply MeasureTheory.OuterMeasure.mono
      intro L hL
      change 5 * (Lax342547.OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank < n at hL
      change (Lax342547.OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank ≤ n / 5
      omega
    _ ≤ (2 : ℝ≥0∞) ^ ((n + n) * (n / 5)) / 2 ^ (n * n) := by
      simpa only [Fintype.card_fin] using
        OrderedMixerLaw.family_parity_low_rank_bound _ _ hdir a b' hab (n / 5)
    _ ≤ _ := ratio_le_inverse _ _ _ (square_exponent_gap n hn)

theorem sharp_test_bound {n b : ℕ} (hn : 50 ≤ n)
    (s t : Fin b → Binary) (hst : s ≠ t) (c d : Binary) (hcd : c ≠ 0 ∨ d ≠ 0) :
    (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | 5 * (c • Lax342547.SharpMixerLaw.weighted (fun a => s a + t a) M +
        d • (Lax342547.SharpMixerLaw.weighted (fun a => s a + t a) M).transpose).rank < n} ≤
      1 / (2 : ℝ≥0∞) ^ n := by
  have h := SharpMixerLaw.label_parity_low_rank_bounds (n := n) s t hst (n / 5)
  have hf := h.1.trans (ratio_le_inverse _ _ _ (square_exponent_gap n hn))
  have hr := h.2.1.trans (ratio_le_inverse _ _ _ (square_exponent_gap n hn))
  have ha := h.2.2.trans (ratio_le_inverse _ _ _ (half_exponent_gap n hn))
  have hsub {Ω : Type} (p : PMF Ω) (rank : Ω → ℕ) :
      p.toOuterMeasure {x | 5 * rank x < n} ≤ p.toOuterMeasure {x | rank x ≤ n / 5} := by
    apply MeasureTheory.OuterMeasure.mono
    intro x hx
    change 5 * rank x < n at hx
    change rank x ≤ n / 5
    omega
  have hbit (z : Binary) : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hbit c with rfl | rfl <;> rcases hbit d with rfl | rfl
  · simp at hcd
  · simpa only [zero_smul, one_smul, zero_add] using (hsub _ _).trans hr
  · simpa only [zero_smul, one_smul, add_zero] using (hsub _ _).trans hf
  · simpa only [one_smul] using (hsub _ _).trans ha

theorem mixer_test_card (b : ℕ) (F : Type) [Fintype F] [DecidableEq F] :
    Fintype.card (MixerTest b F) = 2 ^ (2 * b + 2 * Fintype.card F) := by
  simp only [MixerTest, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    show Fintype.card Binary = 2 from rfl, ← pow_add]
  congr 1
  omega

theorem sharp_test_card (b : ℕ) : Fintype.card (SharpTest b) = 2 ^ (2 * b + 2) := by
  simp only [SharpTest, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    show Fintype.card Binary = 2 from rfl]
  calc
    _ = 2 ^ b * 2 ^ b * 2 ^ 2 := by ring
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

/--
---
conclusion: Lax342547.BinaryMixers.mixer_failure_bound
---
Union over the two labels and all forward/reverse coefficient lists.
Each nonempty indexed parity has a uniform free block; for n≥50 its
low-rank probability is at most 2^(-n). No flavor union is needed.
-/
theorem mixer_failure_bound {k n b degree : ℕ} {F : Type} [Fintype F] [DecidableEq F]
    (hd : 1 ≤ degree) (hn : 50 ≤ n) :
    (PMF.uniformOfFintype (F → Moment k n b degree)).toOuterMeasure
      {L | ¬ MixerGood L} ≤ failureBound b (Fintype.card F) n := by
  classical
  let p := PMF.uniformOfFintype (F → Moment k n b degree)
  let bad (v : MixerTest b F) : Set (F → Moment k n b degree) :=
    {L | v.1 ≠ v.2.1 ∧ (∃ j, v.2.2.1 j ≠ 0 ∨ v.2.2.2 j ≠ 0) ∧
      5 * (Lax342547.OrderedMixerLaw.familyParity (blockDirections v.1 free)
        (blockDirections v.2.1 free) v.2.2.1 v.2.2.2 L).rank < n}
  have heq : {L : F → Moment k n b degree | ¬ MixerGood L} = ⋃ v, bad v := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, MixerGood, bad]
    constructor
    · intro h
      push Not at h
      obtain ⟨s, t, hst, a, b', hab, hbad⟩ := h
      exact ⟨(s, t, a, b'), hst, hab, hbad⟩
    · rintro ⟨⟨s, t, a, b'⟩, hst, hab, hbad⟩ h
      exact (not_lt_of_ge (h s t hst a b' hab)) hbad
  have hb (v : MixerTest b F) : p.toOuterMeasure (bad v) ≤ 1 / (2 : ℝ≥0∞) ^ n := by
    by_cases hst : v.1 = v.2.1
    · simp [bad, hst]
    by_cases hab : ∃ j, v.2.2.1 j ≠ 0 ∨ v.2.2.2 j ≠ 0
    · simpa only [bad, hst, hab, ne_eq, not_false_eq_true, true_and] using
        mixer_test_bound (k := k) hd hn v.1 v.2.1 hst v.2.2.1 v.2.2.2 hab
    · simp [bad, hab]
  rw [heq]
  calc
    _ ≤ ∑ v : MixerTest b F, p.toOuterMeasure (bad v) :=
      MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure _
    _ ≤ ∑ _v : MixerTest b F, 1 / (2 : ℝ≥0∞) ^ n := Finset.sum_le_sum (fun v _ => hb v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mixer_test_card,
        Nat.cast_pow, Nat.cast_ofNat, mul_one_div, failureBound]

/--
---
conclusion: Lax342547.BinaryMixers.sharp_failure_bound
---
Union over the label pairs and the four ordered self-Gram coefficient
pairs. Each nonzero parity is controlled by either the full uniform
matrix or its uniform disjoint alternating block.
-/
theorem sharp_failure_bound {n b : ℕ} (hn : 50 ≤ n) :
    (PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)).toOuterMeasure
      {M | ¬ SharpGood M} ≤ failureBound b 1 n := by
  classical
  let p := PMF.uniformOfFintype (Fin b → Matrix (Fin n) (Fin n) Binary)
  let bad (v : SharpTest b) : Set (Fin b → Matrix (Fin n) (Fin n) Binary) :=
    {M | v.1 ≠ v.2.1 ∧ (v.2.2.1 ≠ 0 ∨ v.2.2.2 ≠ 0) ∧
      5 * (v.2.2.1 • Lax342547.SharpMixerLaw.weighted (fun a => v.1 a + v.2.1 a) M +
        v.2.2.2 • (Lax342547.SharpMixerLaw.weighted (fun a => v.1 a + v.2.1 a) M).transpose).rank < n}
  have heq : {M : Fin b → Matrix (Fin n) (Fin n) Binary | ¬ SharpGood M} = ⋃ v, bad v := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SharpGood, bad]
    constructor
    · intro h
      push Not at h
      obtain ⟨s, t, hst, c, d, hcd, hbad⟩ := h
      exact ⟨(s, t, c, d), hst, hcd, hbad⟩
    · rintro ⟨⟨s, t, c, d⟩, hst, hcd, hbad⟩ h
      exact (not_lt_of_ge (h s t hst c d hcd)) hbad
  have hb (v : SharpTest b) : p.toOuterMeasure (bad v) ≤ 1 / (2 : ℝ≥0∞) ^ n := by
    by_cases hst : v.1 = v.2.1
    · simp [bad, hst]
    by_cases hcd : v.2.2.1 ≠ 0 ∨ v.2.2.2 ≠ 0
    · simpa only [bad, hst, hcd, ne_eq, not_false_eq_true, true_and] using
        sharp_test_bound hn v.1 v.2.1 hst v.2.2.1 v.2.2.2 hcd
    · simp [bad, hcd]
  rw [heq]
  calc
    _ ≤ ∑ v : SharpTest b, p.toOuterMeasure (bad v) :=
      MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure _
    _ ≤ ∑ _v : SharpTest b, 1 / (2 : ℝ≥0∞) ^ n := Finset.sum_le_sum (fun v _ => hb v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sharp_test_card,
        Nat.cast_pow, Nat.cast_ofNat, mul_one_div, failureBound, mul_one]

end Lax342547Proofs.BinaryMixers
