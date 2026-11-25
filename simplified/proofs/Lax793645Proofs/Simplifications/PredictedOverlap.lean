import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRanks
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Local ingredients for the unified predicted branch. In particular the error
bound is for unnormalized query measures; it never divides by compatibility
mass or predictor-cell mass. The base-query hit theorem is a separate obligation.
-/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section

theorem prediction_error_unnormalized {X I : Type*} [Fintype X] [Fintype I]
    (w : Wgt X) (hw : ∀ x, 0 ≤ w x) (W Base Full : X → Prop) (P : I → X → Prop)
    (hfull : ∀ x, W x → Base x → (∀ i, P i x) → Full x)
    (e : ℝ) (hfail : ∀ i, pr w (fun x => ¬P i x) ≤ e) :
    pr w (fun x => W x ∧ Base x) - Fintype.card I*e ≤
      pr w (fun x => W x ∧ Full x) := by
  classical
  have hi (x : X) : ind (W x ∧ Base x) ≤
      ind (W x ∧ Full x) + ∑ i, ind (¬P i x) := by
    by_cases h : W x ∧ Base x
    · rw [ind_one h]
      by_cases hp : ∀ i, P i x
      · rw [ind_one ⟨h.1, hfull x h.1 h.2 hp⟩]
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ind_nonneg (¬P i x))
        linarith
      · obtain ⟨i, hi⟩ := Classical.not_forall.mp hp
        have hb : 1 ≤ ∑ j, ind (¬P j x) := by
          rw [← ind_one hi]
          exact Finset.single_le_sum (fun j _ => ind_nonneg (¬P j x)) (Finset.mem_univ i)
        linarith [ind_nonneg (W x ∧ Full x)]
    · rw [ind_zero h]
      exact add_nonneg (ind_nonneg _) (Finset.sum_nonneg fun i _ => ind_nonneg _)
  have h := avg_mono hw hi
  rw [avg_add, avg_sum] at h
  have he : (∑ i, pr w (fun x => ¬P i x)) ≤ Fintype.card I*e := by
    calc
      _ ≤ ∑ _i : I, e := Finset.sum_le_sum fun i _ => hfail i
      _ = _ := by simp
  change pr w (fun x => W x ∧ Base x) ≤ pr w (fun x => W x ∧ Full x) +
    ∑ i, pr w (fun x => ¬P i x) at h
  linarith

/-- A zero-diagonal binary matrix cannot contain an all-one off-diagonal
submatrix larger than rank plus one. Repeated sampled vertices are allowed. -/
theorem binary_clique_rank {X : Type} [Fintype X] {s : ℕ}
    (H : Mat X X) (x : Fin s → X) (hdiag : ∀ v, H v v = 0)
    (hclique : ∀ i j, i ≠ j → H (x i) (x j) = 1) : s ≤ H.rank+1 := by
  classical
  let B := H.submatrix x x
  let J : Mat (Fin s) (Fin s) := Matrix.vecMulVec (fun _ => 1) (fun _ => 1)
  have he : B+J=1 := by
    ext i j
    by_cases h : i=j
    · subst j
      simp [B, J, Matrix.submatrix, hdiag, Matrix.vecMulVec_apply]
    · simp [B, J, Matrix.submatrix, hclique i j h, h,
        Matrix.vecMulVec_apply]
      exact char_two (1 : F)
  have hr := mrk_add_le B J
  rw [he, Matrix.rank_one, Fintype.card_fin] at hr
  have hJ : J.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hB : B.rank ≤ H.rank := Matrix.rank_submatrix_le H x x
  omega

theorem low_rank_zero_pair {X : Type} [Fintype X] (H : Mat X X) (r : ℕ)
    (hr : H.rank ≤ r) (hdiag : ∀ v, H v v = 0) (x : Fin (r+2) → X) :
    ∃ i j, i ≠ j ∧ H (x i) (x j) = 0 := by
  classical
  by_contra h
  have hc : ∀ i j, i ≠ j → H (x i) (x j) = 1 := by
    intro i j hij
    rcases bit_cases (H (x i) (x j)) with hz | ho
    · exact False.elim (h ⟨i, j, hij, hz⟩)
    · exact ho
  have := binary_clique_rank H x hdiag hc
  omega

/-- Union bound with equal pair marginals. Taking `w` to be an iid sample law
gives the proposed inverse-square compatibility bound (with a looser constant). -/
theorem zero_pair_probability {Ω X : Type} [Fintype Ω] [Fintype X]
    (w : Wgt Ω) (hw : IsLaw w) (H : Mat X X) (r : ℕ)
    (hr : H.rank ≤ r) (hdiag : ∀ v, H v v = 0)
    (sample : Ω → Fin (r+2) → X) (p : ℝ) (hp : 0 ≤ p)
    (hpair : ∀ i j, i ≠ j →
      pr w (fun ω => H (sample ω i) (sample ω j) = 0) ≤ p) :
    1 ≤ (r+2:ℝ)^2*p := by
  classical
  let E (i j : Fin (r+2)) (ω : Ω) := i ≠ j ∧ H (sample ω i) (sample ω j) = 0
  have hall : pr w (fun ω => ∃ i, ∃ j, E i j ω) = 1 := by
    have ht : (fun ω => ∃ i, ∃ j, E i j ω) = fun _ => True := by
      funext ω
      exact propext ⟨fun _ => trivial, fun _ => low_rank_zero_pair H r hr hdiag (sample ω)⟩
    rw [ht]
    simpa [pr] using hw.avg_const 1
  have h1 := pr_exists_le hw.nz (fun i ω => ∃ j, E i j ω)
  have h2 (i) := pr_exists_le hw.nz (E i)
  have he (i j) : pr w (E i j) ≤ p := by
    by_cases hij : i=j
    · subst j
      simp [E, pr, ind, avg, hp]
    · exact (pr_mono hw.nz (fun _ h => h.2)).trans (hpair i j hij)
  rw [hall] at h1
  calc
    1 ≤ ∑ i, pr w (fun ω => ∃ j, E i j ω) := h1
    _ ≤ ∑ i, ∑ j, pr w (E i j) := Finset.sum_le_sum fun i _ => h2 i
    _ ≤ ∑ _i : Fin (r+2), ∑ _j : Fin (r+2), p :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ = (r+2:ℝ)^2*p := by simp; ring

/-- The exact quantitative distinction needed in the rare-compatible-pair case:
the error is paid inside a fixed hit, before averaging over compatibility. -/
theorem predicted_hit_survives {base full h ε : ℝ}
    (hbase : h ≤ base) (herr : base-ε ≤ full) (hsmall : ε ≤ h/2) : h/2 ≤ full := by
  linarith

/-- After subtracting the predicted free coordinates, only a three-dimensional
binary span remains. The coefficients are bits, so zero coefficients are simply
discarded when turning this into an atom list. -/
theorem three_generator_span (S : Set (Fin 3 → F)) (v : Fin 3 → F)
    (hv : v ∈ Submodule.span F S) :
    ∃ T : Set (Fin 3 → F), T ⊆ S ∧ Nat.card T ≤ 3 ∧
      letI := Fintype.ofFinite T
      ∃ c : T → F, (∑ t, c t • t.val) = v := by
  classical
  obtain ⟨T, hTS, hspan, hli⟩ := exists_linearIndependent F S
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T ≤ 3 := by
    simpa using hli.fintype_card_le_finrank
  have ht : v ∈ Submodule.span F (Set.range (Subtype.val : T → (Fin 3 → F))) := by
    simpa [Subtype.range_coe, hspan] using hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp ht
  exact ⟨T, hTS, by simpa [Nat.card_eq_fintype_card] using hcard, c, hc⟩

end
end Lax793645Proofs.Simplifications
