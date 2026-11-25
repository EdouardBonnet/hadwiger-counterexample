import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PolynomialRankBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Finset

noncomputable section

/-- A sparse matrix of rank at most `k` vanishes on a large principal submatrix.
A basis of its light rows covers all columns on which any light row is nonzero. -/
theorem row_support_cut {A K : Type} [Fintype A] [Field K] (M : Matrix A A K)
    (w : Wgt A) (hw : IsLaw w) (k : ℕ) (hr : M.rank ≤ k) (t : ℝ) (ht : 0 < t) :
    ∃ I : A → Prop, (∀ x, I x → ∀ y, I y → M x y = 0) ∧
      1 - pr (pairW w w) (fun xy => M xy.1 xy.2 ≠ 0) / t - k * t ≤ pr w I := by
  classical
  let mass (v : A → K) := pr w (fun y => v y ≠ 0)
  let rows := M.row '' {x | mass (M.row x) < t}
  obtain ⟨basis, hbasis, hcard, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K rows
  have hsize : basis.card ≤ k := by
    rw [hcard]
    apply le_trans _ hr
    rw [M.rank_eq_finrank_span_row]
    exact Submodule.finrank_mono (span_mono (Set.image_subset_range ..))
  let covered (y : A) := ∃ v ∈ basis, v y ≠ 0
  have hcover : pr w covered ≤ k * t := calc
    _ ≤ ∑ v ∈ basis, mass v := pr_union_le hw.nz basis _
    _ ≤ ∑ _v ∈ basis, t := sum_le_sum fun v hv => by
      obtain ⟨x,hx,rfl⟩ := hbasis hv
      exact hx.le
    _ = (basis.card : ℝ) * t := by simp
    _ ≤ k * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) ht.le
  let heavy (x : A) := t ≤ mass (M.row x)
  have hheavy : pr w heavy ≤ pr (pairW w w) (fun xy => M xy.1 xy.2 ≠ 0) / t := by
    apply (le_div_iff₀ ht).mpr
    rw [mul_comm]
    change t * pr w heavy ≤ avg (pairW w w) _
    rw [pairW_avg]
    exact le_avg_markov hw.nz (fun x => pr_nonneg (p := fun y => M x y ≠ 0) hw.nz) t
  refine ⟨fun x => ¬(heavy x ∨ covered x), ?_, ?_⟩
  · intro x hx y hy
    have hx' : mass (M.row x) < t := lt_of_not_ge (fun h => hx (Or.inl h))
    let ev : (A → K) →ₗ[K] K := LinearMap.proj y
    have hker : span K (↑basis : Set (A → K)) ≤ ev.ker :=
      span_le.mpr fun v hv => by
        change v y = 0
        by_contra h
        exact hy (Or.inr ⟨v,hv,h⟩)
    rw [hspan] at hker
    exact hker (subset_span ⟨x,hx',rfl⟩)
  · rw [pr_not w (fun x => heavy x ∨ covered x), hw.total]
    linarith only [hheavy, hcover, pr_or_le (p := heavy) (q := covered) hw.nz]

/-- Either nonzero entries have inverse-rank mass, or a set of mass greater
than `1 - ε` avoids every such entry, in both directions. -/
theorem row_support_alternative {A K : Type} [Fintype A] [Field K] (M : Matrix A A K)
    (w : Wgt A) (hw : IsLaw w) (k : ℕ) (hk : 0 < k) (hr : M.rank ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ε^2 / (4 * k) ≤ pr (pairW w w) (fun xy => M xy.1 xy.2 ≠ 0) ∨
      ∃ I : A → Prop, 1 - ε < pr w I ∧ ∀ x, I x → ∀ y, I y → M x y = 0 := by
  classical
  by_cases h : ε^2 / (4 * k) ≤ pr (pairW w w) (fun xy => M xy.1 xy.2 ≠ 0)
  · exact Or.inl h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  let t := ε / (2 * k)
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨I,hI,hpr⟩ := row_support_cut M w hw k hr t ht
  have hl : pr (pairW w w) (fun xy => M xy.1 xy.2 ≠ 0) / t < ε / 2 := by
    apply (div_lt_iff₀ ht).mpr
    convert lt_of_not_ge h using 1
    dsimp [t]
    ring
  have heq : (k : ℝ) * t = ε / 2 := by dsimp [t]; field_simp
  exact Or.inr ⟨I,by linarith only [hpr, hl, heq],hI⟩

/-- If the diagonal is nonzero, the support of a rank-`k` matrix has
product probability at least `1 / (4*k)` under two draws from the same law. -/
theorem row_support_probability {A K : Type} [Fintype A] [Field K]
    (M : Matrix A A K) (w : Wgt A) (hw : IsLaw w) (k : ℕ) (hk : 0 < k)
    (hr : M.rank ≤ k) (hdiag : ∀ x, M x x ≠ 0) :
    1 / (4 * (k : ℝ)) ≤ pr (pairW w w) (fun x => M x.1 x.2 ≠ 0) := by
  rcases row_support_alternative M w hw k hk hr 1 zero_lt_one with h | ⟨I,hI,hzero⟩
  · simpa only [one_pow] using h
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz (by simpa only [sub_self] using hI)
  exact (hdiag x (hzero x hx x hx)).elim

private def complementMatrix {A : Type} (M : Mat A A) :=
  vecMulVec (fun _ : A => (1 : F)) (fun _ : A => (1 : F)) + M

private lemma complement_rank {A : Type} [Fintype A] (M : Mat A A) :
    (complementMatrix M).rank ≤ M.rank + 1 :=
  (mrk_add_le ..).trans ((Nat.add_le_add_right (rank_vecMulVec_le ..) _).trans_eq (Nat.add_comm ..))

private lemma complement_nonzero {A : Type} (M : Mat A A) (x y : A) :
    complementMatrix M x y ≠ 0 ↔ M x y = 0 := by
  change (1 : F) * 1 + M x y ≠ 0 ↔ _
  rcases bit_cases (M x y) with h|h <;> simp [h, char_two]

/-- Complementing the matrix turns a prescribed zero into a support event. -/
theorem zero_entry_probability {A : Type} [Fintype A] (M : Mat A A)
    (w : Wgt A) (hw : IsLaw w) (r : ℕ) (hr : M.rank ≤ r) (hdiag : ∀ x, M x x = 0) :
    1 / (4 * ((r : ℝ) + 1)) ≤ pr (pairW w w) (fun x => M x.1 x.2 = 0) := by
  have h := row_support_probability (complementMatrix M) w hw (r+1) (by omega)
    ((complement_rank M).trans (Nat.add_le_add_right hr 1))
    (fun x => (complement_nonzero M x x).mpr (hdiag x))
  simpa only [complement_nonzero, Nat.cast_add, Nat.cast_one] using h

/-- The support of the entrywise product of a complemented matrix and its
transpose records a zero in both directions. -/
theorem mutual_zero_probability {A : Type} [Fintype A] (M : Mat A A)
    (w : Wgt A) (hw : IsLaw w) (r : ℕ) (hr : M.rank ≤ r) (hdiag : ∀ x, M x x = 0) :
    1 / (4 * ((r : ℝ) + 1)^2) ≤
      pr (pairW w w) (fun x => M x.1 x.2 = 0 ∧ M x.2 x.1 = 0) := by
  let Q := complementMatrix M
  have hQ : Q.rank ≤ r + 1 := (complement_rank M).trans (Nat.add_le_add_right hr 1)
  have hmask : (mpMask Q Qᵀ).rank ≤ (r+1)^2 := by
    simpa only [rank_transpose, pow_two] using
      (rank_mask Q Qᵀ).trans (Nat.mul_le_mul hQ (by simpa only [rank_transpose] using hQ))
  have nonzero (x y : A) : mpMask Q Qᵀ x y ≠ 0 ↔ M x y = 0 ∧ M y x = 0 := by
    change Q x y * Q y x ≠ 0 ↔ _
    rw [mul_ne_zero_iff, complement_nonzero, complement_nonzero]
  have h := row_support_probability _ w hw ((r+1)^2) (by positivity) hmask
    (fun x => (nonzero x x).mpr ⟨hdiag x,hdiag x⟩)
  simpa only [nonzero, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h

/-- Two zero-diagonal matrices have simultaneous zeros in both directions
on at least an inverse fourth power of their common rank bound. -/
theorem four_zero_probability {A : Type} [Fintype A] (M T : Mat A A)
    (w : Wgt A) (hw : IsLaw w) (r : ℕ) (hM : M.rank≤r) (hT : T.rank≤r)
    (dM : ∀ x,M x x=0) (dT : ∀ x,T x x=0) :
    1/(4*((r:ℝ)+1)^4)≤pr (pairW w w) (fun x=>
      M x.1 x.2=0 ∧ T x.1 x.2=0 ∧ M x.2 x.1=0 ∧ T x.2 x.1=0) := by
  let Q:=mpMask (complementMatrix M) (complementMatrix T)
  have rankQ : Q.rank≤(r+1)^2 := (rank_mask ..).trans (by
    rw [pow_two]
    exact Nat.mul_le_mul ((complement_rank M).trans (Nat.add_le_add_right hM 1))
      ((complement_rank T).trans (Nat.add_le_add_right hT 1)))
  have both (x y) : Q x y≠0 ↔ M x y=0 ∧ T x y=0 := by
    change complementMatrix M x y*complementMatrix T x y≠0 ↔ _
    rw [mul_ne_zero_iff,complement_nonzero,complement_nonzero]
  have hR : (mpMask Q Qᵀ).rank≤(r+1)^4 := (rank_mask ..).trans (by
    calc Q.rank*Qᵀ.rank ≤ (r+1)^2*(r+1)^2 := Nat.mul_le_mul rankQ (by rwa [rank_transpose])
         _ = (r+1)^4 := by ring)
  have nonzero (x y) : mpMask Q Qᵀ x y≠0 ↔
      M x y=0 ∧ T x y=0 ∧ M y x=0 ∧ T y x=0 := by
    change Q x y*Q y x≠0 ↔ _
    rw [mul_ne_zero_iff,both,both,and_assoc]
  have h:=row_support_probability _ w hw ((r+1)^4) (by positivity) hR
    (fun x=>(nonzero x x).mpr ⟨dM x,dT x,dM x,dT x⟩)
  simpa only [nonzero,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h

/-- For the strict upper triangle the reciprocal zero event is exactly
equality. On a single uniform leaf its conditional probability is 1/m. -/
theorem reciprocal_zero_diagonal_example (m : ℕ) [NeZero m] :
    let F₀ : Mat (Fin m) (Fin m):=fun a b=>if a<b then 1 else 0
    (∀ a b,F₀ a b+F₀ b a=0 ↔ a=b) ∧
      pr (pairW unif unif) (fun x=>F₀ x.1 x.2+F₀ x.2 x.1=0)=1/(m:ℝ) := by
  intro F₀
  have h (a b : Fin m) : F₀ a b+F₀ b a=0 ↔ a=b := by
    rcases lt_trichotomy a b with h|rfl|h
    · simp [F₀,h,not_lt.mpr h.le,ne_of_lt h]
    · simp [F₀]
    · simp [F₀,h,not_lt.mpr h.le,ne_of_gt h]
  refine ⟨h,?_⟩
  simp_rw [h]
  rw [pr,pairW_avg]
  change avg (unif : Wgt (Fin m)) (fun i=>pr unif (fun j=>i=j))=_
  have cell (i : Fin m) : pr unif (fun j=>i=j)=1/(m:ℝ) := by
    rw [show (fun j=>i=j)=(fun j=>j=i) from funext (fun _=>propext eq_comm),pr_point',unif_apply]
    simp [one_div]
  simp_rw [cell]
  exact (unif_law (α:=Fin m)).avg_const _

end
end Lax793645Proofs.Simplifications
