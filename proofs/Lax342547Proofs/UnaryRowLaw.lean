import Lax342547.UnaryRowLaw
import Lax342547Proofs.UnaryMixer
import Lax342547Proofs.MixerRowLaw
import Lax342547Proofs.CorankCounting
import Lax342547Proofs.SymmetricFactorization
import Lax342547Proofs.ProfileCounting
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.UnaryRowLaw

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.UnaryMixer Lax342547.UnaryRowLaw

variable {E I N : Type} [Fintype E] [Fintype I] [Fintype N]

theorem rowIndex_card (r : E → ℕ) (inc : Finset E) (J : ℕ) :
    Fintype.card (RowIndex r inc J) = 4 * J * inc.card * ∑ e, r e := by
  rw [← Module.finrank_fintype_fun_eq_card (R := Binary), ← flatten.finrank_eq]
  exact UnaryMixer.rows_dimension r inc J

theorem full_codimension {r : E → ℕ} {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec) :
    Module.finrank Binary (FullList r J N) ≤
      Module.finrank Binary (LinearMap.range (fullObservations (J := J) Z D)) +
        2 * J * (∑ e, r e) ^ 2 := by
  have h := FiniteLinearLaw.family_codimension
    (fun p : Index E J => Lax342547.MixerRowLaw.observations (Z p.2.2.1) (Z p.2.2.2) D)
    (fun p => r p.2.2.1 * r p.2.2.2)
    (fun p => by simpa using (MixerRowLaw.observations_codimension
      (Z p.2.2.1) (Z p.2.2.2) D (hZ _) (hZ _) hD))
  have hc : (∑ p : Index E J, r p.2.2.1 * r p.2.2.2) = 2 * J * (∑ e, r e) ^ 2 := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    ring
  rw [hc] at h
  exact h

omit [Fintype E] [Fintype N] in
theorem pack_surjective {r : E → ℕ} (inc : Finset E) {J : ℕ} :
    Function.Surjective (pack (r := r) (J := J) (N := N) inc) := by
  classical
  intro M
  let y : FullList r J N := fun p =>
    ((fun a i => if hf : p.2.2.2 ∈ inc then
      M ⟨.inl (p.2.1, p.2.2.1, ⟨p.2.2.2, hf⟩), if p.1 then .inr a else .inl a⟩ i else 0),
     (fun i a => if he : p.2.2.1 ∈ inc then
      M ⟨.inr (p.2.1, ⟨p.2.2.1, he⟩, p.2.2.2), if p.1 then .inr a else .inl a⟩ i else 0))
  refine ⟨y, ?_⟩
  funext a i
  rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩ <;> simp [pack, y]

theorem mixerRows_codimension {r : E → ℕ} (inc : Finset E) {J K : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec)
    (hr : ∑ e, r e ≤ K) :
    Module.finrank Binary (Matrix (RowIndex r inc J) N Binary) ≤
      Module.finrank Binary (LinearMap.range (mixerRows (J := J) inc Z D)) + 2 * J * K ^ 2 := by
  have hfull := full_codimension (J := J) Z D hZ hD
  have h := FiniteLinearLaw.codimension_map_le (pack (r := r) (J := J) (N := N) inc)
    (pack_surjective inc) (LinearMap.range (fullObservations Z D))
  rw [← LinearMap.range_comp] at h
  have hdim := (LinearMap.range (mixerRows (J := J) inc Z D)).finrank_le
  have hcost : 2 * J * (∑ e, r e) ^ 2 ≤ 2 * J * K ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 2)
  change _ - Module.finrank Binary (LinearMap.range (mixerRows (J := J) inc Z D)) ≤ _ at h
  omega

open scoped ENNReal

omit [Fintype E] in
theorem mixerRows_factor {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) :
    (mixerRows inc Z D M).mulVecLin = flatten.toLinearMap.comp (rowLinear inc Z D M) := by
  apply LinearMap.ext
  intro v
  funext a
  rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩
  · change ((Z e).transpose * M (false, j, e, f.val) * D).mulVec v a =
      ((Z e).transpose * M (false, j, e, f.val)).mulVec (D.mulVec v) a
    rw [Matrix.mulVec_mulVec]
  · change ((Z e).transpose * M (true, j, e, f.val) * D).mulVec v a =
      ((Z e).transpose * M (true, j, e, f.val)).mulVec (D.mulVec v) a
    rw [Matrix.mulVec_mulVec]
  · change (D.transpose * (M (false, j, e.val, f) * Z f)).transpose.mulVec v a =
      (M (false, j, e.val, f) * Z f).transpose.mulVec (D.mulVec v) a
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  · change (D.transpose * (M (true, j, e.val, f) * Z f)).transpose.mulVec v a =
      (M (true, j, e.val, f) * Z f).transpose.mulVec (D.mulVec v) a
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]

omit [Fintype E] in
/--
---
conclusion: Lax342547.UnaryRowLaw.mixerRows_rank
---
Multiplication by the packed matrix is exactly the formal row map,
followed by the linear equivalence flattening its indexed row halves.
That equivalence preserves the image dimension.
-/
theorem mixerRows_rank {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) :
    (mixerRows inc Z D M).rank = Module.finrank Binary (LinearMap.range (rowLinear inc Z D M)) := by
  rw [Matrix.rank, mixerRows_factor, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq flatten _

theorem event_bound_of_pointwise {α : Type} [Fintype α] (p q : PMF α) (c : ℝ≥0∞)
    (h : ∀ a, p a ≤ c * q a) (S : Set α) : p.toOuterMeasure S ≤ c * q.toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ S
  · simpa only [Set.indicator_of_mem ha] using h a
  · simp [Set.indicator_of_notMem ha]

/--
---
conclusion: Lax342547.UnaryRowLaw.joint_row_law
---
Joint observations of all independent L and R matrices have total
compatibility codimension at most 2J(Σr)². Selecting the incident row
entries is surjective on the unconstrained lists and cannot increase
codimension. The uniform linear-image bound gives the claimed density.
-/
theorem joint_row_law [DecidableEq E] [DecidableEq I] [DecidableEq N]
    {r : E → ℕ} (inc : Finset E) {J K : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec)
    (hr : ∑ e, r e ≤ K) (y : Matrix (RowIndex r inc J) N Binary) :
    (PMF.uniformOfFintype (Index E J → Matrix I I Binary)).map (mixerRows inc Z D) y ≤
      2 ^ (2 * J * K ^ 2) * PMF.uniformOfFintype (Matrix (RowIndex r inc J) N Binary) y := by
  classical
  exact FiniteLinearLaw.uniform_image_bound _ _ (mixerRows_codimension inc Z D hZ hD hr) y

/--
---
conclusion: Lax342547.UnaryRowLaw.row_corank_bound
---
Sum the joint density domination over the corank event and apply the
checked uniform row-relation bound. The number of formal rows is at
most 4J times the incidence count times K, giving the stated exponent.
-/
theorem row_corank_bound [DecidableEq E] [DecidableEq I] [DecidableEq N]
    {r : E → ℕ} (inc : Finset E) {J K : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec)
    (hr : ∑ e, r e ≤ K) (s : ℕ) :
    (PMF.uniformOfFintype (Index E J → Matrix I I Binary)).toOuterMeasure
      {M | (mixerRows inc Z D M).rank + s ≤ Fintype.card (RowIndex r inc J)} ≤
        (2 : ℝ≥0∞) ^ (2 * J * K ^ 2 + s * (4 * J * inc.card * K)) / 2 ^ (s * Fintype.card N) := by
  classical
  let p := PMF.uniformOfFintype (Index E J → Matrix I I Binary)
  let q := PMF.uniformOfFintype (Matrix (RowIndex r inc J) N Binary)
  let S : Set (Matrix (RowIndex r inc J) N Binary) := {A | A.rank + s ≤ Fintype.card (RowIndex r inc J)}
  have hdom := event_bound_of_pointwise (p.map (mixerRows inc Z D)) q (2 ^ (2 * J * K ^ 2))
    (joint_row_law inc Z D hZ hD hr) S
  rw [PMF.toOuterMeasure_map_apply] at hdom
  have hc := CorankCounting.uniform_corank_bound (I := RowIndex r inc J) (J := N) s
  have hcard : Fintype.card (RowIndex r inc J) ≤ 4 * J * inc.card * K := by
    rw [rowIndex_card]
    exact Nat.mul_le_mul_left _ hr
  calc
    _ ≤ 2 ^ (2 * J * K ^ 2) * q.toOuterMeasure S := hdom
    _ ≤ 2 ^ (2 * J * K ^ 2) *
        (2 ^ (s * Fintype.card (RowIndex r inc J)) / 2 ^ (s * Fintype.card N)) :=
      mul_le_mul_right hc _
    _ ≤ 2 ^ (2 * J * K ^ 2) * (2 ^ (s * (4 * J * inc.card * K)) / 2 ^ (s * Fintype.card N)) := by
      gcongr
      norm_num
    _ = _ := by rw [pow_add, mul_div_assoc]

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

/--
---
conclusion: Lax342547.UnaryRowLaw.unary_failure_probability
---
Factor each actual symmetric profile component through its rank. The
always-retained free block gives injective direction columns. If any
non-Z fixing fails the unary rank bound, the common row map must have
corank at least s₀+1. The single row-corank event therefore controls all
fixings at once, without a union over their values or over flavors.
-/
theorem unary_failure_probability {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) (hx : x ≠ 0) (hK : ∑ e, (x.val e).rank ≤ K)
    (l : Tag k) (s : Fin b → Binary) (s₀ : ℕ) :
    (PMF.uniformOfFintype (Index (Component (Tag k)) J → Moment k n b degree)).toOuterMeasure
      {M | UnaryBad D x l s s₀ M} ≤
        (2 : ℝ≥0∞) ^ (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)) / 2 ^ ((s₀ + 1) * n) := by
  classical
  have hf (e : Component (Tag k)) :=
    SymmetricFactorization.symmetric_factorization (x.val e) (ProfileCounting.profile_transpose x e)
  choose Z H hZ hHsym hH hfactor using hf
  have hfree : Function.Injective (free : Fin n → Base k n) := by
    intro i j h
    exact (Prod.mk.inj (Sum.inr.inj h)).2
  have hDir := AtomDirections.blockDirections_injective (degree := degree) s free hfree
  have hprob := row_corank_bound (J := J) (incident l) Z
    (Lax342547.AtomDirections.blockDirections s free) hZ hDir hK (s₀ + 1)
  rw [UnaryMixer.incident_card, Fintype.card_fin] at hprob
  apply le_trans ((PMF.uniformOfFintype
    (Index (Component (Tag k)) J → Moment k n b degree)).toOuterMeasure.mono ?_) hprob
  intro M hM
  obtain ⟨z, hz, hbad⟩ := hM
  by_contra hn
  have hA : Module.finrank Binary (Rows (fun e => (x.val e).rank) (incident l) J) ≤
      Module.finrank Binary (LinearMap.range (zRows Z (leftMixers M) (rightMixers M) l s)) + s₀ := by
    simp only [Set.mem_ofPred_eq] at hn
    rw [mixerRows_rank, rowIndex_card] at hn
    rw [UnaryMixer.rows_dimension]
    change ¬ (Module.finrank Binary (LinearMap.range
      (zRows Z (leftMixers M) (rightMixers M) l s)) + (s₀ + 1) ≤
        4 * J * (incident l).card * ∑ e, (x.val e).rank) at hn
    omega
  have hgood := UnaryMixer.unary_rank_lower hk D x hx Z H hfactor (fun e => (hH e).1)
    (leftMixers M) (rightMixers M) l s z hz s₀ hA
  exact (not_lt_of_ge hgood) hbad

end Lax342547Proofs.UnaryRowLaw
