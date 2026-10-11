import Lax342547.UnaryMixer
import Lax342547.MixerRowLaw
import Lax342547.CorankCounting

/-!
---
title: Joint distribution of the unary mixer row matrix
type: lemma
---
All indexed L and R matrices are sampled from one finite product.
The full forward/reverse observation list has additive compatibility
cost. A surjective coordinate selection retains just the incident
formal rows, including their separate L and R halves.
-/

namespace Lax342547.UnaryRowLaw

open Lax342547.MomentSpace Lax342547.UnaryMixer

variable {E I N : Type} [Fintype E] [Fintype I] [Fintype N]

abbrev Index (E : Type) (J : ℕ) := Bool × Fin J × E × E

abbrev RowIndex (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  (t : Block inc J) × (Fin (blockRank r t) ⊕ Fin (blockRank r t))

noncomputable instance (r : E → ℕ) (inc : Finset E) (J : ℕ) :
    DecidableEq (RowIndex r inc J) := Classical.decEq _

noncomputable instance (r : E → ℕ) (inc : Finset E) (J : ℕ) :
    Fintype (RowIndex r inc J) := Fintype.ofFinite _

def flatten {r : E → ℕ} {inc : Finset E} {J : ℕ} :
    Rows r inc J ≃ₗ[Binary] (RowIndex r inc J → Binary) where
  toFun x a := Sum.elim (x a.1).1 (x a.1).2 a.2
  invFun y t := (fun a => y ⟨t, .inl a⟩, fun a => y ⟨t, .inr a⟩)
  left_inv x := rfl
  right_inv y := by funext a; rcases a with ⟨t, a | a⟩ <;> rfl
  map_add' x y := by funext a; rcases a with ⟨t, a | a⟩ <;> rfl
  map_smul' a x := by funext b; rcases b with ⟨t, b | b⟩ <;> rfl

abbrev FullList (r : E → ℕ) (J : ℕ) (N : Type) :=
  ∀ p : Index E J, Matrix (Fin (r p.2.2.1)) N Binary × Matrix N (Fin (r p.2.2.2)) Binary

def fullObservations {r : E → ℕ} {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary) :
    (Index E J → Matrix I I Binary) →ₗ[Binary] FullList r J N :=
  FiniteLinearLaw.familyMap (fun p => MixerRowLaw.observations (Z p.2.2.1) (Z p.2.2.2) D)

def pack {r : E → ℕ} (inc : Finset E) {J : ℕ} :
    FullList r J N →ₗ[Binary] Matrix (RowIndex r inc J) N Binary where
  toFun y a i := match a with
    | ⟨.inl (j, e, f), .inl h⟩ => (y (false, j, e, f.val)).1 h i
    | ⟨.inl (j, e, f), .inr h⟩ => (y (true, j, e, f.val)).1 h i
    | ⟨.inr (j, e, f), .inl h⟩ => (y (false, j, e.val, f)).2 i h
    | ⟨.inr (j, e, f), .inr h⟩ => (y (true, j, e.val, f)).2 i h
  map_add' x y := by
    funext a i
    rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩ <;> rfl
  map_smul' c x := by
    funext a i
    rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩ <;> rfl

def mixerRows {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary) :
    (Index E J → Matrix I I Binary) →ₗ[Binary] Matrix (RowIndex r inc J) N Binary :=
  (pack inc).comp (fullObservations Z D)

noncomputable def rowLinear {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) : (N → Binary) →ₗ[Binary] Rows r inc J :=
  (rowMap inc Z (fun j e f => M (false, j, e, f))
    (fun j e f => M (true, j, e, f))).comp D.mulVecLin

axiom mixerRows_rank {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) :
    (mixerRows inc Z D M).rank = Module.finrank Binary (LinearMap.range (rowLinear inc Z D M))

open scoped ENNReal

axiom joint_row_law [DecidableEq E] [DecidableEq I] [DecidableEq N]
    {r : E → ℕ} (inc : Finset E) {J K : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec)
    (hr : ∑ e, r e ≤ K) (y : Matrix (RowIndex r inc J) N Binary) :
    (PMF.uniformOfFintype (Index E J → Matrix I I Binary)).map (mixerRows inc Z D) y ≤
      2 ^ (2 * J * K ^ 2) * PMF.uniformOfFintype (Matrix (RowIndex r inc J) N Binary) y

axiom row_corank_bound [DecidableEq E] [DecidableEq I] [DecidableEq N]
    {r : E → ℕ} (inc : Finset E) {J K : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (hZ : ∀ e, Function.Injective (Z e).mulVec) (hD : Function.Injective D.mulVec)
    (hr : ∑ e, r e ≤ K) (s : ℕ) :
    (PMF.uniformOfFintype (Index E J → Matrix I I Binary)).toOuterMeasure
      {M | (mixerRows inc Z D M).rank + s ≤ Fintype.card (RowIndex r inc J)} ≤
        (2 : ℝ≥0∞) ^ (2 * J * K ^ 2 + s * (4 * J * inc.card * K)) / 2 ^ (s * Fintype.card N)

def leftMixers {J : ℕ} (M : Index E J → Matrix I I Binary) : Fin J → E → E → Matrix I I Binary :=
  fun j e f => M (false, j, e, f)

def rightMixers {J : ℕ} (M : Index E J → Matrix I I Binary) : Fin J → E → E → Matrix I I Binary :=
  fun j e f => M (true, j, e, f)

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

def UnaryBad {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (x : Profile k n b degree)
    (l : Tag k) (s : Fin b → Binary) (s₀ : ℕ)
    (M : Index (Component (Tag k)) J → Moment k n b degree) : Prop :=
  ∃ z : Base k n → Binary, ∃ hz : ∀ i, i ∉ allowedBase k n l → z i = 0,
    (FormalQuadratic.polarMatrix (fun v =>
      gradient D (leftMixers M) (rightMixers M) x (atomAlongZ l s z hz v))).rank < 2 * (J - s₀)

axiom unary_failure_probability {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) (hx : x ≠ 0) (hK : ∑ e, (x.val e).rank ≤ K)
    (l : Tag k) (s : Fin b → Binary) (s₀ : ℕ) :
    (PMF.uniformOfFintype (Index (Component (Tag k)) J → Moment k n b degree)).toOuterMeasure
      {M | UnaryBad D x l s s₀ M} ≤
        (2 : ℝ≥0∞) ^ (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)) / 2 ^ ((s₀ + 1) * n)

end Lax342547.UnaryRowLaw
