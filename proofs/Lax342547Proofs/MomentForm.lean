import Lax342547Proofs.SelectorInterpolation
import Lax342547Proofs.GramRank
import Mathlib.LinearAlgebra.Span.Basic

set_option backward.isDefEq.respectTransparency false

namespace Lax342547Proofs.MomentForm

open Lax342547.MomentSpace

variable {Base : Type} {b : ℕ}

abbrev PointDomain (Base : Type) (b : ℕ) := (Fin b → Binary) × (Base → Binary)

def feature (degree : ℕ) (i : SelectorCoordinates b degree × Option Base) :
    PointDomain Base b → Binary := fun ω => point selectorEval ω.1 ω.2 i

def functions (Base : Type) (b degree : ℕ) : Submodule Binary (PointDomain Base b → Binary) :=
  Submodule.span Binary (Set.range (feature (Base := Base) (b := b) degree))

theorem feature_mem (degree : ℕ) (i : SelectorCoordinates b degree × Option Base) :
    feature degree i ∈ functions Base b degree := Submodule.subset_span ⟨i, rfl⟩

theorem functions_mono {d e : ℕ} (h : d ≤ e) : functions Base b d ≤ functions Base b e := by
  apply Submodule.span_le.mpr
  rintro f ⟨⟨S, i⟩, rfl⟩
  exact feature_mem e (⟨S.val, S.property.trans h⟩, i)

def selectorMul (a : Fin b) : (PointDomain Base b → Binary) →ₗ[Binary]
    (PointDomain Base b → Binary) where
  toFun f ω := ω.1 a * f ω
  map_add' f g := by ext ω; exact mul_add _ _ _
  map_smul' c f := by ext ω; exact mul_left_comm _ _ _

theorem selectorMul_feature (a : Fin b) (degree : ℕ)
    (i : SelectorCoordinates b degree × Option Base) :
    selectorMul a (feature degree i) =
      feature (degree + 1)
        (⟨insert a i.1.val, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right i.1.property 1)⟩,
          i.2) := by
  ext ω
  change ω.1 a * (selectorEval ω.1 i.1 * baseEval ω.2 i.2) =
    Lax342547.SelectorInterpolation.monomial (insert a i.1.val) ω.1 * baseEval ω.2 i.2
  rw [SelectorInterpolation.monomial_insert, mul_assoc]
  rfl

theorem selectorMul_mem (a : Fin b) (degree : ℕ) {f : PointDomain Base b → Binary}
    (hf : f ∈ functions Base b degree) : selectorMul a f ∈ functions Base b (degree + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    rw [selectorMul_feature]
    exact feature_mem _ _
  | zero => simp
  | add f g _ _ hf hg => simpa using (functions Base b (degree + 1)).add_mem hf hg
  | smul c f _ hf => simpa using (functions Base b (degree + 1)).smul_mem c hf

section Pairing

variable [Fintype Base] [DecidableEq Base]

def weightedPairing (c : PointDomain Base b → Binary) :
    LinearMap.BilinForm Binary (PointDomain Base b → Binary) where
  toFun f :=
    { toFun := fun g => ∑ ω, c ω * f ω * g ω
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_left_comm, ← Finset.mul_sum] }
  map_add' f g := by
    ext h
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext g
    simp [mul_left_comm, mul_assoc, ← Finset.mul_sum]

theorem weightedPairing_apply (c : PointDomain Base b → Binary)
    (f g : PointDomain Base b → Binary) :
    weightedPairing c f g = ∑ ω, c ω * f ω * g ω := rfl

theorem weightedPairing_symm (c : PointDomain Base b → Binary) :
    (weightedPairing c).IsSymm := by
  constructor
  intro f g
  unfold weightedPairing
  dsimp
  exact Finset.sum_congr rfl (fun _ _ => mul_right_comm _ _ _)

theorem weightedPairing_shift (c : PointDomain Base b → Binary) (a : Fin b)
    (f g : PointDomain Base b → Binary) :
    weightedPairing c (selectorMul a f) g = weightedPairing c f (selectorMul a g) := by
  apply Finset.sum_congr rfl
  intro ω _
  change c ω * (ω.1 a * f ω) * g ω = c ω * f ω * (ω.1 a * g ω)
  ring

theorem weightedPairing_shift_square (c : PointDomain Base b → Binary) (a : Fin b)
    (f g : PointDomain Base b → Binary) :
    weightedPairing c (selectorMul a f) (selectorMul a g) =
      weightedPairing c (selectorMul a f) g := by
  apply Finset.sum_congr rfl
  intro ω _
  change c ω * (ω.1 a * f ω) * (ω.1 a * g ω) = c ω * (ω.1 a * f ω) * g ω
  calc
    _ = c ω * (ω.1 a * ω.1 a) * f ω * g ω := by ring
    _ = _ := by rw [BaseMoments.binary_mul_self]; ring

theorem weightedPairing_shifts_commute (c : PointDomain Base b → Binary) (a a' : Fin b)
    (f g : PointDomain Base b → Binary) :
    weightedPairing c (selectorMul a f) (selectorMul a' g) =
      weightedPairing c (selectorMul a' f) (selectorMul a g) := by
  apply Finset.sum_congr rfl
  intro ω _
  change c ω * (ω.1 a * f ω) * (ω.1 a' * g ω) =
    c ω * (ω.1 a' * f ω) * (ω.1 a * g ω)
  ring

def momentMatrix (c : PointDomain Base b → Binary) (degree : ℕ) :
    Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary :=
  ∑ ω, c ω • pointMoment selectorEval ω.1 ω.2

theorem momentMatrix_eq_gram (c : PointDomain Base b → Binary) (degree : ℕ) :
    momentMatrix c degree = GramRank.gram (weightedPairing c) (feature degree) := by
  ext i j
  simp only [momentMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω _
  change c ω * (point selectorEval ω.1 ω.2 i * point selectorEval ω.1 ω.2 j) =
    c ω * point selectorEval ω.1 ω.2 i * point selectorEval ω.1 ω.2 j
  exact (mul_assoc _ _ _).symm

theorem rank_momentMatrix (c : PointDomain Base b → Binary) (degree : ℕ) :
    (momentMatrix c degree).rank = Module.finrank Binary
      (LinearMap.range ((weightedPairing c).restrict (functions Base b degree))) := by
  rw [momentMatrix_eq_gram]
  exact GramRank.rank_gram_span _ (weightedPairing_symm c) _

theorem moment_rank_monotone (c : PointDomain Base b → Binary) :
    Monotone (fun degree => (momentMatrix c degree).rank) := by
  intro d e hde
  exact (rank_momentMatrix c d).le.trans
    ((GramRank.restrict_rank_mono _ (weightedPairing_symm c) (functions_mono hde)).trans
      (rank_momentMatrix c e).ge)

theorem exists_weights (degree : ℕ)
    (w : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ) :
    ∃ c : PointDomain Base b → Binary, momentMatrix c degree = w := by
  have he : {w | ∃ s z, (∀ i : Base, i ∉ Set.univ → z i = 0) ∧
      w = pointMoment (selectorEval (degree := degree)) s z} =
      Set.range (fun ω : PointDomain Base b => pointMoment (selectorEval (degree := degree)) ω.1 ω.2) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ, not_true_eq_false, IsEmpty.forall_iff,
      implies_true, true_and, Set.mem_range, Prod.exists]
    exact ⟨fun ⟨s, z, h⟩ => ⟨s, z, h.symm⟩, fun ⟨s, z, h⟩ => ⟨s, z, h.symm⟩⟩
  change w ∈ Submodule.span Binary _ at hw
  rw [he] at hw
  exact (Submodule.mem_span_range_iff_exists_fun Binary).mp hw

end Pairing

end Lax342547Proofs.MomentForm
