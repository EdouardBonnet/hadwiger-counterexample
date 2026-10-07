import Lax342547Proofs.MomentForm
import Lax342547Proofs.FlatMap
import Lax342547Proofs.JointProjectors

namespace Lax342547Proofs.FlatSelector

open Lax342547.MomentSpace Lax342547.FlatRank
open MomentForm

variable {Base : Type} [Fintype Base] [DecidableEq Base] {b : ℕ}

def form (c : PointDomain Base b → Binary) (j : ℕ) :
    LinearMap.BilinForm Binary (functions Base b (j + 2)) :=
  (weightedPairing c).restrict (functions Base b (j + 2))

abbrev QuotientSpace (c : PointDomain Base b → Binary) (j : ℕ) :=
  functions Base b (j + 2) ⧸ (form c j).ker

def lowInclusion (j : ℕ) : functions Base b j →ₗ[Binary] functions Base b (j + 2) :=
  Submodule.inclusion (functions_mono (by omega))

def shift (j : ℕ) (a : Fin b) : functions Base b j →ₗ[Binary] functions Base b (j + 2) :=
  LinearMap.codRestrict (functions Base b (j + 2))
    ((selectorMul a).comp (functions Base b j).subtype)
    (fun f => functions_mono (by omega) (selectorMul_mem a j f.property))

def lowClass (c : PointDomain Base b → Binary) (j : ℕ) :
    functions Base b j →ₗ[Binary] QuotientSpace c j := (form c j).ker.mkQ.comp (lowInclusion j)

theorem form_symm (c : PointDomain Base b → Binary) (j : ℕ) : (form c j).IsSymm :=
  ⟨fun x y => (weightedPairing_symm c).eq x y⟩

theorem rank_pullback (c : PointDomain Base b → Binary) (j : ℕ)
    (hflat : (momentMatrix c j).rank = (momentMatrix c (j + 2)).rank) :
    Module.finrank Binary (LinearMap.range ((form c j).comp (lowInclusion j) (lowInclusion j))) =
      Module.finrank Binary (LinearMap.range (form c j)) :=
  (rank_momentMatrix c j).symm.trans (hflat.trans (rank_momentMatrix c (j + 2)))

theorem lowClass_surjective (c : PointDomain Base b → Binary) (j : ℕ)
    (hflat : (momentMatrix c j).rank = (momentMatrix c (j + 2)).rank) :
    Function.Surjective (lowClass c j) :=
  FlatMap.quotient_map_surjective (form c j) (form_symm c j) (lowInclusion j)
    (rank_pullback c j hflat)

theorem exists_operators (c : PointDomain Base b → Binary) (j : ℕ)
    (hflat : (momentMatrix c j).rank = (momentMatrix c (j + 2)).rank) :
    ∃ M : Fin b → Module.End Binary (QuotientSpace c j),
      (∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f)) ∧
      (∀ a x y, quotientPairing (form c j) (form_symm c j) (M a x) y =
        quotientPairing (form c j) (form_symm c j) x (M a y)) ∧
      (∀ a, M a * M a = M a) ∧ ∀ a a', M a * M a' = M a' * M a := by
  apply FlatMap.exists_commuting_idempotents (form c j) (form_symm c j) (lowInclusion j)
    (rank_pullback c j hflat) (shift j)
  · intro a f g
    exact weightedPairing_shift c a f g
  · intro a f g
    exact weightedPairing_shift_square c a f g
  · intro a a' f g
    exact weightedPairing_shifts_commute c a a' f g

theorem quotient_finrank (c : PointDomain Base b → Binary) (j : ℕ) :
    Module.finrank Binary (QuotientSpace c j) = (momentMatrix c (j + 2)).rank :=
  (FlatRank.quotient_finrank (form c j)).trans (rank_momentMatrix c (j + 2)).symm

theorem exists_flat_level (c : PointDomain Base b → Binary) (J R : ℕ)
    (hr : (momentMatrix c J).rank ≤ R) (hroom : 6 * R + 4 ≤ J) :
    ∃ j, 4 * R + 2 ≤ j ∧ j + 2 ≤ J ∧
      (momentMatrix c j).rank = (momentMatrix c (j + 2)).rank := by
  obtain ⟨j, hj, hJ, h₀, h₁⟩ := FlatRank.exists_flat_level
    (fun d => (momentMatrix c d).rank) (4 * R + 2) R J
    (moment_rank_monotone c) (fun d hd => ((moment_rank_monotone c) hd).trans hr) (by omega)
  exact ⟨j, hj, hJ, h₀.trans h₁⟩

end Lax342547Proofs.FlatSelector
