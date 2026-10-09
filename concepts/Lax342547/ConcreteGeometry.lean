import Lax342547.TagGeometry
import Lax342547.GradientForm
import Lean.Elab.Tactic.Omega

/-!
---
title: Concrete coordinates, quadratic testers, and the self-Gram form
type: definition and theorem
---
The coordinate realization of §2.3. The three common blocks are indexed
by 0 (S), 1 (#), and 2 (Z). Tester pairs use coordinates 2ρ and 2ρ+1
in zero-based indexing. The self-Gram matrix has the ordered tester
part and the selector-dependent # part; it has no Z entries.
-/

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)
noncomputable instance (k n b degree : ℕ) : DecidableEq (Coordinate k n b degree) := Classical.decEq _
abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary
abbrev Moment (k n b degree : ℕ) := Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary

def ordinary {k n : ℕ} (d t : Tag k) (i : Fin n) : Base k n := Sum.inl ((d, t), i)
def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)
def sharp {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (1, i)
def free {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (2, i)

def emptySelector (b degree : ℕ) : SelectorCoordinates b degree := ⟨∅, Nat.zero_le _⟩
def bitSelector {b degree : ℕ} (h : 1 ≤ degree) (a : Fin b) : SelectorCoordinates b degree :=
  ⟨{a}, by simpa using h⟩

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩
def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

def matrixEntry {I : Type} (i j : I) : Matrix I I Binary →ₗ[Binary] Binary where
  toFun w := w i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockTester {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    Moment k n b degree →ₗ[Binary] Binary :=
  ∑ ρ : Fin r, matrixEntry (emptySelector b degree, some (c (pairLeft h ρ)))
    (emptySelector b degree, some (c (pairRight h ρ)))

def etaO {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  ∑ d : Tag k, ∑ t : Tag k, blockTester h (ordinary d t)

def eta {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  etaO h + blockTester h shared

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

def testerForm {k n b degree r : ℕ} (h : 2 * r ≤ n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  (∑ d : Tag k, ∑ t : Tag k, blockForm h (ordinary d t)) + blockForm h shared

def sharpForm {k n b degree : ℕ} (h : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ a : Fin b, ∑ i : Fin n, ∑ j : Fin n, M a i j •
    (GradientForm.rankOne (LinearMap.proj (bitSelector h a, some (sharp i)))
      (LinearMap.proj (emptySelector b degree, some (sharp j))) +
    GradientForm.rankOne (LinearMap.proj (emptySelector b degree, some (sharp i)))
      (LinearMap.proj (bitSelector h a, some (sharp j))))

noncomputable def selfGram {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Moment k n b degree :=
  (testerForm hr + sharpForm hd M).toMatrix'

def matrixPair {I : Type} [Fintype I] (E : Matrix I I Binary) :
    Matrix I I Binary →ₗ[Binary] Binary :=
  ∑ i, ∑ j, E i j • matrixEntry i j

/-- The action on all coefficient vectors induced by a common Z-coordinate change. -/
def changeZ {k n b degree : ℕ} (A : Matrix (Fin n) (Fin n) Binary) :
    Vector k n b degree →ₗ[Binary] Vector k n b degree where
  toFun v c := match c.2 with
    | some (Sum.inr (q, i)) => if q = 2 then ∑ j, A i j * v (c.1, some (free j)) else v c
    | _ => v c
  map_add' v w := by
    ext ⟨S, c⟩
    cases c with
    | none => rfl
    | some c =>
      cases c with
      | inl c => rfl
      | inr c =>
        rcases c with ⟨q, i⟩
        by_cases hq : q = 2 <;> simp [hq, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    ext ⟨S, c⟩
    cases c with
    | none => rfl
    | some c =>
      cases c with
      | inl c => rfl
      | inr c =>
        rcases c with ⟨q, i⟩
        by_cases hq : q = 2 <;> simp [hq, Finset.mul_sum, mul_left_comm]

axiom selfGram_moments {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (w : Moment k n b degree)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ) :
    matrixPair (selfGram hr hd M) w = eta hr w

axiom selfGram_changeZ {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (A : Matrix (Fin n) (Fin n) Binary) :
    (changeZ A).toMatrix'.transpose * selfGram (k := k) (b := b) hr hd M *
      (changeZ A).toMatrix' = selfGram hr hd M

end Lax342547.ConcreteGeometry
