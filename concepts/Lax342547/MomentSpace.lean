import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Boolean point moments with restricted base coordinates
type: definition
---
The selector evaluations and the constant/base coordinates of §2.3.
Keeping the selector evaluation map as a parameter lets the coordinate
projection arguments apply at every selector degree.
-/

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

instance (b degree : ℕ) : DecidableEq (SelectorCoordinates b degree) :=
  inferInstanceAs (DecidableEq {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

def point (p : Label → Coord → Binary) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) : Binary := p s i.1 * baseEval z i.2

def pointMoment (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary :=
  fun i j => point p s z i * point p s z j

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

def allowed (A : Set Base) (i : Coord × Option Base) : Prop :=
  match i.2 with
  | none => True
  | some b => b ∈ A

noncomputable def mask (A : Set Base) (i : Coord × Option Base) : Binary :=
  by classical exact if allowed A i then 1 else 0

noncomputable def project (A : Set Base) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary →ₗ[Binary]
      Matrix (Coord × Option Base) (Coord × Option Base) Binary where
  toFun w i j := mask A i * w i j * mask A j
  map_add' w v := by
    ext i j
    change mask A i * (w i j + v i j) * mask A j =
      mask A i * w i j * mask A j + mask A i * v i j * mask A j
    simp [mul_add, add_mul]
  map_smul' c w := by
    ext i j
    change mask A i * (c * w i j) * mask A j = c * (mask A i * w i j * mask A j)
    simp [mul_assoc, mul_left_comm]

noncomputable def eraseBase (A : Set Base) (z : Base → Binary) (i : Base) : Binary :=
  by classical exact if i ∈ A then z i else 0

end Lax342547.MomentSpace
