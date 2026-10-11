import Lax342547.FormalQuadratic
import Lax342547.RestrictionRank
import Lax342547.AtomDirections
import Lax342547.Atoms

/-!
---
title: Formal forward and reverse rows of a unary mixer test
type: lemma
---
For a fixed rank profile, each forward and reverse product receives
its own pair of formal row vectors. The substitution map records the
actual mixer restrictions. Its restriction to the Z direction matrix
is chosen before any non-Z coordinates or flavor are fixed.
-/

namespace Lax342547.UnaryMixer

open Lax342547.MomentSpace

variable {E I : Type} [Fintype E] [Fintype I]

abbrev Block (inc : Finset E) (J : ℕ) :=
  (Fin J × E × {f : E // f ∈ inc}) ⊕ (Fin J × {e : E // e ∈ inc} × E)

def blockRank (r : E → ℕ) {inc : Finset E} {J : ℕ} : Block inc J → ℕ
  | .inl (_, e, _) => r e
  | .inr (_, _, f) => r f

abbrev Rows (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  FormalQuadratic.Rows (fun t : Block inc J => Fin (blockRank r t) → Binary)

noncomputable def middle {r : E → ℕ} {inc : Finset E} {J : ℕ}
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary) :
    ∀ t : Block inc J, LinearMap.BilinForm Binary (Fin (blockRank r t) → Binary)
  | .inl (_, e, _) => (H e).toBilin'
  | .inr (_, _, f) => (H f).toBilin'

noncomputable def rowMap {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary)
    (L R : Fin J → E → E → Matrix I I Binary) : (I → Binary) →ₗ[Binary] Rows r inc J :=
  LinearMap.pi fun t => match t with
    | .inl (j, e, f) =>
        ((Z e).transpose * L j e f.val).mulVecLin.prod
          ((Z e).transpose * R j e f.val).mulVecLin
    | .inr (j, e, f) =>
        ((L j e.val f * Z f).transpose).mulVecLin.prod
          ((R j e.val f * Z f).transpose).mulVecLin

noncomputable def formalQuadratic {r : E → ℕ} (inc : Finset E) (J : ℕ)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary) : QuadraticForm Binary (Rows r inc J) :=
  FormalQuadratic.quadratic (middle H)

axiom formal_rank {r : E → ℕ} (inc : Finset E) (J : ℕ)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hH : ∀ e, Function.Injective (H e).mulVec) :
    Module.finrank Binary (LinearMap.range (formalQuadratic inc J H).polarBilin) =
      4 * J * inc.card * ∑ e, r e

axiom substitution_rank {r : E → ℕ} (inc : Finset E) (J : ℕ)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    {U : Type} [AddCommGroup U] [Module Binary U]
    (A : U →ₗ[Binary] Rows r inc J) (s : ℕ)
    (hA : Module.finrank Binary (Rows r inc J) ≤
      Module.finrank Binary (LinearMap.range A) + s) :
    4 * J * inc.card * ∑ e, r e ≤
      Module.finrank Binary (LinearMap.range (LinearMap.compl₁₂
        (formalQuadratic inc J H).polarBilin A A)) + 2 * s

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.CutProfiles Lax342547.Atoms

noncomputable def incident {k : ℕ} (l : Tag k) : Finset (Component (Tag k)) := by
  classical
  exact Finset.univ.filter (fun e => l ∈ e.val)

axiom incident_card {k : ℕ} (l : Tag k) : (incident l).card = 2 * k

noncomputable def zRows {k n b degree J : ℕ} {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) : (Fin n → Binary) →ₗ[Binary] Rows r (incident l) J :=
  (rowMap (incident l) Z L R).comp (AtomDirections.blockDirections s free).mulVecLin

noncomputable def zRowSpace {k n b degree J : ℕ} {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) : Submodule Binary (Module.Dual Binary (Fin n → Binary)) :=
  LinearMap.range (zRows Z L R l s).dualMap

axiom row_space_dimension {k n b degree J K : ℕ} {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (hrank : ∑ e, r e ≤ K) :
    Module.finrank Binary (zRowSpace Z L R l s) ≤ 4 * J * (2 * k) * K

def testerTerm {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  GradientForm.form D.role D.aTag D.bTag 0

noncomputable def atomAlongZ {k n b degree : ℕ}
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0)
    (v : Fin n → Binary) : Profile k n b degree :=
  atom l s (AtomDirections.varyBlock z free v) (by
    classical
    intro i hi
    cases i with
    | inl i => simpa [AtomDirections.varyBlock, free] using hz (.inl i) hi
    | inr i => exact False.elim (hi trivial))

axiom unary_affine_quadratic {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (v : Fin n → Binary) :
    gradient D L R x (atomAlongZ l s z hz v) =
      testerTerm D x (atom l s z hz) + formalQuadratic (incident l) J H
        (rowMap (incident l) Z L R (point selectorEval s z) + zRows Z L R l s v)

axiom unary_polar {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (u v : Fin n → Binary) :
    FormalQuadratic.affinePolar (fun w => gradient D L R x (atomAlongZ l s z hz w)) u v =
      (formalQuadratic (incident l) J H).polarBilin (zRows Z L R l s u) (zRows Z L R l s v)

axiom unary_depends_on_rows {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (u v : Fin n → Binary)
    (hrows : ∀ a ∈ zRowSpace Z L R l s, a u = a v) :
    gradient D L R x (atomAlongZ l s z hz u) = gradient D L R x (atomAlongZ l s z hz v)

axiom mixer_atom_expansion {k n b degree J : ℕ}
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) :
    mixingForm L R x (atom l s z hz) + mixingForm L R (atom l s z hz) x =
      formalQuadratic (incident l) J H (rowMap (incident l) Z L R (point selectorEval s z))

axiom unary_rank_bound {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (s₀ : ℕ)
    (hA : Module.finrank Binary (Rows r (incident l) J) ≤
      Module.finrank Binary (LinearMap.range (zRows Z L R l s)) + s₀) :
    4 * J * (incident l).card * ∑ e, r e ≤
      (FormalQuadratic.polarMatrix (fun w => gradient D L R x (atomAlongZ l s z hz w))).rank + 2 * s₀

axiom unary_rank_lower {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n} (hk : 0 < k)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (x : Profile k n b degree) (hx : x ≠ 0) {r : Component (Tag k) → ℕ}
    (Z : ∀ e, Matrix (Coordinate k n b degree) (Fin (r e)) Binary)
    (H : ∀ e, Matrix (Fin (r e)) (Fin (r e)) Binary)
    (hfactor : ∀ e, Z e * H e * (Z e).transpose = x.val e)
    (hH : ∀ e, Function.Injective (H e).mulVec)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (s₀ : ℕ)
    (hA : Module.finrank Binary (Rows r (incident l) J) ≤
      Module.finrank Binary (LinearMap.range (zRows Z L R l s)) + s₀) :
    2 * (J - s₀) ≤
      (FormalQuadratic.polarMatrix (fun w => gradient D L R x (atomAlongZ l s z hz w))).rank

end Lax342547.UnaryMixer
