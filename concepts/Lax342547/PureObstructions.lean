import Lax342547.BarredSpaces
import Lax342547.LabelDecomposition

/-!
---
title: Pure obstructions on the actual pair of cut profiles
type: definition and theorem
---
The independent component responses on barred nominal quotients define
functionals on the pair of actual cut profiles. Annihilation gives the
2K+28 component-rank bound and hence a bounded label decomposition.
Derivative responses and the final obstruction-space reduction remain
separate obligations.
-/

namespace Lax342547.PureObstructions

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PairedAnnihilators Lax342547.BarredSpaces
open Lax342547.BaseMoments

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

abbrev Parameters (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) :=
  ∀ e, (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
    (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary] Binary

def endpointComponent (e : Component (Tag k)) :
    (Fin 2 → Profile k n b degree) →ₗ[Binary] (Fin 2 → Moment k n b degree) where
  toFun x i := (x i).val e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def response (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (β : Parameters W P U V) : (Fin 2 → Profile k n b degree) →ₗ[Binary] Binary :=
  ∑ e, (pureResponse (barred W P (U e) (e, true))
    (barred W P (V e) (e, false)) (β e)).comp (endpointComponent e)

def Annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) : Prop := ∀ β, response W P U V β x = 0

axiom component_annihilation (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (e : Component (Tag k)) :
    PairedAnnihilates (endpointComponent e x)
      (barred W P (U e) (e, true)) (barred W P (V e) (e, false))

axiom component_rank [Fintype H] {K : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x) :
    ∀ i e, ((x i).val e).rank ≤ 2 * K + 28

axiom component_labels [Fintype H] {K : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∀ i e, ∃ L : Finset (Fin b → Binary),
    ∃ Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary,
      L.card ≤ 2 * K + 28 ∧ (∀ s ∈ L, IsBaseMoment (Z s)) ∧
      (∑ s ∈ L, (Z s).rank) ≤ 2 * K + 28 ∧
      ∀ a c, (x i).val e a c = ∑ s ∈ L, selectorEval s a.1 * selectorEval s c.1 * Z s a.2 c.2

end Lax342547.PureObstructions
