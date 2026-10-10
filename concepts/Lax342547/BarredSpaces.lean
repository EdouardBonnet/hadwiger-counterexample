import Lax342547.PairedAnnihilators
import Lax342547.PairedKeys

/-!
---
title: Barred response spaces and the actual obstruction rank budget
type: definition and theorem
---
Quotient the nominal spaces by frozen pins, selected incident keys, and
private channel directions. Individual primal projections have kernel
budget K+14, giving the paper's component obstruction bound 2K+28.
-/

namespace Lax342547.BarredSpaces

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedKeys
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.PairedAnnihilators

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

noncomputable def individualDirection (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) (x : Σ z, Fin (W.length i z)) : Vector k n b degree := by
  classical
  exact if (W.left i x.1 x.2).tag ∈ e.val then (W.left i x.1 x.2).vector else 0

def individualKeys (W : Lists k n b degree r hr) (i : Fin 2) (e : Component (Tag k)) :
    Submodule Binary (Vector k n b degree) :=
  Submodule.span Binary (Set.range (individualDirection W i e))

def barred (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool) :
    Submodule Binary (Nominal (Coordinate k n b degree) H) :=
  P.space a ⊔ keys (H := H) W a.1 ⊔ ⨆ z, (U z).map (channelEmbedding z)

axiom individual_key_dimension (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) : Module.finrank Binary (individualKeys W i e) ≤ 14

axiom barred_projection (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool) (i : Fin 2) :
    (barred W P U a).map (primalProjection i) ≤ projected P i a ⊔ individualKeys W i a.1

axiom annihilator_component_rank [Fintype H] {K : ℕ}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Fin 2 → Submodule Binary (H → Binary))
    (e : Component (Tag k)) (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, true)) (barred W P V (e, false))) :
    ∀ i, (M i).rank ≤ 2 * K + 28

end Lax342547.BarredSpaces
