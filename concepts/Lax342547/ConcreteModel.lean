import Lax342547.ConcreteCut
import Lax342547.RawLaw
import Lax342547.SampledGraph

/-!
---
title: The concrete finite frame model and its sampled graphs
type: lemma
---
Assemble the actual moment coordinates, cut-profile space, descended
testers, ordered mixer form, self-Gram matrix, frame tensors, and uniform
raw law. This algebraic construction works for arbitrary mixers. It does
not assert a connected-matching bound for those arbitrary choices.
-/

namespace Lax342547.ConcreteModel

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.ConcreteCut Lax342547.RawFrames
open Lax342547.HoleRelation Lax342547.SampledGraph
open scoped ENNReal

abbrev RawVertex {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (h N : ℕ) :=
  Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)

abbrev Ambient (k N : ℕ) := Component (Tag k) → Matrix (Fin N) (Fin N) Binary

structure Model {k n b degree r J h N : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) where
  testers : Testers (k := k) (b := b) (degree := degree) hr
  frame : Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)
  holes : HoleData (RawVertex (k := k) hr hd M h N) (Profile k n b degree) (Ambient k N)
  role_eq : holes.a = testers.role
  gradient_eq : holes.T = gradient testers L R
  embedding_eq : ∀ o, holes.U o = (profileMap o).comp (Profile k n b degree).subtype
  contraction_eq : ∀ o, holes.u o = profileContraction o
  hole_symmetric : ∀ {i j}, Hole holes i j → Hole holes j i
  law : PMF (RawVertex (k := k) hr hd M h N)
  law_uniform : ∀ o, law o = (Fintype.card (RawVertex (k := k) hr hd M h N) : ℝ≥0∞)⁻¹

noncomputable def graph {k n b degree r J h N m : ℕ} {hr : 2 * r ≤ n} {hd : 1 ≤ degree}
    {M : Fin b → Matrix (Fin n) (Fin n) Binary}
    {L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree}
    (D : Model (h := h) (N := N) hr hd M L R) (sample : Fin m → RawVertex (k := k) hr hd M h N) :
    SimpleGraph (Fin m) := sampleGraph (Hole D.holes) (fun {_ _} hij => D.hole_symmetric hij) sample

axiom exists_model {k n b degree r J h N : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) ≤ N) :
    Nonempty (Model (h := h) (N := N) hr hd M L R)

axiom graph_indepNum_le_two {k n b degree r J h N m : ℕ} {hr : 2 * r ≤ n} {hd : 1 ≤ degree}
    {M : Fin b → Matrix (Fin n) (Fin n) Binary}
    {L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree}
    (D : Model (h := h) (N := N) hr hd M L R) (sample : Fin m → RawVertex (k := k) hr hd M h N) :
    (graph D sample).indepNum ≤ 2

end Lax342547.ConcreteModel
