import Lax342547.TargetTesters

/-!
---
title: Explicit low-rank matrices for the whole-space gradient target
type: lemma
---
The adjoints of the concrete mixer sandwiches have ranks bounded by the witness component ranks. Combining both orientations with the routed tester matrices constructs the actual target matrices, proves the rank 15r+14J|E|, and represents the whole profile-pair target exactly.
-/

namespace Lax342547.TargetMatrices

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms
open Lax342547.PairedWitnesses Lax342547.WitnessAtoms Lax342547.TargetTesters

axiom sandwich_adjoint {B : Type} [Fintype B] (M W L R : Matrix B B Binary) :
    matrixPair M (L * W * R.transpose) = matrixPair (L.transpose * M * R) W

noncomputable def mixerMatrix {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (v : Profile k n b degree) (e : Component (Tag k)) : Moment k n b degree :=
  (∑ j, ∑ f, (L j f e).transpose * v.val f * R j f e) +
    ∑ j, ∑ f, L j e f * v.val f * (R j e f).transpose

axiom mixer_matrix_representation {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (v x : Profile k n b degree) :
    (∑ e, matrixPair (mixerMatrix L R v e) (x.val e)) = mixingForm L R v x + mixingForm L R x v

axiom witness_component_rank {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) (e : Component (Tag k)) :
    ((leftWitness W i z).val e).rank ≤ 7

axiom mixer_matrix_rank {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (v : Profile k n b degree) (S : ℕ) (hS : ∀ f, (v.val f).rank ≤ S)
    (e : Component (Tag k)) : (mixerMatrix L R v e).rank ≤
      2 * J * Fintype.card (Component (Tag k)) * S

noncomputable def targetMatrix {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (i z : Fin 2) (e : Component (Tag k)) : Moment k n b degree :=
  witnessTesterMatrix W D i z e + mixerMatrix L R (leftWitness W i z) e

axiom target_matrix_rank {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (i z : Fin 2) (e : Component (Tag k)) :
    (targetMatrix W D L R i z e).rank ≤ 15 * r + 14 * J * Fintype.card (Component (Tag k))

axiom target_matrix_representation {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (i z : Fin 2) (hodd : (∑ j, diagonalBit hr (W.left i z j)) = 1)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (targetMatrix W D L R i z e) (x.val e)) =
      (D.role + gradient D L R (leftWitness W i z)) x

axiom target_family_representation {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (z : Fin 2) (hodd : ∀ i, (∑ j, diagonalBit hr (W.left i z j)) = 1) :
    Lax342547.ResidualRealization.matrixResponse (Profile k n b degree) (fun i => targetMatrix W D L R i z) =
      ∑ i, (D.role + gradient D L R (leftWitness W i z)).comp (LinearMap.proj i)

end Lax342547.TargetMatrices
