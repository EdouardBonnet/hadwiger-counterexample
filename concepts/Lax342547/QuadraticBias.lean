import Lax342547.Walsh
import Lax342547.FiniteLinearLaw
import Lax342547.RestrictionRank
import Lax342547.FormalQuadratic

/-!
---
title: Quadratic character bias on affine subspaces
type: definition and theorem
---
Translation and character orthogonality give the actual quadratic sign bias from polar rank and its affine-subspace restriction.
-/

namespace Lax342547.QuadraticBias

open Lax342547.MomentSpace Lax342547.Walsh
open scoped BigOperators

axiom square_translation {V : Type} [AddCommGroup V] [Fintype V]
    (f : V → ℝ) :
    (∑ x, f x)^2 = ∑ h, ∑ x, f x*f (x+h)

axiom polar_sign_product {V : Type} [AddCommGroup V] [Module Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) (x h : V) :
    sign (Q x)*sign (Q (x+h)) = sign (Q h+Q 0)*sign (B h x)

axiom quadratic_sign_square {V : Type} [AddCommGroup V] [Module Binary V] [Fintype V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) :
    by
      classical
      exact (∑ x, sign (Q x))^2 = (Fintype.card V : ℝ)*
      ∑ h ∈ Finset.univ.filter (fun h => B h = 0),sign (Q h+Q 0)

axiom quadratic_bias_square_bound {V : Type} [AddCommGroup V] [Module Binary V]
    [Fintype V] [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) :
    ((∑ x, sign (Q x))/(Fintype.card V : ℝ))^2 ≤
      1/(2 : ℝ)^Module.finrank Binary (LinearMap.range B)

axiom quadratic_bias_rank_bound {V : Type} [AddCommGroup V] [Module Binary V]
    [Fintype V] [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V) (r : ℕ)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (hrank : 2*r ≤ Module.finrank Binary (LinearMap.range B)) :
    |(∑ x, sign (Q x))/(Fintype.card V : ℝ)| ≤ 1/(2 : ℝ)^r

axiom affine_restricted_polar {V : Type} [AddCommGroup V] [Module Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (S : Submodule Binary V) (w : V) (x h : S) :
    Q (w+(x+h).val)+Q (w+x.val)+Q (w+h.val)+Q w = (B.restrict S) h x

axiom affine_subspace_bias {V : Type} [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V) (S : Submodule Binary V) [Fintype S]
    (w : V) (r c : ℕ)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (hrank : 2*r ≤ Module.finrank Binary (LinearMap.range B))
    (hcodim : Module.finrank Binary V ≤ Module.finrank Binary S+c) :
    |(∑ x : S, sign (Q (w+x.val)))/(Fintype.card S : ℝ)| ≤ 1/(2 : ℝ)^(r-c)

end Lax342547.QuadraticBias
