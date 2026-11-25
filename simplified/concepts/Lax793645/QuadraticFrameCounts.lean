import Lax793645.ConstructionData

/-!
---
title: Counting a new frame column
type: lemma
---
Fix an independent list in a binary quadratic space and prescribe the polar pairings
and the quadratic value of the next column. A signed count gives the size of this
fiber. Lists with the same quadratic Gram data have the same possibilities for
extending by an independent column.
-/

namespace Lax793645.QuadraticFrameCounts

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function
variable {D V : Type} [AddCommGroup D] [Module F D] [AddCommGroup V] [Module F V]
  [Fintype D] [Fintype V]

axiom quadratic_column_mass [FiniteDimensional F V] [FiniteDimensional F D]
    (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate)
    (P : D →ₗ[F] V) (hP : Injective P) (b : Module.Dual F D) (a : F) :
    pr unif (fun v => (q.polarBilin v).comp P = b ∧ q v = a) =
      (bp (-(dim D : ℝ)) + wsign a * ((avg unif (fun v => wsign (q v))) *
        avg unif (fun t => wsign (q (P t) + b t))))/2

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open LinearMap Module Function
axiom quadratic_column_partner
    {D V : Type} [AddCommGroup D] [Module F D] [AddCommGroup V] [Module F V]
  [Fintype D] [Fintype V] [FiniteDimensional F V] [FiniteDimensional F D]
    (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate)
    (P Q : D →ₗ[F] V) (hP : Injective P) (hQ : Injective Q)
    (hform : ∀ d, q (P d) = q (Q d)) (x : V) (hx : x ∉ P.range) :
    ∃ y ∉ Q.range, q y = q x ∧ (q.polarBilin y).comp Q = (q.polarBilin x).comp P

end

end Lax793645.QuadraticFrameCounts
