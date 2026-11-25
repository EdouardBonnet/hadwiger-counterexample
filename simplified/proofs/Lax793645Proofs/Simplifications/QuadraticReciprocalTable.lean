import Lax793645Proofs.Simplifications.QuadraticPairCompletion
import Lax793645Proofs.Simplifications.QuadraticMomentMaps
import Lax793645Proofs.Simplifications.HyperbolicExtension

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

/-- The two reciprocal channel maps occupy disjoint blocks of one cross
table. The primal-primal and channel-channel blocks stay independently free. -/
def reciprocalQuadraticTable (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (Hyperbolic h))
    (gA : A→ₗ[F]Hyperbolic h) (gB : B→ₗ[F]Hyperbolic h) :
    (A×Hyperbolic h)→ₗ[F](B×Hyperbolic h)→ₗ[F]F :=
  M.compl₁₂ (LinearMap.fst F A _) (LinearMap.fst F B _)+
  (hyperbolicQuadratic h).polarBilin.compl₁₂
    (gA.comp (LinearMap.fst F A _)) (LinearMap.snd F B _)+
  (hyperbolicQuadratic h).polarBilin.compl₁₂
    (LinearMap.snd F A _) (gB.comp (LinearMap.fst F B _))+
  D.compl₁₂ (LinearMap.snd F A _) (LinearMap.snd F B _)

theorem reciprocal_quadratic_table_apply (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (Hyperbolic h))
    (gA : A→ₗ[F]Hyperbolic h) (gB : B→ₗ[F]Hyperbolic h)
    (a : A) (b : B) (c d : Hyperbolic h) :
    reciprocalQuadraticTable h M D gA gB (a,c) (b,d)=
      M a b+(hyperbolicQuadratic h).polarBilin (gA a) d+
        (hyperbolicQuadratic h).polarBilin c (gB b)+D c d := rfl

theorem reciprocal_quadratic_table_left (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (Hyperbolic h))
    (gA : A→ₗ[F]Hyperbolic h) (gB : B→ₗ[F]Hyperbolic h)
    (a : A) (c : Hyperbolic h) :
    reciprocalQuadraticTable h M D gA gB (a,0) (0,c)=
      (hyperbolicQuadratic h).polarBilin (gA a) c := by
  simp only [reciprocal_quadratic_table_apply,map_zero,LinearMap.zero_apply,zero_add,add_zero]

theorem reciprocal_quadratic_table_right (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (Hyperbolic h))
    (gA : A→ₗ[F]Hyperbolic h) (gB : B→ₗ[F]Hyperbolic h)
    (b : B) (c : Hyperbolic h) :
    reciprocalQuadraticTable h M D gA gB (0,c) (b,0)=
      (hyperbolicQuadratic h).polarBilin c (gB b) := by
  simp only [reciprocal_quadratic_table_apply,map_zero,LinearMap.zero_apply,zero_add,add_zero]

variable {V : Type} [Fintype V]

/-- A prescribed channel map gives precisely its hyperbolic quadratic
value on the opposite primal image. There is no extra product correction. -/
theorem quadratic_channel_cross_value (h : ℕ) (q : QuadraticForm F (Vec V))
    (P : A→ₗ[F]Vec V) (C : Hyperbolic h→ₗ[F]Vec V) (g : A→ₗ[F]Hyperbolic h)
    (hcross : ∀ a c,q.polarBilin (P a) (C c)=(hyperbolicQuadratic h).polarBilin (g a) c)
    (a : A) :
    quadraticChannelFunctional q (fun j : Fin h=>C (Pi.single j 1,0))
      (fun j : Fin h=>C (0,Pi.single j 1)) (vecMulVec (P a) (P a))=
        hyperbolicQuadratic h (g a) := by
  classical
  rw [quadratic_channel_functional_outer,hyperbolic_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [binary_polar_symm q (C _) (P a),binary_polar_symm q (C _) (P a),hcross,hcross]
  change (hyperbolicQuadratic h).polarBilin (g a) (Pi.single j 1,0)*
    (hyperbolicQuadratic h).polarBilin (g a) (0,Pi.single j 1)=(g a).1 j*(g a).2 j
  rw [hyperbolic_polar,hyperbolic_polar]
  simp [mul_comm]

/-- Both reciprocal values follow from the same cross table, independently
of its still-free primal-primal and channel-channel blocks. -/
theorem quadratic_reciprocal_channel_values (h : ℕ) (q : QuadraticForm F (Vec V))
    (P : (A×Hyperbolic h)→ₗ[F]Vec V) (U : (B×Hyperbolic h)→ₗ[F]Vec V)
    (M : A→ₗ[F]B→ₗ[F]F) (D : LinearMap.BilinForm F (Hyperbolic h))
    (gA : A→ₗ[F]Hyperbolic h) (gB : B→ₗ[F]Hyperbolic h)
    (hcross : ∀ a b,q.polarBilin (P a) (U b)=reciprocalQuadraticTable h M D gA gB a b) :
    (∀ a,quadraticChannelFunctional q
      (fun j : Fin h=>U (0,(Pi.single j 1,0))) (fun j : Fin h=>U (0,(0,Pi.single j 1)))
      (vecMulVec (P (a,0)) (P (a,0)))=hyperbolicQuadratic h (gA a)) ∧
    (∀ b,quadraticChannelFunctional q
      (fun j : Fin h=>P (0,(Pi.single j 1,0))) (fun j : Fin h=>P (0,(0,Pi.single j 1)))
      (vecMulVec (U (b,0)) (U (b,0)))=hyperbolicQuadratic h (gB b)) := by
  constructor
  · exact quadratic_channel_cross_value h q (P.comp (LinearMap.inl F A _))
      (U.comp (LinearMap.inr F B _)) gA (fun a c=>(hcross (a,0) (0,c)).trans
        (reciprocal_quadratic_table_left h M D gA gB a c))
  · apply quadratic_channel_cross_value h q (U.comp (LinearMap.inl F B _))
      (P.comp (LinearMap.inr F A _)) gB
    intro b c
    change q.polarBilin (U (b,0)) (P (0,c))=(hyperbolicQuadratic h).polarBilin (gB b) c
    rw [binary_polar_symm,hcross,reciprocal_quadratic_table_right,binary_polar_symm]

end
end Lax793645Proofs.Simplifications
