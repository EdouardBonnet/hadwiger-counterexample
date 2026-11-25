import Lax793645Proofs.Simplifications.QuadraticUnitTables
import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

def unitPrimalTable (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) : A→ₗ[F]B→ₗ[F]F :=
  T.compl₁₂ (LinearMap.inl F _ _) (LinearMap.inl F _ _)

def unitChannelTable (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) :
    LinearMap.BilinForm F (UnitChannels h) :=
  T.compl₁₂ (LinearMap.inr F _ _) (LinearMap.inr F _ _)

def unitLeftChannels (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) (j : Bool) :
    A→ₗ[F]Hyperbolic h :=
  (LinearMap.BilinForm.toDual (hyperbolicQuadratic h).polarBilin
    (hyperbolic_nondegenerate h)).symm.toLinearMap.comp
    (T.compl₁₂ (LinearMap.inl F _ _)
      ((LinearMap.inr F _ _).comp (LinearMap.single F (fun _ : Bool=>Hyperbolic h) j)))

def unitRightChannels (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) (i : Bool) :
    B→ₗ[F]Hyperbolic h := unitLeftChannels h T.flip i

theorem unit_left_channels_pairing (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F)
    (j : Bool) (a : A) (c : Hyperbolic h) :
    (hyperbolicQuadratic h).polarBilin (unitLeftChannels h T j a) c=
      T (a,0) (0,Pi.single j c) := by
  let L:=(T.compl₁₂ (LinearMap.inl F _ _)
    ((LinearMap.inr F _ _).comp (LinearMap.single F (fun _ : Bool=>Hyperbolic h) j))) a
  have he:=(LinearMap.BilinForm.toDual (hyperbolicQuadratic h).polarBilin
    (hyperbolic_nondegenerate h)).apply_symm_apply L
  exact LinearMap.congr_fun he c

theorem unit_right_channels_pairing (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F)
    (i : Bool) (b : B) (c : Hyperbolic h) :
    (hyperbolicQuadratic h).polarBilin c (unitRightChannels h T i b)=
      T (0,Pi.single i c) (b,0) := by
  rw [binary_polar_symm]
  exact unit_left_channels_pairing h T.flip i b c

theorem unit_table_coordinates (h : ℕ)
    (T : (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F) :
    unitQuadraticTable h (unitPrimalTable h T) (unitChannelTable h T)
      (unitLeftChannels h T) (unitRightChannels h T)=T := by
  apply LinearMap.ext
  rintro ⟨a,c⟩
  apply LinearMap.ext
  rintro ⟨b,d⟩
  have hL : (∑ j,(hyperbolicQuadratic h).polarBilin (unitLeftChannels h T j a) (d j))=
      T (a,0) (0,d) := by
    simp_rw [unit_left_channels_pairing]
    rw [←map_sum]
    congr 1
    apply Prod.ext
    · simp
    · ext i <;> cases i <;> simp
  have hR : (∑ i,(hyperbolicQuadratic h).polarBilin (c i) (unitRightChannels h T i b))=
      T (0,c) (b,0) := by
    simp_rw [unit_right_channels_pairing]
    rw [←LinearMap.sum_apply,←map_sum]
    congr 2
    apply Prod.ext
    · simp
    · ext i <;> cases i <;> simp
  rw [unit_quadratic_table_apply,hL,hR]
  change T (a,0) (b,0)+T (a,0) (0,d)+T (0,c) (b,0)+T (0,c) (0,d)=T (a,c) (b,d)
  have ha : (a,c)=(a,0)+(0,c):=by simp
  have hb : (b,d)=(b,0)+(0,d):=by simp
  conv_rhs => rw [ha,hb]
  simp only [map_add,LinearMap.add_apply]
  abel

end
end Lax793645Proofs.Simplifications
