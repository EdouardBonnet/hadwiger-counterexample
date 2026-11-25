import Lax793645Proofs.Simplifications.QuadraticReciprocalTable

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

abbrev UnitChannels (h : ℕ) := Bool→Hyperbolic h

/-- The reciprocal table for two units, each with two endpoint channel
blocks. A channel map acts on both opposite primal endpoints together. -/
def unitQuadraticTable (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h) :
    (A×UnitChannels h)→ₗ[F](B×UnitChannels h)→ₗ[F]F :=
  M.compl₁₂ (LinearMap.fst F A _) (LinearMap.fst F B _)+
  (∑ j,(hyperbolicQuadratic h).polarBilin.compl₁₂
    ((gA j).comp (LinearMap.fst F A _)) ((LinearMap.proj j).comp (LinearMap.snd F B _)))+
  (∑ i,(hyperbolicQuadratic h).polarBilin.compl₁₂
    ((LinearMap.proj i).comp (LinearMap.snd F A _)) ((gB i).comp (LinearMap.fst F B _)))+
  D.compl₁₂ (LinearMap.snd F A _) (LinearMap.snd F B _)

theorem unit_quadratic_table_apply (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h)
    (a : A) (b : B) (c d : UnitChannels h) :
    unitQuadraticTable h M D gA gB (a,c) (b,d)=M a b+
      (∑ j,(hyperbolicQuadratic h).polarBilin (gA j a) (d j))+
      (∑ i,(hyperbolicQuadratic h).polarBilin (c i) (gB i b))+D c d := by
  simp only [unitQuadraticTable,LinearMap.add_apply,LinearMap.sum_apply,
    LinearMap.compl₁₂_apply,LinearMap.comp_apply,LinearMap.fst_apply,
    LinearMap.snd_apply,LinearMap.proj_apply]

theorem unit_quadratic_table_left (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h)
    (j : Bool) (a : A) (c : Hyperbolic h) :
    unitQuadraticTable h M D gA gB (a,0) (0,Pi.single j c)=
      (hyperbolicQuadratic h).polarBilin (gA j a) c := by
  cases j <;> simp [unit_quadratic_table_apply]

theorem unit_quadratic_table_right (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h)
    (i : Bool) (b : B) (c : Hyperbolic h) :
    unitQuadraticTable h M D gA gB (0,Pi.single i c) (b,0)=
      (hyperbolicQuadratic h).polarBilin c (gB i b) := by
  cases i <;> simp [unit_quadratic_table_apply]

theorem unit_quadratic_table_reciprocal (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA : Bool→A→ₗ[F]Hyperbolic h) (gB : Bool→B→ₗ[F]Hyperbolic h)
    (a : A×UnitChannels h) (b : B×UnitChannels h) :
    unitQuadraticTable h M D gA gB a b=unitQuadraticTable h M.flip D.flip gB gA b a := by
  rcases a with ⟨a,c⟩
  rcases b with ⟨b,d⟩
  rw [unit_quadratic_table_apply,unit_quadratic_table_apply]
  simp only [LinearMap.flip_apply]
  have h₁ : (∑ j,(hyperbolicQuadratic h).polarBilin (gA j a) (d j))=
      ∑ j,(hyperbolicQuadratic h).polarBilin (d j) (gA j a):=
    Finset.sum_congr rfl (fun j _=>binary_polar_symm _ _ _)
  have h₂ : (∑ i,(hyperbolicQuadratic h).polarBilin (c i) (gB i b))=
      ∑ i,(hyperbolicQuadratic h).polarBilin (gB i b) (c i):=
    Finset.sum_congr rfl (fun i _=>binary_polar_symm _ _ _)
  rw [h₁,h₂]
  abel

/-- Reciprocal realization preserves all frozen rows and columns. The
projection constraints on the opposite channel maps are essential here. -/
theorem unit_quadratic_frozen_rows (h : ℕ) (M : A→ₗ[F]B→ₗ[F]F)
    (D : LinearMap.BilinForm F (UnitChannels h))
    (gA GA : Bool→A→ₗ[F]Hyperbolic h) (gB GB : Bool→B→ₗ[F]Hyperbolic h)
    (PA : Space A) (PB : Space B) (CA CB : Bool→Space (Hyperbolic h))
    (hAf : ∀ j,∀ a∈PA,gA j a=GA j a) (hBf : ∀ i,∀ b∈PB,gB i b=GB i b)
    (hAp : ∀ j a,∀ c∈CB j,(hyperbolicQuadratic h).polarBilin (gA j a) c=
      (hyperbolicQuadratic h).polarBilin (GA j a) c)
    (hBp : ∀ i b,∀ c∈CA i,(hyperbolicQuadratic h).polarBilin (gB i b) c=
      (hyperbolicQuadratic h).polarBilin (GB i b) c) :
    (∀ (a : A) (c : UnitChannels h),a∈PA→(∀ i,c i∈CA i)→∀ v,
      unitQuadraticTable h M D gA gB (a,c) v=unitQuadraticTable h M D GA GB (a,c) v) ∧
    (∀ (b : B) (d : UnitChannels h),b∈PB→(∀ j,d j∈CB j)→∀ u,
      unitQuadraticTable h M D gA gB u (b,d)=unitQuadraticTable h M D GA GB u (b,d)) := by
  constructor
  · rintro a c ha hc ⟨b,d⟩
    simp only [unit_quadratic_table_apply,hAf _ a ha]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    rw [binary_polar_symm, hBp i b (c i) (hc i),binary_polar_symm]
  · rintro b d hb hd ⟨a,c⟩
    simp only [unit_quadratic_table_apply,hBf _ b hb]
    congr 3
    exact Finset.sum_congr rfl (fun j _=>hAp j a (d j) (hd j))

end
end Lax793645Proofs.Simplifications
