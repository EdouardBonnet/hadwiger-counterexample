import Lax342547.RawFrameComparison
import Lax342547Proofs.RawBatchComparison
import Lax342547Proofs.FrameTuples
import Lax342547Proofs.InjectionAsymptotics

namespace Lax342547Proofs.RawFrameComparison
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.RawFrameComparison
open Lax342547.GramOrbitDensity Lax342547.RawBatchComparison Lax342547.RawFrames
open Lax342547.PushforwardWalsh
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false


/--
---
conclusion: Lax342547.RawFrameComparison.errorBound_half_decay
---
-/
theorem errorBound_half_decay (n : ℕ) (I J K L : Type)
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] :
    errorBound n I J K L ≤ scale I J K L/Real.sqrt ((2 : ℝ)^n) := by
  have hp : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have hs : (0 : ℝ) < Real.sqrt ((2 : ℝ)^n) := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt ((2 : ℝ)^n) ≤ (2 : ℝ)^n :=
    Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ (by norm_num)))
  have hd := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
      ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
      ((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))) hs hsq
  unfold errorBound scale
  calc
    _ ≤ (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
          (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
            ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
            ((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/Real.sqrt ((2 : ℝ)^n))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      simpa only [mul_div_assoc] using hd
    _ = _ := by ring

/--
---
conclusion: Lax342547.RawFrameComparison.eventually_valid
---
-/
theorem eventually_valid (I J K L : Type) [Fintype I] [Fintype J] [Fintype K] [Fintype L] :
    ∃ n₀ : ℕ,∀ n ≥ n₀,Fintype.card I+Fintype.card J+1 ≤ n ∧
      Fintype.card K+Fintype.card L+1 ≤ n ∧
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
        1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1) := by
  let D : ℝ := ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*((2 : ℝ)^(Fintype.card K*Fintype.card L+2))
  have ht := (InjectionAsymptotics.polynomial_dyadic_floor_tends_zero 0 2 (by omega)).const_mul D
  have ht' : Filter.Tendsto (fun n : ℕ => D/(2 : ℝ)^(n/2)) Filter.atTop (nhds 0) := by simpa only [pow_zero,one_div,mul_zero,div_eq_mul_inv,one_mul] using ht
  have he : ∀ᶠ n : ℕ in Filter.atTop,D/(2 : ℝ)^(n/2) <
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1) :=
    (tendsto_order.1 ht').2 _ (by positivity)
  obtain ⟨n₀,hn₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max n₀ (Fintype.card I+Fintype.card J+Fintype.card K+Fintype.card L+1),?_⟩
  intro n hn
  refine ⟨by omega,by omega,?_⟩
  have hsq : (2 : ℝ)^(n/2) ≤ Real.sqrt ((2 : ℝ)^n) := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact (div_le_div_of_nonneg_left (by dsimp [D]; positivity : 0 ≤ D) (by positivity) hsq).trans
    (hn₀ n (by omega)).le

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

theorem observation_comparison [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] {Ω : Type} [Fintype Ω] (n : ℕ) (p : PMF Ω)
    (G : Matrix I J Binary) (H : Matrix K L Binary) (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (x : Ω → (Fin n × (I ⊕ J) → Binary)) (y : Ω → (Fin n × (K ⊕ L) → Binary))
    (hx : p.map x = (PMF.uniformOfFintype (Orbit (Fin n) G)).map (fun z => batchEquiv z.val))
    (hy : p.map y = (PMF.uniformOfFintype (Orbit (Fin n) H)).map (fun z => batchEquiv z.val))
    (hxy : p.map (fun ω => (x ω,y ω)) =
      (PMF.uniformOfFintype (Orbit (Fin n) (Matrix.fromBlocks G A B H))).map
        (fun z => Lax342547.JointGramInjection.ambientEquiv.symm z.val))
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ ω,weights p ω*(f (x ω)*g (y ω)))-
      (∑ ω,weights p ω*f (x ω))*(∑ ω,weights p ω*g (y ω))| ≤ errorBound n I J K L := by
  have hx' := congrArg (fun q => ∑ z,weights q z*f z) hx
  have hy' := congrArg (fun q => ∑ z,weights q z*g z) hy
  have hxy' := congrArg (fun q => ∑ z,weights q z*(f z.1*g z.2)) hxy
  simp_rw [ChannelColumns.pmf_weights_map] at hx' hy' hxy'
  rw [PushforwardWalsh.push_integral,PushforwardWalsh.push_integral] at hxy'
  rw [PushforwardWalsh.push_integral,PushforwardWalsh.push_integral] at hx' hy'
  have hmG : (∑ z : Orbit (Fin n) G,weights (PMF.uniformOfFintype _) z*f (batchEquiv z.val)) =
      ∑ z,batchLaw G z*f z := by
    unfold batchLaw
    simp_rw [ChannelColumns.pmf_weights_map]
    rw [PushforwardWalsh.push_integral]
  have hmH : (∑ z : Orbit (Fin n) H,weights (PMF.uniformOfFintype _) z*g (batchEquiv z.val)) =
      ∑ z,batchLaw H z*g z := by
    unfold batchLaw
    simp_rw [ChannelColumns.pmf_weights_map]
    rw [PushforwardWalsh.push_integral]
  rw [hmG] at hx'
  rw [hmH] at hy'
  rw [hxy',hx',hy']
  exact RawBatchComparison.union_test_comparison n G H A B f g hN₁ hN₂ hf hg hsmall

theorem orbit_uniform_congr {U V N : Type} [Fintype U] [Fintype V] [Fintype N]
    {P Q : Matrix U V Binary} (h : P = Q)
    [Nonempty (Orbit N P)] [Nonempty (Orbit N Q)] :
    (PMF.uniformOfFintype (Orbit N P)).map Subtype.val =
      (PMF.uniformOfFintype (Orbit N Q)).map Subtype.val := by
  subst Q
  rfl

variable {B H : Type} [Fintype B] [Fintype H]

/--
---
conclusion: Lax342547.RawFrameComparison.primal_test_comparison
---
-/
theorem primal_test_comparison [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] (n : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B H (Fin n) E)]
    (C₁ : Matrix B I Binary) (D₁ : Matrix B J Binary)
    (C₂ : Matrix B K Binary) (D₂ : Matrix B L Binary)
    (hC : Function.Injective (Matrix.fromCols C₁ C₂).mulVec)
    (hD : Function.Injective (Matrix.fromCols D₁ D₂).mulVec)
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*
        (f (batchEquiv (F.P*C₁,F.Q*D₁))*g (batchEquiv (F.P*C₂,F.Q*D₂))))-
      (∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*f (batchEquiv (F.P*C₁,F.Q*D₁)))*
      (∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*g (batchEquiv (F.P*C₂,F.Q*D₂)))| ≤
        errorBound n I J K L := by
  classical
  let G := C₁.transpose*E*D₁
  let H₀ := C₂.transpose*E*D₂
  let A := C₁.transpose*E*D₂
  let B₀ := C₂.transpose*E*D₁
  have hC₁ : Function.Injective C₁.mulVec := by
    have he : (Matrix.fromCols C₁ C₂).submatrix id Sum.inl = C₁ := rfl
    rw [← he]
    exact JoinedGramOrbits.left_injective (Matrix.fromCols C₁ C₂) hC
  have hC₂ : Function.Injective C₂.mulVec := by
    have he : (Matrix.fromCols C₁ C₂).submatrix id Sum.inr = C₂ := rfl
    rw [← he]
    exact JoinedGramOrbits.right_injective (Matrix.fromCols C₁ C₂) hC
  have hD₁ : Function.Injective D₁.mulVec := by
    have he : (Matrix.fromCols D₁ D₂).submatrix id Sum.inl = D₁ := rfl
    rw [← he]
    exact JoinedGramOrbits.left_injective (Matrix.fromCols D₁ D₂) hD
  have hD₂ : Function.Injective D₂.mulVec := by
    have he : (Matrix.fromCols D₁ D₂).submatrix id Sum.inr = D₂ := rfl
    rw [← he]
    exact JoinedGramOrbits.right_injective (Matrix.fromCols D₁ D₂) hD
  let : Nonempty (Orbit (Fin n) G) := ⟨primalTuple (H := H) (E := E) C₁ D₁ hC₁ hD₁ (Classical.choice inferInstance)⟩
  let : Nonempty (Orbit (Fin n) H₀) := ⟨primalTuple (H := H) (E := E) C₂ D₂ hC₂ hD₂ (Classical.choice inferInstance)⟩
  have hgram : (Matrix.fromCols C₁ C₂).transpose*E*(Matrix.fromCols D₁ D₂) = Matrix.fromBlocks G A B₀ H₀ := by
    simp only [Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.mul_fromCols]
    ext (i | k) (j | l) <;> rfl
  let hOrbit : Nonempty (Orbit (Fin n) ((Matrix.fromCols C₁ C₂).transpose*E*(Matrix.fromCols D₁ D₂))) :=
    ⟨primalTuple (H := H) (E := E) _ _ hC hD (Classical.choice inferInstance)⟩
  let : Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B₀ H₀)) := hgram ▸ hOrbit
  have hx := congrArg (fun p => p.map (fun z => batchEquiv z.val)) (FrameTuples.primal_uniform (H := H) (N := Fin n) (E := E) C₁ D₁ hC₁ hD₁)
  have hy := congrArg (fun p => p.map (fun z => batchEquiv z.val)) (FrameTuples.primal_uniform (H := H) (N := Fin n) (E := E) C₂ D₂ hC₂ hD₂)
  rw [PMF.map_comp] at hx hy
  have hu := congrArg (fun p => p.map Subtype.val) (FrameTuples.primal_uniform (H := H) (N := Fin n) (E := E) _ _ hC hD)
  rw [PMF.map_comp] at hu
  simp only [Function.comp_def,primalTuple] at hu
  have hu' := hu.trans (orbit_uniform_congr (N := Fin n) hgram)
  have hxy := congrArg (fun p => p.map Lax342547.JointGramInjection.ambientEquiv.symm) hu'
  rw [PMF.map_comp,PMF.map_comp] at hxy
  have hj : (fun F : Frame B H (Fin n) E =>
      Lax342547.JointGramInjection.ambientEquiv.symm
        (F.P*Matrix.fromCols C₁ C₂,F.Q*Matrix.fromCols D₁ D₂)) =
      (fun F => (batchEquiv (F.P*C₁,F.Q*D₁),batchEquiv (F.P*C₂,F.Q*D₂))) := by
    funext F
    rw [Matrix.mul_fromCols,Matrix.mul_fromCols]
    rfl
  simp only [Function.comp_def,primalTuple] at hx hy hu hxy
  rw [hj] at hxy
  exact observation_comparison n (PMF.uniformOfFintype (Frame B H (Fin n) E)) G H₀ A B₀
    (fun F => batchEquiv (F.P*C₁,F.Q*D₁)) (fun F => batchEquiv (F.P*C₂,F.Q*D₂)) hx hy hxy
    f g hN₁ hN₂ hf hg hsmall
/--
---
conclusion: Lax342547.RawFrameComparison.full_test_comparison
---
-/
theorem full_test_comparison [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] (n : ℕ) (E : Matrix B B Binary) (S : Matrix H H Binary)
    [Nonempty (ChannelFiber (N := Fin n) E S)]
    (C₁ : Matrix (B ⊕ H) I Binary) (D₁ : Matrix (B ⊕ H) J Binary)
    (C₂ : Matrix (B ⊕ H) K Binary) (D₂ : Matrix (B ⊕ H) L Binary)
    (hC : Function.Injective (Matrix.fromCols C₁ C₂).mulVec)
    (hD : Function.Injective (Matrix.fromCols D₁ D₂).mulVec)
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*
        (f (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁))*g (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂))))-
      (∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*f (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁)))*
      (∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*g (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂)))| ≤
        errorBound n I J K L := by
  classical
  let G := C₁.transpose*(fullGram E S)*D₁
  let H₀ := C₂.transpose*(fullGram E S)*D₂
  let A := C₁.transpose*(fullGram E S)*D₂
  let B₀ := C₂.transpose*(fullGram E S)*D₁
  have hC₁ : Function.Injective C₁.mulVec := by
    have he : (Matrix.fromCols C₁ C₂).submatrix id Sum.inl = C₁ := rfl
    rw [← he]
    exact JoinedGramOrbits.left_injective (Matrix.fromCols C₁ C₂) hC
  have hC₂ : Function.Injective C₂.mulVec := by
    have he : (Matrix.fromCols C₁ C₂).submatrix id Sum.inr = C₂ := rfl
    rw [← he]
    exact JoinedGramOrbits.right_injective (Matrix.fromCols C₁ C₂) hC
  have hD₁ : Function.Injective D₁.mulVec := by
    have he : (Matrix.fromCols D₁ D₂).submatrix id Sum.inl = D₁ := rfl
    rw [← he]
    exact JoinedGramOrbits.left_injective (Matrix.fromCols D₁ D₂) hD
  have hD₂ : Function.Injective D₂.mulVec := by
    have he : (Matrix.fromCols D₁ D₂).submatrix id Sum.inr = D₂ := rfl
    rw [← he]
    exact JoinedGramOrbits.right_injective (Matrix.fromCols D₁ D₂) hD
  let : Nonempty (Orbit (Fin n) G) := ⟨fullTuple (N := Fin n) (E := E) (G := S) C₁ D₁ hC₁ hD₁ (Classical.choice inferInstance)⟩
  let : Nonempty (Orbit (Fin n) H₀) := ⟨fullTuple (N := Fin n) (E := E) (G := S) C₂ D₂ hC₂ hD₂ (Classical.choice inferInstance)⟩
  have hgram : (Matrix.fromCols C₁ C₂).transpose*(fullGram E S)*(Matrix.fromCols D₁ D₂) = Matrix.fromBlocks G A B₀ H₀ := by
    simp only [Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.mul_fromCols]
    ext (i | k) (j | l) <;> rfl
  let hOrbit : Nonempty (Orbit (Fin n) ((Matrix.fromCols C₁ C₂).transpose*(fullGram E S)*(Matrix.fromCols D₁ D₂))) :=
    ⟨fullTuple (N := Fin n) (E := E) (G := S) _ _ hC hD (Classical.choice inferInstance)⟩
  let : Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B₀ H₀)) := hgram ▸ hOrbit
  have hx := congrArg (fun p => p.map (fun z => batchEquiv z.val)) (FrameTuples.full_uniform (N := Fin n) (E := E) (G := S) C₁ D₁ hC₁ hD₁)
  have hy := congrArg (fun p => p.map (fun z => batchEquiv z.val)) (FrameTuples.full_uniform (N := Fin n) (E := E) (G := S) C₂ D₂ hC₂ hD₂)
  rw [PMF.map_comp] at hx hy
  have hu := congrArg (fun p => p.map Subtype.val) (FrameTuples.full_uniform (N := Fin n) (E := E) (G := S) _ _ hC hD)
  rw [PMF.map_comp] at hu
  simp only [Function.comp_def,fullTuple] at hu
  have hu' := hu.trans (orbit_uniform_congr (N := Fin n) hgram)
  have hxy := congrArg (fun p => p.map Lax342547.JointGramInjection.ambientEquiv.symm) hu'
  rw [PMF.map_comp,PMF.map_comp] at hxy
  have hj : (fun F : ChannelFiber (N := Fin n) E S =>
      Lax342547.JointGramInjection.ambientEquiv.symm
        ((Lax342547.FrameSymmetry.plus F.val).val*Matrix.fromCols C₁ C₂,(Lax342547.FrameSymmetry.minus F.val).val*Matrix.fromCols D₁ D₂)) =
      (fun F => (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁),batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂))) := by
    funext F
    rw [Matrix.mul_fromCols,Matrix.mul_fromCols]
    rfl
  simp only [Function.comp_def,fullTuple] at hx hy hu hxy
  rw [hj] at hxy
  exact observation_comparison n (PMF.uniformOfFintype (ChannelFiber (N := Fin n) E S)) G H₀ A B₀
    (fun F => batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁)) (fun F => batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂)) hx hy hxy
    f g hN₁ hN₂ hf hg hsmall

end
end Lax342547Proofs.RawFrameComparison
