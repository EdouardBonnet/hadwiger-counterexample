import Lax342547.DerivativeContractions
import Lax342547Proofs.ChannelChanges
import Lax342547Proofs.TensorContractions

namespace Lax342547Proofs.DerivativeContractions

open Lax342547.MomentSpace Lax342547.PrimalContractions Lax342547.ConcreteGeometry
open Lax342547.TensorContractions

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.DerivativeContractions.right_rank_one
---
The baseline paired with the rank-one channel value is a product
of coordinate functionals. The product-test identity gives exactly
the baseline evaluation of the contracted residual vector.
-/
theorem right_rank_one {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (f : (B → Binary) →ₗ[Binary] (H → Binary))
    (ψ : Module.Dual Binary (B → Binary)) (c : H → Binary) :
    ambient f (ψ.smulRight c) M = dotProduct (f (M.mulVecLin (coordinates ψ))) c := by
  classical
  let φ := ((dotProductBilin Binary Binary).flip c).comp f
  have hb : (dotProductBilin Binary Binary).compl₁₂ f (ψ.smulRight c) = φ.smulRight ψ := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change dotProduct (f v) (ψ w • c) = φ v * ψ w
    simp [φ, dotProduct, smul_eq_mul, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc]
  have hc := Lax342547Proofs.PrimalContractions.product_pair M φ ψ
  rw [ambient, hb]
  exact hc

/--
---
conclusion: Lax342547.DerivativeContractions.transpose_contraction
---
Swap the finite matrix indices and use symmetry of the channel
dot product. No symmetry of the input matrix is assumed.
-/
theorem transpose_contraction {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    ambient f g M = ambient g f M.transpose := by
  classical
  simp only [ambient, matrixPair, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, matrixEntry, LinearMap.BilinForm.toMatrix'_apply,
    LinearMap.compl₁₂_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact dotProduct_comm _ _

/--
---
conclusion: Lax342547.DerivativeContractions.left_rank_one
---
Transpose the contraction and apply the right rank-one identity,
retaining the reciprocal baseline and the transposed residual.
-/
theorem left_rank_one {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (g : (B → Binary) →ₗ[Binary] (H → Binary))
    (φ : Module.Dual Binary (B → Binary)) (c : H → Binary) :
    ambient (φ.smulRight c) g M = dotProduct c (g (M.transpose.mulVecLin (coordinates φ))) := by
  rw [transpose_contraction, right_rank_one, dotProduct_comm]

theorem ambient_zero_left {B H : Type} [Fintype B] [Fintype H]
    (g : (B → Binary) →ₗ[Binary] (H → Binary)) : ambient 0 g = 0 := by
  classical
  have hb : (dotProductBilin Binary Binary).compl₁₂
      (0 : (B → Binary) →ₗ[Binary] (H → Binary)) g = 0 := by ext v w; simp
  simp [ambient, hb, matrixPair]

theorem ambient_zero_right {B H : Type} [Fintype B] [Fintype H]
    (f : (B → Binary) →ₗ[Binary] (H → Binary)) : ambient f 0 = 0 := by
  classical
  have hb : (dotProductBilin Binary Binary).compl₁₂ f
      (0 : (B → Binary) →ₗ[Binary] (H → Binary)) = 0 := by ext v w; simp
  simp [ambient, hb, matrixPair]

open Lax342547.PairedAnnihilators

theorem bilinear_transpose_pair {B : Type} [Fintype B]
    (β : LinearMap.BilinForm Binary (B → Binary)) (M : Matrix B B Binary) : by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' β) M.transpose =
        matrixPair (LinearMap.BilinForm.toMatrix' β.flip) M := by
  classical
  simp only [matrixPair, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, matrixEntry, LinearMap.BilinForm.toMatrix'_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rfl

/--
---
conclusion: Lax342547.DerivativeContractions.paired_transpose
---
Transpose every endpoint tensor and flip the arbitrary quotient bilinear
form. The same pure test then applies with the nominal quotients swapped.
-/
theorem paired_transpose {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) : PairedAnnihilates (fun i => (M i).transpose) E D := by
  classical
  intro β
  have hh := h β.flip
  simp only [pureResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at hh ⊢
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [bilinear_transpose_pair]
  congr 2

end Lax342547Proofs.DerivativeContractions
