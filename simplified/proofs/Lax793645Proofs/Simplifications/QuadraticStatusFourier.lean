import Lax793645Proofs.Simplifications.WeightedFourCorners
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixFactorization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- An affine pullback costs no Fourier norm, even when its linear part
has a kernel. -/
theorem fourier_norm_affine_pullback (M : Mat J I) (c : Vec J) (w : Wgt (Vec J)) :
    fourierNorm (fun x=>w (M*ᵥx+c))≤fourierNorm w := by
  have he (x : Vec I) : w (M*ᵥx+c)=
      ∑ ξ:Vec J,(linearFourier w ξ*vectorPhase ξ c)*vectorPhase (Mᵀ*ᵥξ) x := by
    rw [←hat_eqn w (M*ᵥx+c)]
    apply Finset.sum_congr rfl
    intro ξ _
    change linearFourier w ξ*vectorPhase ξ (M*ᵥx+c)=_
    have hchar : vectorPhase ξ (M*ᵥx+c)=vectorPhase (Mᵀ*ᵥξ) x*vectorPhase ξ c := by
      unfold vectorPhase
      rw [dotProduct_add,wsign_add,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]
    rw [hchar]
    ring
  simp_rw [he]
  refine (fourier_norm_sum _).trans_eq ?_
  simp_rw [fourier_norm_smul,fourier_norm_character,mul_one,abs_mul,
    vectorPhase,wsign_abs,mul_one]
  rfl

theorem fourier_norm_affine_map (T : Vec I→ₗ[F] Vec J) (c : Vec J) (w : Wgt (Vec J)) :
    fourierNorm (fun x=>w (T x+c))≤fourierNorm w := by
  have he x : (LinearMap.toMatrix' T)*ᵥx=T x := LinearMap.congr_fun (toMat_map T) x
  simpa only [he] using fourier_norm_affine_pullback (LinearMap.toMatrix' T) c w

/-- A rank-r quadratic status depends on at most 2r linear coordinates.
Its Fourier norm is at most 2^r; no nonsingularity assumption is needed. -/
theorem quadratic_status_fourier (M : Mat I I) (φ : Wgt F) (hφ : ∀ z,|φ z|≤1) :
    fourierNorm (fun x=>φ (evmat M x x))≤bp (M.rank:ℝ) := by
  obtain ⟨C,L,_,_,hM⟩:=rank_product M
  let T : Vec I→ₗ[F] Vec (Bool×Fin M.rank) := {
    toFun x j:=if j.1 then (L*ᵥx) j.2 else (Cᵀ*ᵥx) j.2
    map_add' x y:=by ext ⟨b,j⟩; cases b <;> simp [Matrix.mulVec_add]
    map_smul' a x:=by ext ⟨b,j⟩; cases b <;> simp [Matrix.mulVec_smul] }
  let w : Wgt (Vec (Bool×Fin M.rank)):=fun x=>
    φ (dotProduct (fun j=>x (false,j)) (fun j=>x (true,j)))
  have he x : w (T x)=φ (evmat M x x) := by
    dsimp [w,T,evmat]
    rw [Matrix.mulVec_transpose,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,hM]
  have hh:=fourier_norm_affine_map T 0 w
  simp only [add_zero,he] at hh
  refine hh.trans ((fourier_norm_bounded w (fun x=>hφ _)).trans_eq ?_)
  congr 1
  simp only [num,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem affine_quadratic_status_fourier (M : Mat J J) (T : Vec I→ₗ[F] Vec J)
    (c : Vec J) (φ : Wgt F) (hφ : ∀ z,|φ z|≤1) :
      fourierNorm (fun x=>φ (evmat M (T x+c) (T x+c)))≤bp (M.rank:ℝ) := by
  exact (fourier_norm_affine_map T c (fun y=>φ (evmat M y y))).trans
    (quadratic_status_fourier M φ hφ)

end
end Lax793645Proofs.Simplifications
