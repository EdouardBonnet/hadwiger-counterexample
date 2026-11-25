import Lax793645Proofs.Simplifications.LinearCellBounds
import Lax793645Proofs.Simplifications.LinearCellCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {I Q : Type} [Fintype I] [DecidableEq I]

/-- The reference law gives every attained value the mass of at least
half a full fiber, even if different fibers have the same value. -/
theorem attained_coordinate_mass {A : Type} (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (R : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hsmall : γ ≤ bp (-(R:ℝ))/2)
    (hbias : ∀ ξ : Vec I, ξ ≠ 0 → |avg ν (vectorPhase ξ)| ≤ γ)
    (f : Q → Vec I → A) (hf : HasLinearCells f R) (q : Q) (x : Vec I) :
    bp (-(R:ℝ))/2 ≤ mapW ν (f q) (f q x) := by
  classical
  obtain ⟨r,hr,L,φ,hφ⟩:=hf
  let P : Mat (Fin r) I:=LinearMap.toMatrix' L
  have hP (x : Vec I) : P*ᵥx=L x := by
    exact LinearMap.toMatrix'_mulVec L x
  have hsub : mapW ν P.mulVec (P*ᵥx) ≤ mapW ν (f q) (f q x) := by
    apply pr_mono hν.nz
    intro y hy
    change P*ᵥy=P*ᵥx at hy
    rw [hP,hP] at hy
    rw [hφ,hφ,hy]
  have hmass : mapW (unif : Wgt (Vec I)) P.mulVec (P*ᵥx)=bp (-(P.rank:ℝ)) := by
    have hh:=pr_unif_lin P.mulVecLin (P*ᵥx)
    rw [ind_one (show P*ᵥx∈LinearMap.range P.mulVecLin from ⟨x,rfl⟩),one_mul] at hh
    exact hh
  have hlow : bp (-(R:ℝ))≤mapW (unif : Wgt (Vec I)) P.mulVec (P*ᵥx) := by
    rw [hmass]
    apply bp_le
    have hh : P.rank≤R:=(Matrix.rank_le_card_height P).trans (by simpa using hr)
    exact neg_le_neg (by exact_mod_cast hh)
  have herr:=linear_cell_mass_error ν hν γ hγ hbias P (P*ᵥx)
  have hdiff : mapW unif P.mulVec (P*ᵥx)-mapW ν P.mulVec (P*ᵥx)≤γ :=
    (le_abs_self _).trans (by rwa [abs_sub_comm])
  linarith only [hlow,hdiff,hsmall,hsub]

/-- A function of a bounded list of linear coordinates has a fixed
separation gap under every sufficiently unbiased reference law. -/
theorem bounded_coordinate_separation (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (R : ℕ) (γ τ : ℝ) (hγ : 0≤γ) (hsmall : γ≤bp (-(R:ℝ))/2)
    (hτ : τ<bp (-(R:ℝ))/2)
    (hbias : ∀ ξ : Vec I,ξ≠0→|avg ν (vectorPhase ξ)|≤γ)
    (f : Q→Vec I→F) (hf : HasLinearCells f R) (q : Q) (b : F)
    (he : pr ν (fun x=>f q x≠b)≤τ) : ∀ x,f q x=b := by
  classical
  intro x
  by_contra hx
  have hsub : mapW ν (f q) (f q x) ≤ pr ν (fun y=>f q y≠b) :=
    pr_mono hν.nz (fun y hy => (show f q y=f q x from hy).symm ▸ hx)
  exact (not_lt_of_ge ((attained_coordinate_mass ν hν R γ hγ hsmall hbias f hf q x).trans
    (hsub.trans he))) hτ

end
end Lax793645Proofs.Simplifications
