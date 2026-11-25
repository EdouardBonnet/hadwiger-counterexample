import Lax793645Proofs.Simplifications.LinearReferenceProjection
import Lax793645Proofs.Simplifications.BoundedOverlapTransfer
import Lax793645Proofs.Simplifications.ProjectionRefinementBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J K T : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]

/-- On a law with small linear bias, the overlap of two bounded linear
tables is determined, up to an explicit error, by their common equations. -/
theorem linear_reference_common_overlap (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (γ : ℝ) (hγ : 0≤γ) (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (Q : Mat K I) (C : Mat T I)
    (hC : frequencySpace P⊓frequencySpace Q≤frequencySpace C)
    (φ : Wgt (Vec J)) (ψ : Wgt (Vec K)) (B : ℝ) (hB : 0≤B)
    (hφ : ∀ x,|φ x|≤B) (hψ : ∀ x,|ψ x|≤B) :
    let f : Wgt (Vec I):=fun x=>φ (P*ᵥx)
    let g : Wgt (Vec I):=fun x=>ψ (Q*ᵥx)
    |dip ν f g-dip ν (banner ν C.mulVec f) (banner ν C.mulVec g)|≤
      2*γ*fourierNorm f*fourierNorm g+
        2*B*γ*num (Vec T)*(fourierNorm f+fourierNorm g) := by
  intro f g
  let f₀:=banner unif C.mulVec f
  let g₀:=banner unif C.mulVec g
  let f₁:=banner ν C.mulVec f
  let g₁:=banner ν C.mulVec g
  have hf x : |f x|≤B:=hφ _
  have hg x : |g x|≤B:=hψ _
  have hf₁ x : |f₁ x|≤B:=cashbook_bound ν hν.nz C.mulVec f B hB hf _
  have hg₀ x : |g₀ x|≤B:=cashbook_bound unif unif_law.nz C.mulVec g B hB hg _
  have h1 : |dip ν f g-dip unif f g|≤γ*fourierNorm f*fourierNorm g :=
    (small_bias_test ν hν γ hγ hbias (fun x=>f x*g x)).trans
      ((mul_le_mul_of_nonneg_left (fourier_norm_mul f g) hγ).trans_eq (by ring))
  have h2 : |dip unif f g-dip ν f₀ g₀|≤γ*fourierNorm f*fourierNorm g := by
    rw [linear_uniform_common_overlap P Q C hC φ ψ,abs_sub_comm]
    refine (small_bias_test ν hν γ hγ hbias (fun x=>f₀ x*g₀ x)).trans ?_
    have hh : fourierNorm (fun x=>f₀ x*g₀ x)≤fourierNorm f*fourierNorm g:=
      (fourier_norm_mul f₀ g₀).trans (mul_le_mul (projection_fourier_norm C f)
        (projection_fourier_norm C g) (fourier_norm_nonneg _) (fourier_norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hh hγ).trans_eq (by ring)
  have h3 : |dip ν f₀ g₀-dip ν f₁ g₁|≤
      2*B*γ*num (Vec T)*(fourierNorm f+fourierNorm g) := by
    have hferr:=linear_reference_projection_error ν hν γ hγ hbias C f
    have hgerr:=linear_reference_projection_error ν hν γ hγ hbias C g
    have he : lcost ν f₀ f₁+lcost ν g₀ g₁≤
        2*γ*num (Vec T)*fourierNorm f+2*γ*num (Vec T)*fourierNorm g := by
      simpa only [lcost,abs_sub_comm] using add_le_add hferr hgerr
    exact (bounded_pair_change ν f₀ g₀ f₁ g₁ hν.nz B hf₁ hg₀).trans
      ((mul_le_mul_of_nonneg_left he hB).trans_eq (by ring))
  have hh := (abs_sub_le (dip ν f g) (dip unif f g) (dip ν f₁ g₁)).trans
    (add_le_add le_rfl (abs_sub_le (dip unif f g) (dip ν f₀ g₀) (dip ν f₁ g₁)))
  exact hh.trans ((add_le_add h1 (add_le_add h2 h3)).trans_eq (by ring))

/-- Passing from nonnegative actual densities to bounded linear tables
loses only their L1 errors. The actual densities need not be bounded. -/
theorem linear_actual_overlap (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (γ : ℝ) (hγ : 0≤γ) (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (Q : Mat K I) (C : Mat T I)
    (hC : frequencySpace P⊓frequencySpace Q≤frequencySpace C)
    (φ : Wgt (Vec J)) (ψ : Wgt (Vec K)) (B : ℝ) (hB : 0≤B)
    (hφ : ∀ x,0≤φ x ∧ φ x≤B) (hψ : ∀ x,0≤ψ x ∧ ψ x≤B)
    (d e : Wgt (Vec I)) (hd : ∀ x,0≤d x) (he : ∀ x,0≤e x) :
    let f : Wgt (Vec I):=fun x=>φ (P*ᵥx)
    let g : Wgt (Vec I):=fun x=>ψ (Q*ᵥx)
    dip ν (banner ν C.mulVec f) (banner ν C.mulVec g)≤
      dip ν d e+B*(lcost ν f d+lcost ν g e)+
        (2*γ*fourierNorm f*fourierNorm g+
          2*B*γ*num (Vec T)*(fourierNorm f+fourierNorm g)) := by
  intro f g
  have hh:=linear_reference_common_overlap ν hν γ hγ hbias P Q C hC φ ψ B hB
    (fun x=>by rw [abs_of_nonneg (hφ x).1]; exact (hφ x).2)
    (fun x=>by rw [abs_of_nonneg (hψ x).1]; exact (hψ x).2)
  have hb:=bounded_overlap_transfer ν d e f g hν.nz B (fun x=>hφ _) (fun x=>hψ _) hd he
  have hc : dip ν (banner ν C.mulVec f) (banner ν C.mulVec g)-dip ν f g≤
      2*γ*fourierNorm f*fourierNorm g+2*B*γ*num (Vec T)*(fourierNorm f+fourierNorm g) :=
    (le_abs_self _).trans (by rwa [abs_sub_comm])
  linarith only [hb,hc]

/-- The same estimate for the actual common projections. Their bounds
come from the cell hit estimate; their approximation error is unnormalized. -/
theorem linear_actual_projected_overlap (ν : Wgt (Vec I)) (hν : IsLaw ν)
    (γ : ℝ) (hγ : 0≤γ) (hbias : ∀ ξ : Vec I,ξ≠0 → |avg ν (vectorPhase ξ)|≤γ)
    (P : Mat J I) (Q : Mat K I) (C : Mat T I)
    (hC : frequencySpace P⊓frequencySpace Q≤frequencySpace C)
    (φ : Wgt (Vec J)) (ψ : Wgt (Vec K)) (B : ℝ) (hB : 0≤B)
    (hφ : ∀ x,0≤φ x ∧ φ x≤B) (hψ : ∀ x,0≤ψ x ∧ ψ x≤B)
    (d e : Wgt (Vec I)) (hd : ∀ x,0≤d x) (he : ∀ x,0≤e x)
    (hproj : ∀ x,|banner ν C.mulVec e x|≤B) :
    let f : Wgt (Vec I):=fun x=>φ (P*ᵥx)
    let g : Wgt (Vec I):=fun x=>ψ (Q*ᵥx)
    dip ν (banner ν C.mulVec d) (banner ν C.mulVec e)≤
      dip ν d e+2*B*(lcost ν f d+lcost ν g e)+
        (2*γ*fourierNorm f*fourierNorm g+
          2*B*γ*num (Vec T)*(fourierNorm f+fourierNorm g)) := by
  intro f g
  have hh:=linear_actual_overlap ν hν γ hγ hbias P Q C hC φ ψ B hB hφ hψ d e hd he
  have hf x : |banner ν C.mulVec f x|≤B:=cashbook_bound ν hν.nz C.mulVec f B hB
    (fun x=>by rw [abs_of_nonneg (hφ _).1]; exact (hφ _).2) _
  have hc:=bounded_pair_change ν (banner ν C.mulVec d) (banner ν C.mulVec e)
    (banner ν C.mulVec f) (banner ν C.mulVec g) hν.nz B hf hproj
  have hcost : lcost ν (banner ν C.mulVec d) (banner ν C.mulVec f)+
      lcost ν (banner ν C.mulVec e) (banner ν C.mulVec g)≤lcost ν f d+lcost ν g e := by
    simpa only [lcost,abs_sub_comm] using add_le_add
      (projection_lcost_contract ν hν.nz C.mulVec d f)
      (projection_lcost_contract ν hν.nz C.mulVec e g)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hcost hB)
  have he' := (le_abs_self _).trans hc'
  linarith only [hh,he']

end
end Lax793645Proofs.Simplifications
