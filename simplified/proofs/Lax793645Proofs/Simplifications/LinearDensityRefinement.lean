import Lax793645Proofs.Simplifications.FilteredDensityEnergy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectionError

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]

theorem bounded_discrepancy_test (ν f g : Wgt A) :
    ∃ W : Wgt A,(∀ x,|W x|≤1) ∧ dip ν (fun x=>f x-g x) W=lcost ν f g := by
  let W (x:A):=if g x≤f x then (1:ℝ) else -1
  refine ⟨W,fun x=>by dsimp only [W]; split <;> norm_num,?_⟩
  unfold dip lcost
  apply avg_congr
  intro x _
  dsimp only [W]
  split
  · rename_i hx
    rw [mul_one,abs_of_nonneg (sub_nonneg.mpr hx)]
  · rename_i hx
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hx))]
    ring

theorem filtered_density_progress (ν : Wgt A) (hν : SubLaw ν)
    (μ : Wgt J) (hμ : SubLaw μ) (d : J→Wgt A) (t : Wgt J)
    (ht : ∀ i,0≤t i) (hcap : ∀ i,t i≤μ i)
    (P : A→B) (Q : B→C) (W : Wgt A) (hW : ∀ x,|W x|≤1)
    (ε : ℝ) (hε : 0<ε)
    (hbad : 2*ε<dip ν (fun x=>mixW t d x-banner ν (Q∘P) (mixW t d) x) W)
    (happrox : |dip ν (mixW t d) (fun x=>W x-banner ν P W x)|≤ε) :
    densityFamilyEnergy ν μ d (Q∘P)+ε^2≤densityFamilyEnergy ν μ d P := by
  let f:=mixW t d
  let g:=banner ν (Q∘P) f
  let S:=banner ν P W
  have he : dip ν (fun x=>f x-g x) W-dip ν (fun x=>f x-g x) S=
      dip ν f (fun x=>W x-S x) := by
    rw [dip_sub,dip_sub]
    have ho:=refinement_test_orthogonal ν hν.nz P Q f W
    change dip ν g S=dip ν g W at ho
    rw [ho]
    conv_rhs => rw [dip_sym,dip_sub]
    rw [dip_sym ν W f,dip_sym ν S f]
    ring
  have hc : ε<dip ν (fun x=>f x-g x) S := by
    have hh: dip ν f (fun x=>W x-S x)≤ε:=(le_abs_self _).trans happrox
    linarith only [he,hh,hbad]
  have hgain:=filtered_density_gain ν hν μ hμ d t ht hcap P Q (cashbook ν P W)
    (fun x=>cashbook_bound ν hν.nz P W 1 zero_le_one hW _)
  change (dip ν (fun x=>f x-g x) S)^2≤_ at hgain
  have hs:=sq_le_sq₀ hε.le (hε.trans hc).le |>.mpr hc.le
  linarith only [hs,hgain]

/-- A bounded energy and bounded linear test refinements produce one
linear partition that approximates every filtered density in the family.
The family may contain arbitrarily many orientations. -/
theorem all_filters_linear_partition (V ε : ℝ) (hε : 0<ε) :
    ∃ D : ℕ,∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J]
      (ν : Wgt (Vec I)) (μ : Wgt J) (d : J→Wgt (Vec I)),
      SubLaw ν → SubLaw μ → ∀ k : ℕ,
      (∀ r : ℕ,r≤D*k → ∀ P : Mat (Fin r) I,
        densityFamilyEnergy ν μ d P.mulVec≤V) →
      (∀ r : ℕ,r≤D*k → ∀ (P : Mat (Fin r) I) (W : Wgt (Vec I)),
        (∀ x,|W x|≤1) →
        ∃ s : ℕ,s≤r+k ∧ ∃ R : Mat (Fin s) I,∃ Q : Vec (Fin s)→Vec (Fin r),
          Q∘R.mulVec=P.mulVec ∧
          ∀ t : Wgt J,(∀ i,0≤t i) → (∀ i,t i≤μ i) →
            |dip ν (mixW t d) (fun x=>W x-banner ν R.mulVec W x)|≤ε/2) →
      ∃ r : ℕ,r≤D*k ∧ ∃ P : Mat (Fin r) I,
        ∀ t : Wgt J,(∀ i,0≤t i) → (∀ i,t i≤μ i) →
          lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε := by
  obtain ⟨D,hD⟩:=exists_nat_gt (V/(ε/2)^2)
  rw [div_lt_iff₀ (sq_pos_of_pos (half_pos hε))] at hD
  refine ⟨D,fun I J _ _ _ ν μ d hν hμ k hbound hrefine=>?_⟩
  by_contra! h
  have he (j : ℕ) (hj : j≤D) :
      ∃ r : ℕ,r≤j*k ∧ ∃ P : Mat (Fin r) I,
        (j:ℝ)*(ε/2)^2≤densityFamilyEnergy ν μ d P.mulVec := by
    induction j with
    | zero =>
      refine ⟨0,by simp,0,?_⟩
      simp only [Nat.cast_zero,zero_mul]
      exact avg_nonneg hμ.nz (fun i=>ode_nonneg hν.nz _)
    | succ j ih =>
      obtain ⟨r,hr,P,hP⟩:=ih (by omega)
      have hrD : r≤D*k:=hr.trans (Nat.mul_le_mul_right k (by omega))
      obtain ⟨t,ht,hcap,hbad⟩:=h r hrD P
      obtain ⟨W,hW,hcost⟩:=bounded_discrepancy_test ν (mixW t d) (banner ν P.mulVec (mixW t d))
      obtain ⟨s,hs,R,Q,hQ,happrox⟩:=hrefine r hrD P W hW
      have hbad' : 2*(ε/2)<dip ν (fun x=>mixW t d x-banner ν (Q∘R.mulVec) (mixW t d) x) W := by
        rw [hQ,hcost]
        linarith only [hbad]
      have hgain:=filtered_density_progress ν hν μ hμ d t ht hcap R.mulVec Q W hW
        (ε/2) (half_pos hε) hbad' (happrox t ht hcap)
      rw [hQ] at hgain
      refine ⟨s,hs.trans (by rw [Nat.succ_mul]; exact Nat.add_le_add_right hr k),R,?_⟩
      push_cast
      linarith only [hgain,hP]
  obtain ⟨r,hr,P,hP⟩:=he D le_rfl
  exact (not_lt_of_ge (hP.trans (hbound r hr P))) hD

end
end Lax793645Proofs.Simplifications
