import Lax793645Proofs.Simplifications.CommonQuadraticPrediction
import Lax793645Proofs.Simplifications.QueryCellRecentring

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def recenteredInput (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (x : Vec (I⊕J)) : Vec J :=
  affineRecenter A k S (x∘Sum.inr) (x∘Sum.inl)

theorem recentered_input_affine (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (j : J) :
    (fun x=>recenteredInput A k S x j)∈Stocks (I⊕J) 1 := by
  let U : Vec (I⊕J)→ₗ[F]Vec I:=LinearMap.funLeft F F Sum.inl
  let V : Vec (I⊕J)→ₗ[F]Vec J:=LinearMap.funLeft F F Sum.inr
  have hh := affine_coordinate_stocks (V+S.comp (U-A.comp V)) (-S k) j
  convert hh using 1
  funext x
  simp only [recenteredInput,affineRecenter,U,V,LinearMap.add_apply,
    LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.funLeft_apply,
    map_sub,map_add,Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
  change x (Sum.inr j)+(S (x∘Sum.inl) j-(S (A (x∘Sum.inr)) j+S k j))=
    x (Sum.inr j)+(S (x∘Sum.inl) j-S (A (x∘Sum.inr)) j)+ -S k j
  ring

theorem recentered_prediction_error (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (hS : ∀ c,A (S c)=c)
    (q : Vec J→F) (hqS : ∀ x c,q (x+S c)=q x)
    (R : Vec J→F) (φ : F→Vec I→F) :
    pr (pairW unif unif) (fun x : Vec I×Vec J=>
      φ (q x.2) x.1≠R (recenteredInput A k S (joinCoordinates x)))=
      pr unif (fun x=>φ (q x) (A x+k)≠R x) := by
  let P (x : Vec J×Vec I) := affineRecenter A k S x.1 x.2
  have hcell (x : Vec J×Vec I) : A (P x)+k=x.2 := by
    simp only [P,affineRecenter,map_add,hS]
    abel
  have hq (x : Vec J×Vec I) : q (P x)=q x.1 := hqS _ _
  calc
    _=pr (pairW unif unif) (fun x : Vec J×Vec I=>φ (q x.1) x.2≠R (P x)) := by
      simp only [pr,pairW_avg]
      exact avg_avg _ _ _
    _=pr (pairW unif unif) (fun x=>φ (q (P x)) (A (P x)+k)≠R (P x)) := by
      simp only [hq,hcell]
    _=_ := by
      rw [←mapW_pr (pairW unif unif) P (fun x=>φ (q x) (A x+k)≠R x),
        affine_recenter_uniform]

/-- Uniform free coordinates turn a fixed-error common prediction into
an exact quadratic identity on the original input space. -/
theorem affine_cell_prediction_fit (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (hS : ∀ c,A (S c)=c)
    (q R : Vec J→F) (hq : q∈Stocks J 2) (hR : R∈Stocks J 2)
    (hqS : ∀ x c,q (x+S c)=q x) (φ : F→Vec I→F) (a b : Vec J)
    (hqbit : ∀ c : F,(1/4:ℝ)≤pr unif (fun y=>q y=c))
    (hqdiff : ∀ y,q (y+a+b)-q (y+a)-q (y+b)+q y=1)
    (ε : ℝ) (hε : 5*ε<1/16)
    (he : pr unif (fun x=>φ (q x) (A x+k)≠R x)≤ε) :
    ∃ (Q : Vec I→F) (γ : F),Q∈Stocks I 2 ∧
      (∀ x,R x=Q (A x+k)+γ*q x) ∧
      (∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε) ∧
      ∃ y,Q=(fun c=>R (affineRecenter A k S y c)) := by
  let R' := fun x=>R (recenteredInput A k S x)
  have hR' : R'∈Stocks (I⊕J) 2 := polynomial_affine_substitution 2 R hR
    (recenteredInput A k S) (recentered_input_affine A k S)
  have he' : pr (pairW unif unif) (fun x : Vec I×Vec J=>
      φ (q x.2) x.1≠R' (joinCoordinates x))≤ε := by
    rw [recentered_prediction_error A k S hS q hqS]
    exact he
  obtain ⟨Q,γ,hQ,hval,hfit,y,hy⟩:=quadratic_predictor_fit R' hR' q hq φ a b
    hqbit hqdiff ε hε he'
  refine ⟨Q,γ,hQ,?_,hfit,y,hy⟩
  intro x
  have hh:=hval (A x+k) x
  simpa only [R',recenteredInput,joinCoordinates,Equiv.coe_fn_mk,Sum.elim_inl,
    Sum.elim_inr,Function.comp_def,affineRecenter,sub_self,map_zero,add_zero] using hh

/-- The same fitted polynomial works on every other affine input map
with the stated uniform free-coordinate law. -/
theorem affine_cell_prediction_transfer (A : Vec J→ₗ[F]Vec I) (k : Vec I)
    (S : Vec I→ₗ[F]Vec J) (hS : ∀ c,A (S c)=c)
    (q R : Vec J→F) (hq : q∈Stocks J 2) (hR : R∈Stocks J 2)
    (hqS : ∀ x c,q (x+S c)=q x) (φ : F→Vec I→F)
    (Q : Vec I→F) (hQ : Q∈Stocks I 2) (γ : F)
    (ε : ℝ) (hε : 5*ε<1/4)
    (hfit : ∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε)
    (he : pr unif (fun x=>φ (q x) (A x+k)≠R x)≤ε) :
    ∀ x,R x=Q (A x+k)+γ*q x := by
  let R' := fun x=>R (recenteredInput A k S x)
  have hR' : R'∈Stocks (I⊕J) 2 := polynomial_affine_substitution 2 R hR
    (recenteredInput A k S) (recentered_input_affine A k S)
  have he' : pr (pairW unif unif) (fun x : Vec I×Vec J=>
      φ (q x.2) x.1≠R' (joinCoordinates x))≤ε := by
    rw [recentered_prediction_error A k S hS q hqS]
    exact he
  have hh:=common_quadratic_prediction R' hR' q hq φ Q hQ γ ε hε hfit he'
  intro x
  simpa only [R',recenteredInput,joinCoordinates,Equiv.coe_fn_mk,Sum.elim_inl,
    Sum.elim_inr,Function.comp_def,affineRecenter,sub_self,map_zero,add_zero]
    using hh (A x+k) x

end
end Lax793645Proofs.Simplifications
