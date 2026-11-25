import Lax793645Proofs.Simplifications.QuadraticPredictorFitting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A fit selected from one unit transfers to every other unit with the
same common predictor. No union bound over the population is needed. -/
theorem common_quadratic_prediction (R : Vec (I⊕J)→F)
    (hR : R∈Stocks (I⊕J) 2) (q : Vec J→F) (hq : q∈Stocks J 2)
    (φ : F→Vec I→F) (Q : Vec I→F) (hQ : Q∈Stocks I 2) (γ : F)
    (ε : ℝ) (hε : 5*ε<1/4)
    (hfit : ∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε)
    (he : pr (pairW unif unif)
      (fun x : Vec I×Vec J=>φ (q x.2) x.1≠R (joinCoordinates x))≤ε) :
    ∀ c y,R (joinCoordinates (c,y))=Q c+γ*q y := by
  let G (x : Vec (I⊕J)) := Q (x∘Sum.inl)+γ*q (x∘Sum.inr)
  have hG : G∈Stocks (I⊕J) 2 := by
    apply Submodule.add_mem
    · exact polynomial_affine_substitution 2 Q hQ (fun x=>x∘Sum.inl)
        (fun i=>stock_var (Sum.inl i))
    · exact Submodule.smul_mem _ γ (polynomial_affine_substitution 2 q hq
        (fun x=>x∘Sum.inr) (fun j=>stock_var (Sum.inr j)))
  have ht : pr (pairW unif unif)
      (fun x : Vec I×Vec J=>φ (q x.2) x.1≠Q x.1+γ*q x.2)≤4*ε :=
    predictor_fit_transfer unif unif unif_law unif_law φ q (fun d c=>Q c+γ*d)
      (4*ε) hfit
  have herr : pr unif (fun x=>R x≠G x)<bp (-(2:ℝ)) := by
    rw [joined_uniform_event]
    have hh : pr (pairW unif unif)
        (fun x=>R (joinCoordinates x)≠G (joinCoordinates x))≤ε+4*ε := by
      refine (pr_mono (pairW_law unif_law unif_law).nz (fun x hx=>?_) |>.trans
        (pr_or_le (pairW_law unif_law unif_law).nz)).trans (add_le_add he ht)
      by_contra! h
      exact hx (h.1.symm.trans h.2)
    have hb : bp (-(2:ℝ))=1/4 := by norm_num [bp]
    rw [hb]
    exact hh.trans_lt (by linarith only [hε])
  have hh := polynomial_agreement_exact 2 R G hR hG herr
  intro c y
  exact congrFun hh (joinCoordinates (c,y))

end
end Lax793645Proofs.Simplifications
