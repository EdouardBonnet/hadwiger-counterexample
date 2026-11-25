import Lax793645Proofs.Simplifications.PredictorSliceFitting
import Lax793645Proofs.Simplifications.PolynomialSubstitution

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def joinCoordinates : (Vec I×Vec J)≃Vec (I⊕J) where
  toFun x := Sum.elim x.1 x.2
  invFun x := (x∘Sum.inl,x∘Sum.inr)
  left_inv x := rfl
  right_inv x := by funext i; cases i <;> rfl

theorem joined_uniform_event (P : Vec (I⊕J)→Prop) :
    pr unif P=pr (pairW unif unif) (fun x=>P (joinCoordinates x)) := by
  rw [←pair_unif,←mapW_pr unif joinCoordinates P,unif_equiv]

theorem quadratic_section (R : Vec (I⊕J)→F) (hR : R∈Stocks (I⊕J) 2) (y : Vec J) :
    (fun c=>R (joinCoordinates (c,y)))∈Stocks I 2 := by
  apply polynomial_affine_substitution 2 R hR
  intro j
  cases j with
  | inl i => exact stock_var i
  | inr j => exact stocks_one I 1 (y j)

/-- A quadratic target that is well predicted by a common cell and one
quadratic tester has an exact common quadratic predictor, possibly plus
a constant multiple of the tester. This is the dimension-free fitting
step; the construction's tester identities subsequently remove that bit. -/
theorem quadratic_predictor_fit (R : Vec (I⊕J)→F)
    (hR : R∈Stocks (I⊕J) 2) (q : Vec J→F) (hq : q∈Stocks J 2)
    (φ : F→Vec I→F) (a b : Vec J)
    (hqbit : ∀ c : F,(1/4:ℝ)≤pr unif (fun y=>q y=c))
    (hqdiff : ∀ y,q (y+a+b)-q (y+a)-q (y+b)+q y=1)
    (ε : ℝ) (hε : 5*ε<1/16)
    (he : pr (pairW unif unif)
      (fun x : Vec I×Vec J=>φ (q x.2) x.1≠R (joinCoordinates x))≤ε) :
    ∃ (Q : Vec I→F) (γ : F),Q∈Stocks I 2 ∧
      (∀ c y,R (joinCoordinates (c,y))=Q c+γ*q y) ∧
      (∀ d : F,pr unif (fun c=>φ d c≠Q c+γ*d)≤4*ε) ∧
      ∃ y,Q=(fun c=>R (joinCoordinates (c,y))) := by
  classical
  choose y hy hfit using fun d : F=>predictor_slice_fit unif unif unif_law unif_law
    φ q (fun c y=>R (joinCoordinates (c,y))) d ε (hqbit d) he
  let Q (d : F) (c : Vec I) := R (joinCoordinates (c,y d))
  let G (d : F) (x : Vec (I⊕J)) := Q d (x∘Sum.inl)
  let q' (x : Vec (I⊕J)) := q (x∘Sum.inr)
  have hG (d : F) : G d∈Stocks (I⊕J) 2 := by
    apply polynomial_affine_substitution 2 (Q d) (quadratic_section R hR (y d))
    intro i
    exact stock_var (Sum.inl i)
  have hq' : q'∈Stocks (I⊕J) 2 := by
    apply polynomial_affine_substitution 2 q hq
    intro j
    exact stock_var (Sum.inr j)
  have hQbit (d : F) (c : Vec I) : Q d c=Q 0 c+d*(Q 0 c+Q 1 c) := by
    rcases bit_cases d with hd|hd <;> subst d
    · simp
    · simp only [one_mul]
      rw [←add_assoc,char_two,zero_add]
  have htransfer : pr (pairW unif unif)
      (fun x : Vec I×Vec J=>φ (q x.2) x.1≠Q (q x.2) x.1)≤4*ε :=
    predictor_fit_transfer unif unif unif_law unif_law φ q Q (4*ε) hfit
  have herror : pr unif (fun x=>R x≠G 0 x+q' x*(G 0 x+G 1 x))<1/16 := by
    rw [joined_uniform_event]
    have hsub : pr (pairW unif unif)
        (fun x=>R (joinCoordinates x)≠G 0 (joinCoordinates x)+
          q' (joinCoordinates x)*(G 0 (joinCoordinates x)+G 1 (joinCoordinates x)))≤ε+4*ε := by
      refine (pr_mono (pairW_law unif_law unif_law).nz (fun x hx=>?_) |>.trans
        (pr_or_le (pairW_law unif_law unif_law).nz)).trans (add_le_add he htransfer)
      by_contra! hh
      apply hx
      change R (joinCoordinates x)=Q 0 x.1+q x.2*(Q 0 x.1+Q 1 x.1)
      exact (hh.1.symm.trans hh.2).trans (hQbit _ _)
    exact hsub.trans_lt (by linarith only [hε])
  have hidentity := quadratic_switch_exact R q' (G 0) (G 1) hR hq' (hG 0) (hG 1) herror
  let A : Vec (I⊕J) := Sum.elim 0 a
  let B : Vec (I⊕J) := Sum.elim 0 b
  have hGa (d : F) (x : Vec (I⊕J)) : G d (x+A)=G d x := by
    unfold G
    congr 1
    funext i
    simp [A,Function.comp_def]
  have hGb (d : F) (x : Vec (I⊕J)) : G d (x+B)=G d x := by
    unfold G
    congr 1
    funext i
    simp [B,Function.comp_def]
  have hdiff (x : Vec (I⊕J)) : q' (x+A+B)-q' (x+A)-q' (x+B)+q' x=1 := by
    exact hqdiff (x∘Sum.inr)
  obtain ⟨γ,hγ,hfinal⟩ := quadratic_switch_constant_slope R q' (G 0) (G 1) hR A B
    (hGa 0) (hGb 0) (hGa 1) (hGb 1) hdiff hidentity
  refine ⟨Q 0,γ,quadratic_section R hR (y 0),?_,?_,y 0,rfl⟩
  · intro c z
    exact hfinal (joinCoordinates (c,z))
  · intro d
    have hd (c : Vec I) : Q d c=Q 0 c+γ*d := by
      have hh := hγ (joinCoordinates (c,0))
      change Q 0 c+Q 1 c=γ at hh
      rw [hQbit,hh,mul_comm]
    have hh : pr unif (fun c=>φ d c≠Q d c)≤4*ε := hfit d
    simpa only [hd] using hh

end
end Lax793645Proofs.Simplifications
