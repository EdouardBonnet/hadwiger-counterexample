import Lax793645Proofs.Simplifications.QuadraticPredictorFitting
import Lax793645Proofs.Simplifications.ConditionalStatusSupports

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- A relation on a nonempty rectangle of possible statuses forces
constant unary parities, with no probabilistic error. -/
theorem support_rectangle_constant {A B C : Type}
    (s : C→Set A) (t : C→Set B) (a : A→F) (b : B→F) (q : C→F)
    (hs : ∀ c,(s c).Nonempty) (ht : ∀ c,(t c).Nonempty)
    (h : ∀ c x,x∈s c→∀ y,y∈t c→a x+b y=q c) :
    ∃ φ : C→F,(∀ c x,x∈s c→a x=φ c) ∧
      ∀ c y,y∈t c→b y=φ c+q c := by
  classical
  choose x hx using hs
  choose y hy using ht
  refine ⟨fun c=>a (x c),?_,?_⟩
  · intro c z hz
    exact add_right_cancel ((h c z hz (y c) (hy c)).trans (h c (x c) (hx c) (y c) (hy c)).symm)
  · intro c z hz
    have hh:=congrArg (fun v=>a (x c)+v) (h c (x c) (hx c) z hz)
    simpa only [←add_assoc,char_two,zero_add] using hh

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Exact support constancy needs only two sections and a second
difference. Neither a fitting error nor a degree-four agreement test
appears in this normal form. -/
theorem exact_quadratic_predictor (R : Vec (I⊕J)→F)
    (hR : R∈Stocks (I⊕J) 2) (q : Vec J→F) (φ : F→Vec I→F)
    (hq : Function.Surjective q) (a b : Vec J)
    (hqdiff : ∀ y,q (y+a+b)-q (y+a)-q (y+b)+q y=1)
    (he : ∀ c y,R (joinCoordinates (c,y))=φ (q y) c) :
    ∃ (Q : Vec I→F) (γ : F),Q∈Stocks I 2 ∧
      (∀ d c,φ d c=Q c+γ*d) ∧
      ∃ y,q y=0 ∧ Q=(fun c=>R (joinCoordinates (c,y))) := by
  classical
  choose y hy using hq
  let Q (d : F) (c : Vec I):=R (joinCoordinates (c,y d))
  have hQ (d : F) (c : Vec I) : Q d c=φ d c:=by
    dsimp only [Q]
    rw [he,hy]
  have hQbit (d : F) (c : Vec I) : Q d c=Q 0 c+d*(Q 0 c+Q 1 c):=by
    rcases bit_cases d with hd|hd <;> subst d
    · simp
    · simp only [one_mul]
      rw [←add_assoc,char_two,zero_add]
  let G (d : F) (x : Vec (I⊕J)):=Q d (x∘Sum.inl)
  let q' (x : Vec (I⊕J)):=q (x∘Sum.inr)
  have hid (x : Vec (I⊕J)) : R x=G 0 x+q' x*(G 0 x+G 1 x):=by
    have hh:=he (x∘Sum.inl) (x∘Sum.inr)
    have hx : joinCoordinates (x∘Sum.inl,x∘Sum.inr)=x := by
      funext i
      cases i <;> rfl
    rw [hx] at hh
    exact hh.trans ((hQ _ _).symm.trans (hQbit _ _))
  let A : Vec (I⊕J):=Sum.elim 0 a
  let B : Vec (I⊕J):=Sum.elim 0 b
  have hGa (d : F) (x : Vec (I⊕J)) : G d (x+A)=G d x:=by
    unfold G
    congr 1
    funext i
    simp [A,Function.comp_def]
  have hGb (d : F) (x : Vec (I⊕J)) : G d (x+B)=G d x:=by
    unfold G
    congr 1
    funext i
    simp [B,Function.comp_def]
  have hdiff (x : Vec (I⊕J)) : q' (x+A+B)-q' (x+A)-q' (x+B)+q' x=1:=
    hqdiff (x∘Sum.inr)
  obtain ⟨γ,_,hfinal⟩:=quadratic_switch_constant_slope R q' (G 0) (G 1) hR A B
    (hGa 0) (hGb 0) (hGa 1) (hGb 1) hdiff hid
  refine ⟨Q 0,γ,quadratic_section R hR (y 0),?_,y 0,hy 0,rfl⟩
  intro d c
  have hh:=hfinal (joinCoordinates (c,y d))
  change R (joinCoordinates (c,y d))=Q 0 c+γ*q (y d) at hh
  rw [he,hy] at hh
  exact hh

end
end Lax793645Proofs.Simplifications
