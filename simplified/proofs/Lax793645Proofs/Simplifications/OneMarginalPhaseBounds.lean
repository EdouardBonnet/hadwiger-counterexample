import Lax793645Proofs.Simplifications.OnePhaseProbeBounds
import Lax793645Proofs.Simplifications.OneCoverGlimpses

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem bool_side_event_cap {A : Type} [Fintype A] (μ : Wgt A) (hμ : IsLaw μ)
    (w : Wgt (Bool→A)) (i : Bool) (H : ℝ)
    (hc : ∀ a,mapW w (fun x=>x i) a≤H*μ a)
    (E : (Bool→A)→Prop) (hE : ∀ x y,x i=y i→(E x↔E y)) :
    pr w E≤H*pr (prodW (fun _ : Bool=>μ)) E := by
  let P (a : A):=E (fun _=>a)
  have he : E=(fun x=>P (x i)):=funext (fun x=>propext (hE x (fun _=>x i) rfl))
  rw [he,←mapW_pr w (fun x=>x i) P,
    ←mapW_pr (prodW (fun _ : Bool=>μ)) (fun x=>x i) P,
    product_projection_law _ (fun _=>hμ) i]
  exact pr_cap hc P

variable {p : Shape} {n N : ℕ}

theorem one_heat_unary (x : OneUnit p n N) (i : Bool) (e : Comp p.g) :
    oneHeat x (unary i) e=(onePhaseCube (x i) e).2*(onePhaseCube (x i) e).1ᵀ := by
  cases i <;> simp [oneHeat,unary]

theorem one_heat_one {q t : Comp p.g→ℕ} (i : Bool)
    (A B : ImageTuple (Comp p.g) t (2*N)) (Z : ImageTuple (Comp p.g) q (2*N))
    {w : Wgt (OneUnit p n N)} {H : ℝ} (hH : 0≤H)
    (m : Mixer p n) {ζ : ℝ}
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hside : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o) :
    pr w (fun x=>oneBasisFrom x i Z ∧oneTupleGlimpse x i A ∧oneThermal x (unary i) A=B)≤
      H*oneHeatRate p n N ζ (∑ e,q e) (∑ e,t e) := by
  apply (bool_side_event_cap (oneRaw m N) (one_raw_law m hroom) w i H hside _ ?_).trans
    (mul_le_mul_of_nonneg_left (one_heat_rate i (unary i) (by simp [unary]) A B Z m hcap) hH)
  intro x y hxy
  unfold oneBasisFrom oneTupleGlimpse oneThermal
  simp_rw [one_heat_unary,hxy]

theorem one_heat_none {q : Comp p.g→ℕ} (i : Bool)
    (Z : ImageTuple (Comp p.g) q (2*N))
    {w : Wgt (OneUnit p n N)} {H : ℝ} (hH : 0≤H)
    (m : Mixer p n) {ζ : ℝ}
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hside : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o) :
    pr w (fun x=>oneBasisFrom x i Z)≤H*oneHeatRate p n N ζ (∑ e,q e) 0 := by
  let t : Comp p.g→ℕ:=fun _=>0
  let B : ImageTuple (Comp p.g) t (2*N):=0
  have hh:=one_heat_one i B B Z hH m hroom hcap hside
  have hg (x : OneUnit p n N) : oneTupleGlimpse x i B:=fun _ _ _ _=>Subsingleton.elim _ _
  have ht (x : OneUnit p n N) : oneThermal x (unary i) B=B:=Subsingleton.elim _ _
  simpa only [hg,ht,and_true,t,Finset.sum_const_zero] using hh

end
end Lax793645Proofs.Simplifications
