import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PolynomialZeroTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Below the minimum weight of a nonzero Boolean polynomial, agreement
in probability is an identity. The dimension does not enter the bound. -/
theorem polynomial_agreement_exact (d : ℕ) (f g : Vec I→F)
    (hf : f∈Stocks I d) (hg : g∈Stocks I d)
    (he : pr unif (fun x=>f x≠g x)<bp (-(d:ℝ))) : f=g := by
  apply funext
  intro x
  by_contra hx
  have hne : ∃ y,(f-g) y≠0 := ⟨x,by simpa only [Pi.sub_apply,sub_ne_zero] using hx⟩
  have hh := stocks_bound I d (f-g) (Submodule.sub_mem _ hf hg) hne
  simp only [Pi.sub_apply,sub_ne_zero] at hh
  exact (not_lt_of_ge hh) he

/-- The degree-four switch used to fit a predictor becomes exact at
one fixed accuracy. -/
theorem quadratic_switch_exact (f q g₀ g₁ : Vec I→F)
    (hf : f∈Stocks I 2) (hq : q∈Stocks I 2)
    (h₀ : g₀∈Stocks I 2) (h₁ : g₁∈Stocks I 2)
    (he : pr unif (fun x=>f x≠g₀ x+q x*(g₀ x+g₁ x))<1/16) :
    ∀ x,f x=g₀ x+q x*(g₀ x+g₁ x) := by
  have hprod : q*(g₀+g₁)∈Stocks I 4 :=
    stock_prod (d:=2) (j:=2) hq (Submodule.add_mem _ h₀ h₁)
  have ht : g₀+q*(g₀+g₁)∈Stocks I 4 :=
    Submodule.add_mem _ (stocks_rise I (d:=2) (j:=4) (by norm_num) h₀) hprod
  have hnum : bp (-(4:ℝ))=1/16 := by norm_num [bp]
  have hbound : pr unif (fun x=>f x≠(g₀+q*(g₀+g₁)) x)<bp (-(4:ℝ)) := by
    rw [hnum]
    exact he
  have hh := polynomial_agreement_exact 4 f (g₀+q*(g₀+g₁))
    (stocks_rise I (d:=2) (j:=4) (by norm_num) hf) ht hbound
  exact congrFun hh

/-- A nonzero second difference in tester variables forces the switch
slope to be a constant. The fitted functions are invariant under these
two tester shifts, because they depend only on the common coordinates. -/
theorem quadratic_switch_constant_slope (f q g₀ g₁ : Vec I→F)
    (hf : f∈Stocks I 2) (a b : Vec I)
    (h₀a : ∀ x,g₀ (x+a)=g₀ x) (h₀b : ∀ x,g₀ (x+b)=g₀ x)
    (h₁a : ∀ x,g₁ (x+a)=g₁ x) (h₁b : ∀ x,g₁ (x+b)=g₁ x)
    (hq : ∀ x,q (x+a+b)-q (x+a)-q (x+b)+q x=1)
    (he : ∀ x,f x=g₀ x+q x*(g₀ x+g₁ x)) :
    ∃ γ : F,(∀ x,g₀ x+g₁ x=γ) ∧ ∀ x,f x=g₀ x+γ*q x := by
  let d := spoil a (spoil b f)
  have hd : d∈Stocks I 0 := stock_decay (d:=0) a (stock_decay (d:=1) b hf)
  have hval (x : Vec I) : d x=g₀ x+g₁ x := by
    change (f (x+a+b)-f (x+a))-(f (x+b)-f x)=_
    simp only [he,h₀a,h₀b,h₁a,h₁b]
    calc
      _ = (q (x+a+b)-q (x+a)-q (x+b)+q x)*(g₀ x+g₁ x) := by ring
      _ = _ := by rw [hq,one_mul]
  refine ⟨d 0,?_,?_⟩
  · intro x
    exact (hval x).symm.trans (stock_initial x 0 hd)
  · intro x
    rw [he,←hval x,stock_initial x 0 hd,mul_comm]

/-- The proposed numerical accuracy is strictly inside the degree-four
separation gap. -/
theorem fixed_predictor_accuracy : (5:ℝ)*(1/1000)<1/16 := by norm_num

theorem quadratic_second_difference (q : Vec I→F) (hq : q∈Stocks I 2)
    (a b : Vec I) (h : q (a+b)-q a-q b+q 0=1) :
    ∀ x,q (x+a+b)-q (x+a)-q (x+b)+q x=1 := by
  have hd : spoil a (spoil b q)∈Stocks I 0 :=
    stock_decay (d:=0) a (stock_decay (d:=1) b hq)
  intro x
  have hh:=stock_initial x 0 hd
  change (q (x+a+b)-q (x+a))-(q (x+b)-q x)=
    (q (0+a+b)-q (0+a))-(q (0+b)-q 0) at hh
  simp only [zero_add] at hh
  calc
    _=(q (x+a+b)-q (x+a))-(q (x+b)-q x) := by ring
    _=(q (a+b)-q a)-(q b-q 0) := hh
    _=1 := by linear_combination h

theorem polynomial_vanish_outside (d : ℕ) (f : Vec I→F) (hf : f∈Stocks I d)
    (E : Finset (Vec I))
    (hE : (E.card:ℝ)<bp ((Fintype.card I:ℝ)-d))
    (he : ∀ x,x∉E→f x=0) : ∀ x,f x=0 := by
  classical
  intro x
  by_contra hx
  have h:=stocks_bound I d f hf ⟨x,hx⟩
  have hsub : pr unif (fun x=>f x≠0)≤pr unif (fun x=>x∈E) :=
    pr_mono unif_law.nz (fun x hx=>by by_contra hh; exact hx (he x hh))
  have hcount:=h.trans hsub
  rw [pr_unif,nbr_eq_card,card_space (Vec I),dim_vec] at hcount
  rw [Fintype.card_coe,le_div_iff₀ (bp_pos _),←bp_add] at hcount
  have heq : -(d:ℝ)+(Fintype.card I:ℝ)=Fintype.card I-d := by ring
  rw [heq] at hcount
  exact hE.not_ge hcount

end
end Lax793645Proofs.Simplifications
