import Lax793645Proofs.Simplifications.ReducedMixerSpace

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

def reducedUrBad (K s0 : ℕ) (x : Profile p n) (l : Tag p.g) (s : Label p.b) (d : ReducedDraw p n) :=
  totalRank x ≤ K ∧ totalRank x>0 ∧ blockRank Block.Z s s
    (qmix (reducedMixer d) x l+(qmix (reducedMixer d) x l)ᵀ)<2*(p.J-s0)

def reducedProdBound (p : Shape) (K : ℕ) := 2*p.J*reducedRankBudget p K

theorem reducedUrBad_cap (K s0 : ℕ) (hg : 3≤p.g) (hodd : Odd p.g) (hj : s0≤p.J)
    (x : Profile p n) (l : Tag p.g) (s : Label p.b) :
    pr unif (reducedUrBad K s0 x l s) ≤
      bp (((reducedProdBound p K : ℝ)+2*(reducedRankBudget p K)-n)*(s0+1)) := by
  classical
  by_cases h : totalRank x≤K ∧ totalRank x>0
  swap
  · rw [show reducedUrBad K s0 x l s = fun _ => False by
      funext d; exact propext ⟨fun g => h ⟨g.1,g.2.1⟩,False.elim⟩,pr_false]
    exact (bp_pos _).le
  let R := blockRay p n s Block.Z
  let r (i : Comp p.g×Bool) := (reducedProfile x l i.1 i.2).rank
  obtain ⟨P,Q,h1,h2,h3⟩ :
      ∃ (P Q : ReducedParts p n r), (∀ i,Function.Injective (P i).mulVec) ∧
        (∀ i,Function.Injective (Q i).mulVec) ∧ (∀ i,reducedProfile x l i.1 i.2=P i*(Q i)ᵀ) := by
    choose A B h1 h2 h3 using fun i : Comp p.g×Bool => rank_product (reducedProfile x l i.1 i.2)
    refine ⟨A,fun i => (B i)ᵀ,h1,fun i => ?_,fun i => (h3 i).symm⟩
    rw [← transpose_surj_iff]; exact h2 i
  obtain ⟨S,hS,hrS⟩ := reduced_factors_space P Q
  obtain ⟨T,hT,hv⟩ := choose_free (blockRay_inj p n s Block.Z) S
  let W := R*pack T
  let V := (ReducedTerms p r)
  let A := reducedStack P Q W
  have hb : Function.Surjective A := by
    apply reduced_stack_surj _ _ _
      (inj_comp_mat _ _ (blockRay_inj p n s Block.Z) (pack_inj T)) h1 h2
    · exact fun i => hv.mono_left (hS i).1
    exact fun i => hv.mono_left (hS i).2
  have hc : Fintype.card (V⊕V)=2*p.J*reducedMass x l := by
    simp only [Fintype.card_sum,ReducedTerms,Fintype.card_prod,Fintype.card_fin,
      Fintype.card_sigma,V,Fintype.sum_prod_type,reducedMass,r]
    ring
  have hcard : 2*p.J≤Fintype.card (V⊕V) := by
    rw [hc]
    have hp:=Nat.mul_le_mul_left (2*p.J) (reduced_mass_positive hg x l h.2)
    simpa only [Nat.mul_one] using hp
  let Y (M : Mat (Fin (dim T)) (V ⊕ V)) :=
    M.rank+(s0+1) ≤ Fintype.card (V⊕V)
  have he (d) (hh : reducedUrBad K s0 x l s d) : Y (A d) := by
    let B := qmix (reducedMixer d) x l + (qmix (reducedMixer d) x l)ᵀ
    have hineq := rank_ge_congr (swapM V) (A d)
    have hx : pullM W W B=liftM (A d) (A d) (swapM V) := by
      dsimp only [B]
      rw [reduced_qmix_factors hodd P Q l d x (fun e b=>h3 (e,b))]
      exact alt_of_forms _ _ W
    rw [← hx, swapM_rank] at hineq
    have hp : (pullM W W B).rank ≤ (pullM R R B).rank := by
      calc _ = (pullM (pack T) (pack T) (pullM R R B)).rank := by
                 unfold W pullM
                 rw [liftM_comp, Matrix.transpose_mul]
           _ ≤ _ := rank_lift_le _ _ _
    have hh1 : (pullM R R B).rank < 2*(p.J-s0) := hh.2.2
    change _+_ ≤ _
    omega
  have hpr := pr_mono (w:=unif) unif_subLaw.nz he
  change pr unif (reducedUrBad K s0 x l s) ≤ pr unif (fun d => Y (A d)) at hpr
  rw [← mapW_pr unif A Y,map_unif_surjective _ hb] at hpr
  apply le_trans (hpr.trans (pr_deficient _))
  apply bp_le
  have hmass : reducedMass x l≤reducedRankBudget p K:=
    (reduced_mass_bound x l).trans (Nat.mul_le_mul_left _ h.1)
  have hp : num (V⊕V)≤reducedProdBound p K := by
    have he : Fintype.card (V⊕V)≤reducedProdBound p K := by
      rw [hc]
      exact Nat.mul_le_mul_left _ hmass
    exact_mod_cast he
  have hsum : (∑ i,r i)=reducedMass x l:=by rw [Fintype.sum_prod_type]; rfl
  have hx : n≤num (Fin (dim T))+2*(reducedRankBudget p K:ℝ) := by
    rw [Fintype.card_fin] at hT
    have he : n≤Fintype.card (Fin (dim T))+2*reducedRankBudget p K := by
      rw [Fintype.card_fin]
      rw [hsum] at hrS
      exact hT.trans (Nat.add_le_add_left (hrS.trans (Nat.mul_le_mul_left _ hmass)) _)
    exact_mod_cast he
  push_cast
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith only [hp,hx]

end
end Lax793645Proofs.Simplifications
