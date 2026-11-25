import Lax793645Proofs.Simplifications.OneExactTesterRank
import Lax793645Proofs.Simplifications.TesterPolynomialInputs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N g : ℕ}

theorem bit_support_complement (v : Fin g→F) :
    (bitSupport v).card+(bitSupport (fun t=>v t+1)).card=g := by
  classical
  have hh:=Finset.card_filter_add_card_filter_not (s:=univ) (p:=fun t : Fin g=>v t≠0)
  have he : (fun t=>¬v t≠0)=(fun t=>v t+1≠0) := by
    funext t
    rcases bit_cases (v t) with h|h <;> rw [h] <;> decide
  simpa only [he,bitSupport,card_univ,Fintype.card_fin] using hh

theorem small_support_slopes (v γ : Fin g→F) (r k : ℕ)
    (hroom : 4*k<g*r)
    (hs : ∀ l,(bitSupport (fun t=>v t+γ l)).card*r≤2*k) :
    ∀ l j,γ l=γ j := by
  intro l j
  by_contra hne
  have hcard : (bitSupport (fun t=>v t+γ l)).card+
      (bitSupport (fun t=>v t+γ j)).card=g := by
    rcases bit_cases (γ l) with hl|hl <;> rcases bit_cases (γ j) with hj|hj
    · exact (hne (hl.trans hj.symm)).elim
    · simpa only [hl,hj,add_zero] using bit_support_complement v
    · simpa only [hl,hj,add_zero,add_comm] using bit_support_complement v
    · exact (hne (hl.trans hj.symm)).elim
  have hh:=Nat.add_le_add (hs l) (hs j)
  rw [←Nat.add_mul,hcard] at hh
  omega

/-- The shared point is common to every tag. Once the slopes agree,
oddness of the cycle forces their common value to be zero. -/
theorem one_shared_slope_zero (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (s : Label p.b)
    (hfree : Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype))
    (w : Pdual p n) (φ : Tag p.g→Module.Dual F H→F) (γ : F)
    (hg : Odd p.g) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (he : ∀ l f y,w (useAtom p l s f y)=
      φ l (oneQueryCell H o l s f y)+γ*dialed p l f y) : γ=0 := by
  classical
  have hpos : 0<p.g:=by obtain ⟨k,hk⟩:=hg; omega
  let l0 : Tag p.g:=⟨0,hpos⟩
  let f:=Flavor.sharedOnly (g:=p.g)
  let A0:=(oneJointCell H).comp (oneFreeKey (oneFreeColumns p n s) o)
  obtain ⟨S,hS⟩:=A0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (one_joint_cell_free_surjective _ o H hfree))
  have hS' (c : Module.Dual F H) : A0 (S c)=c:=LinearMap.congr_fun hS c
  have hsum (b : F) : (∑ l,φ l 0)+γ*b=0 := by
    obtain ⟨y,hy,_⟩:=exists_of_pr_pos (spins_law p n).nz
      ((by norm_num : (0:ℝ)<1/4).trans_le (dialed_bit_mass l0 f hr hn b))
    let z:=oneRecenterQuery H o l0 s f S y 0
    have hz : dialed p l0 f z=b:=by
      rw [show dialed p l0 f z=dialed p l0 f y from dialed_add_free l0 f y _]
      exact hy
    have hc (l : Tag p.g) : oneQueryCell H o l s f z=0 := by
      change oneJointCell H (onePrimalKey o (point p s (lit f l z)))=0
      rw [←common_lit p l0 l z]
      exact one_recenter_query_cell H o l0 s f S hS' y 0
    have hv (l : Tag p.g) : w (atom p l s (lit f l0 z))=φ l 0+γ*b := by
      have hh:=he l f z
      rw [hc l,←common_dial p l0 l z,hz] at hh
      change w (atom p l s (lit f l z))=_ at hh
      rwa [←common_lit p l0 l z] at hh
    have ht : (∑ l,w (atom p l s (lit f l0 z)))=0 := by
      rw [←map_sum,atom_union,map_zero]
    simp_rw [hv] at ht
    rw [Finset.sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,
      odd_smul_bit hg] at ht
    exact ht
  have h0:=hsum 0
  have h1:=hsum 1
  have hz : (∑ l,φ l 0)=0 := by simpa only [mul_zero,add_zero] using h0
  simpa only [hz,mul_one,zero_add] using h1

theorem one_exact_slopes_zero (H : Space (OneJointKey p N))
    (x : OneUnit p n N) (i : Bool) (u : Profile p n) (α : F)
    (m : Mixer p n) (K : ℕ) (hk : totalRank u≤K)
    (s : Label p.b)
    (hfree : Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp H.subtype))
    (φ : Tag p.g→Module.Dual F H→F) (γ : Tag p.g→F)
    (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (hroom : 4*oneScreenRank p K<p.g*p.r)
    (he : ∀ l f y,oneYoke m x i u α (useAtom p l s f y)=
      φ l (oneQueryCell H (x i) l s f y)+γ l*dialed p l f y) :
    (∀ l,γ l=0) ∧ (bitSupport (testerCoefficients u α)).card*p.r≤2*oneScreenRank p K := by
  have hs (l : Tag p.g) := one_exact_tester_support H x i u α (γ l) m K hk hg
    (by omega) s l hfree (φ l) hj hn (he l Flavor.full)
  have hconst:=small_support_slopes (testerCoefficients u α) γ p.r (oneScreenRank p K) hroom hs
  let l0 : Tag p.g:=⟨0,by omega⟩
  have he' (l f y) : oneYoke m x i u α (useAtom p l s f y)=
      φ l (oneQueryCell H (x i) l s f y)+γ l0*dialed p l f y := by
    rw [he,hconst l l0]
  have hz:=one_shared_slope_zero H (x i) s hfree (oneYoke m x i u α) φ (γ l0) hg hr hn he'
  refine ⟨fun l=>(hconst l l0).trans hz,?_⟩
  simpa only [hz,add_zero] using hs l0

end
end Lax793645Proofs.Simplifications
