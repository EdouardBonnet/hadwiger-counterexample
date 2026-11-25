import Lax793645Proofs.Simplifications.OneBinaryForms
import Lax793645Proofs.Simplifications.OneClosedPinLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProductCoordinateReplacement
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MixerConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneUnitPair : OneUnit p n N≃OneOrient p n N×OneOrient p n N where
  toFun x:=(x true,x false)
  invFun x i:=if i then x.1 else x.2
  left_inv x:=by funext i; cases i <;> rfl
  right_inv x:=rfl

theorem one_unit_pair_law (m : Mixer p n) :
    mapW (oneUnitRaw m N) oneUnitPair=pairW (oneRaw m N) (oneRaw m N) := by
  funext x
  rw [mapW_equiv_val]
  simp only [oneUnitRaw,prodW,Fintype.prod_bool,oneUnitPair,pairW]
  rfl

theorem one_issue_live (p : Shape) :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ,2*(n:ℝ)+2≤N→
      Fintype.card (Row p n)+2*p.h+3≤N→
      ∀ (m : Mixer p n) (s t : Label p.b) (c : Vec (Comp p.g)),c≠0→
      pr (pairW (oneRaw m N) (oneRaw m N))
        (fun x=>5*blockRank Block.Z s t (oneIssue c x.1 x.2)<n)≤bp (-(n:ℝ)*n/20) := by
  classical
  filter_upwards [one_duel_live p] with n hn N hN hroom m s t c hc
  obtain ⟨j,hj⟩:=Function.ne_iff.mp hc
  have hj' : c j=1:=(bit_cases _).resolve_left hj
  let μ : Wgt (OneFrame p n N):=quadraticChannelRaw (C:=Vec (Fin p.h))
    (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm'
  let f:=fun _ : Comp p.g=>μ
  let R:=blockRay p n s Block.Z
  let S:=blockRay p n t Block.Z
  let F (x : OneOrient p n N×OneOrient p n N):=
    5*(pullM R S (oneIssue c x.1 x.2)).rank<n
  have hμ : IsLaw μ:=quadratic_channel_raw_law _ (hyperbolic_matrix_nondegenerate N) _
    (one_frame_room (by omega))
  have hu : IsLaw (oneRaw m N):=one_raw_law m (by omega)
  have hi (x : OneOrient p n N×OneOrient p n N) :
      pr (pairW μ μ) (fun y=>F (update x.1 j y.1,update x.2 j y.2))≤bp (-(n:ℝ)*n/20) := by
    let W:=pullM R S (∑ i∈univ.erase j,c i •oneDuel (x.1 i) (x.2 i))
    have he (y : OneFrame p n N×OneFrame p n N) :
        F (update x.1 j y.1,update x.2 j y.2) ↔
          5*(pullM R S (oneDuel y.1 y.2)+W).rank<n := by
      unfold F oneIssue
      rw [←add_sum_erase _ _ (mem_univ j),map_add]
      simp only [update_self,hj',one_smul]
      have hs : (∑ i∈univ.erase j,c i •oneDuel (update x.1 j y.1 i) (update x.2 j y.2 i))=
          ∑ i∈univ.erase j,c i •oneDuel (x.1 i) (x.2 i) := by
        apply sum_congr rfl
        intro i hi
        simp only [update_of_ne ((mem_erase.mp hi).1)]
      rw [hs]
    simp_rw [he]
    exact hn N hN hroom m R S (blockRay_inj ..) (blockRay_inj ..) W
  change avg (pairW (prodW f) (prodW f)) (fun x=>ind (F x))≤_
  rw [update2_avg f f j _ hμ hμ]
  exact (pairW_law hu hu).avg_le hi

def oneLitFire (x : OneUnit p n N) : Prop:=
  ∀ (s t : Label p.b) (c : Vec (Comp p.g)),c≠0→
    n≤5*blockRank Block.Z s t (oneIssue c (x true) (x false))

/-- The quadratic binary test is uniform outside a squared-exponential
exception, even after the full exponential leaf-density inflation. -/
theorem one_lit_fire_calendar (p : Shape) (C : ℝ) (M : ℕ) (hM : 4≤M) :
    ∀ᶠ n : ℕ in atTop,let N:=M*n;∀ m : Mixer p n,
      Fintype.card (Row p n)+2*p.h+3≤N→∀ w : Wgt (OneUnit p n N),
      (∀ x,w x≤bp (C*(2*N))*oneUnitRaw m N x)→
      pr w (fun x=>¬oneLitFire x)≤bp (-(n:ℝ)*n/40) := by
  classical
  let I:=Label p.b×Label p.b×Vec (Comp p.g)
  have ht:=bp_poly_dom_nat (a:=1) zero_lt_one (num I) 0
  filter_upwards [one_issue_live p,ht,eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (eventually_ge_atTop (40*(2*C*M+1)))] with n hn hp hn1 hab N m hroom w hw
  have hN : 2*(n:ℝ)+2≤N := by
    have hm : (4:ℝ)≤M:=by exact_mod_cast hM
    have h1 : (1:ℝ)≤n:=by exact_mod_cast hn1
    dsimp only [N]
    push_cast
    nlinarith
  let Q (i : I) (x : OneUnit p n N):=i.2.2≠0 ∧
    5*blockRank Block.Z i.1 i.2.1 (oneIssue i.2.2 (x true) (x false))<n
  have hμ : IsLaw (oneUnitRaw m N):=one_unit_raw_law m (by omega)
  have he (i : I) : pr (oneUnitRaw m N) (Q i)≤bp (-(n:ℝ)*n/20) := by
    by_cases hz : i.2.2=0
    · simp only [Q,hz,ne_eq,not_true,false_and,pr_false]; exact (bp_pos _).le
    have hh:=hn N hN hroom m i.1 i.2.1 i.2.2 hz
    rw [←one_unit_pair_law m,mapW_pr] at hh
    exact (pr_mono hμ.nz (fun _ h=>h.2)).trans hh
  have hh (x : OneUnit p n N) (h : ¬oneLitFire x) : ∃ i,Q i x := by
    unfold oneLitFire at h
    push Not at h
    obtain ⟨s,t,c,hc,h⟩:=h
    exact ⟨(s,t,c),hc,h⟩
  have hi : pr (oneUnitRaw m N) (fun x=>¬oneLitFire x)≤num I*bp (-(n:ℝ)*n/20) :=
    ((pr_mono hμ.nz hh).trans (pr_exists_le hμ.nz Q)).trans
      ((sum_le_sum (fun i _=>he i)).trans_eq (by simp [num]))
  refine (pr_cap hw _).trans ((mul_le_mul_of_nonneg_left hi (bp_pos _).le).trans ?_)
  simp only [pow_zero,mul_one,one_mul] at hp
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp.le
    (bp_pos (-(n:ℝ)*n/20)).le) (bp_pos (C*(2*N))).le).trans
  rw [←bp_add,←bp_add]
  apply bp_le
  dsimp only [N]
  push_cast
  change 40*(2*C*M+1)≤(n:ℝ) at hab
  nlinarith only [mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n : 0≤(n:ℝ))]

end
end Lax793645Proofs.Simplifications
