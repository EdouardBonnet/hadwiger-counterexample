import Lax793645Proofs.Simplifications.OneMarkedPhaseRecords
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FinitePhaseAlternative

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}

def oneMergeCover {p : Shape} {N : ℕ} (T : Cov p N) : SymCover p N:=
  fun e=>T (e,true)⊔T (e,false)

theorem one_merge_cover_dimension (T : Cov p (2*N)) :
    oneCoverDimension (oneMergeCover T)≤cdim p T := by
  rw [cdim_sign]
  unfold oneCoverDimension cdSign
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _=>Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem one_merge_covered (T : Cov p (2*N)) (x : Ambient p (2*N))
    (h : covered p T x) : oneSymCovered (oneMergeCover T) x := by
  apply (covered_iff (oneSymCov (oneMergeCover T)) x).mpr
  intro e a ha b hb
  apply (covered_iff T x).mp h e a ?_ b ?_
  · rw [annih_mem] at ha ⊢
    exact fun y hy=>ha y (Submodule.mem_sup_left hy)
  · rw [annih_mem] at hb ⊢
    exact fun y hy=>hb y (Submodule.mem_sup_right hy)

def oneNoSweepBudget (p : Shape) (N m b r : ℕ) (c ψ H : ℝ):=
  bp (2*(r:ℝ)*num (Comp p.g)*(2*N))*(H*oneCubePrice p^2*
    (exponentErr p m b c/ψ^(2^m*(2*b))))

/-- All numerical costs of the one-frame phase argument. The raw image
cap is the concrete quadratic-frame cap, not a two-frame assumption. -/
structure OnePhaseReady (p : Shape) (n N m b r k d : ℕ) (mix : Mixer p n)
    (c l ψ ε L H : ℝ) : Prop where
  hb : 1≤b
  hm : 16*r<m
  hk : k≤d
  hc : 0<c
  hc' : c≤1
  hl : 0<l
  hl' : l≤1
  hψ : 0<ψ
  hL : 0≤L
  hH : 0≤H
  hroom : Fintype.card (Row p n)+2*p.h+1≤N
  hN : 5≤N
  hchannels : 4*p.h+3≤N
  cap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
    pr (oneUnitRaw mix N) (imagePinAgree oneDualImages a)≤fee (2*N) ε (imagePlanRank a.sp)
  noBranch : ψ+oneNoSweepBudget p N m b r c ψ H<0.005
  frames : oneScaleBill p n N (2*maxSpan m b r) L≤c/2
  atlas (T : SymCover p (2*N)) (ht : oneCoverDimension T≤2*maxSpan m b r) :
    num (SymAtlas p r T)≤bp (0.002*(2*N))
  price : oneSelectionPrice p r n N (rhUp L c) ε
  price' : oneSelectionPrice p r n N (rhUp (rhUp L c) l) ε
  localQ : oneQuest p r k n N (rhUp H c) ε
  testFailure : oneGlimpseBill p k (rhUp L c)+bp (-0.1*(2*N))<l^(k+1)
  testFailure' : 2*oneGlimpseBill p d (rhUp L c)≤l/2
  beatSlack : 5*l+bp (-0.24*(2*N))<0.005

set_option maxHeartbeats 800000 in
/-- The full finite phase alternative for the actual one-frame
construction, including extraction of records from marked profiles. -/
theorem one_phase_alternative {w : Wgt (OneUnit p n N)}
    (marks : OneUnit p n N→Bool→Profile p n)
    {c l ψ ε L H : ℝ} {m b k d : ℕ}
    (mix : Mixer p n) (hr : OnePhaseReady p n N m b r k d mix c l ψ ε L H)
    (hw : IsLaw w)
    (hk : ∀ i o,mapW w (fun x=>x i) o≤L*oneRaw mix N o)
    (hv : ∀ x,w x≤H*oneUnitRaw mix N x)
    (hmarks : ∀ x,w x≠0→∀ i,marks x i∈Xspace p n)
    (hh : ∀ x,w x≠0→ oneMarkedDelta x (marks x)≠0 ∧totalRank (marks x true)≤r)
    (hK : ∀ x,epoch p (oneMarkedDelta x (marks x))≤r) :
    ∃ P : OneUnit p n N→Prop,(c/2)*(l/2)≤pr w P ∧
      (oneTonalMix (fun x=>oneMarkedDelta x (marks x)) (onW w P) ∨
        oneTonalTiny (fun x=>oneMarkedDelta x (marks x)) (onW w P) d) := by
  classical
  let Δ x:=oneMarkedDelta x (marks x)
  have hc:=hr.hc
  have hl:=hr.hl
  by_cases he : ∀ T : Cov p (2*N),(∀ i,cdSign p T i≤maxSpan m b r)→
      pr w (fun x=>covered p T (Δ x))≤c
  · refine ⟨fun _=>True,?_,Or.inl ?_⟩
    · rw [pr_true,hw.total]
      nlinarith [hr.hc',hr.hl']
    rw [onW_true w hw]
    apply one_tonal_left _ _
    intro S R hS
    exact (one_pitch_no_cover Δ hw S R hS r m b hK hr.hm hr.hb c ψ H hc.le he
      hr.hψ hr.hH mix hv hr.hroom hr.hchannels).trans_lt hr.noBranch
  push Not at he
  obtain ⟨T,hT,hW⟩:=he
  let C:=oneMergeCover T
  have hC : oneCoverDimension C≤2*maxSpan m b r := by
    apply (one_merge_cover_dimension T).trans
    rw [cdim_sign,two_mul (maxSpan m b r)]
    exact Nat.add_le_add (hT true) (hT false)
  let P (x : OneUnit p n N):=covered p T (Δ x) ∧oneSeparated x C
  let v:=onW w P
  have hp : c/2≤pr w P := by
    have hf:=one_cover_separation_failure hw.sub mix hr.hL hk hr.hroom hr.hN C
      (2*maxSpan m b r) hC
    have hs:=pr_shield hw.nz (fun x=>covered p T (Δ x)) (fun x=>oneSeparated x C)
    change _≤pr w P at hs
    linarith only [hr.frames,hW,hf,hs]
  have hpp : 0<pr w P:=lt_of_lt_of_le (half_pos hc) hp
  have hf : IsLaw v:=on_law hw.nz hpp
  obtain ⟨s,hs⟩:=one_marked_bazaar marks v C
    (fun x hx=>hmarks x (onW_ne hx).2)
    (fun x hx=>(onW_ne hx).1.2)
    (fun x hx=>one_merge_covered T _ (onW_ne hx).1.1)
    (fun x hx=>(hh x (onW_ne hx).2).1)
    (fun x hx=>(hh x (onW_ne hx).2).2)
  have hH:=hr.hH
  have hL:=hr.hL
  have hv' x : v x≤rhUp H c*oneUnitRaw mix N x := by
    apply (on_mon hw.nz (half_pos hc) hp x).trans
    unfold rhUp
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hv x) (by positivity)
  obtain ⟨Q,hQ,hV⟩:=s.cover_options _ v mix hf hs hr.cap
    (by unfold rhUp; positivity) hl hr.hl' (one_by_side_halving mix hw.nz hk P hc hp)
    (by unfold rhUp; positivity) hv' hr.hroom (hr.atlas C hC) hr.price hr.price'
    k d hr.hk hr.localQ hr.testFailure hr.testFailure' hr.beatSlack
  refine ⟨fun x=>P x∧Q x,?_,?_⟩
  · rw [pr_of_on hw.nz]
    exact mul_le_mul hp hQ (by positivity) hpp.le
  rw [←on_both w P Q hw.nz hpp (lt_of_lt_of_le (half_pos hl) hQ)]
  exact hV

end
end Lax793645Proofs.Simplifications
