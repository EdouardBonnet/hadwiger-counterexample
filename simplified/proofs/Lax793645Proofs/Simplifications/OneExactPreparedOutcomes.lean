import Lax793645Proofs.Simplifications.OnePhasePreparedOutcomes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M} {P : OneCampaign p M}

/-- The exact tester support count has already identified the endpoint
bits. The zero-discrepancy branch needs only the finite phase table. -/
theorem one_phase_absent_exact (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneDosed q l m w s b P) (hα : b.α true=b.α false)
    (he : ∀ᶠ n in l,∀ x,P n x→ oneMarkedDelta x (b.m n x)=0) :
    oneFinished q l m w b := by
  classical
  refine one_by_torch hl hq hw hx (hb.citable hl hq.hM) ?_
  filter_upwards [hb.stake hl hq hw hx,he,hx,hb.mark] with n hn hv hx hs
  let v:=onePotion s w P n
  have heq (x) (hh : v x≠0) :
      (oneRawHoles (m n)).unit (x true,x false) ∧ oneFrameSide (m n) x ∧
        oneMarkedDelta x (b.m n x)=0 ∧ oneEngrave b q m s n x := by
    obtain ⟨hp,hx'⟩:=onW_ne hh
    obtain ⟨⟨i,hi,hx'⟩,_⟩:=ImageLeafMixture.present hx'
    obtain ⟨_,h1,h3⟩:=hx.onTile i hi x hx'
    exact ⟨h1,h3,hv x hp,hs x hp⟩
  have hm (x) (h : pairW v v x≠0) : oneMatchProg b n x := by
    have hx:=heq x.1 (left_ne_zero_of_mul h)
    have hy:=heq x.2 (right_ne_zero_of_mul h)
    refine one_fade b.c b.α b.r hb.forecast.light hα (fun HD=>?_) _ x
      hx.2.2.1 hy.2.2.1
    obtain ⟨hunit,hF,hD,⟨hg,_⟩,hh,hink⟩:=hx
    exact hh.symm.trans (one_delta_dusk (m n) (b.m n) _
      (fun i=>((one_effective_mem _ _ _).mp (hg i).2).1) (hink HD) hD hunit hF)
  have hi : oneCharm s w P b n=pr (pairW v v) (fun _=>True) :=
    avg_congr (fun x hx=>(ind_one (hm x hx)).trans ind_true.symm)
  rw [hi,pr_true,(pairW_law hn.1 hn.1).total]
  norm_num

end
end Lax793645Proofs.Simplifications
