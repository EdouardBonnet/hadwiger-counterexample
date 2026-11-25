import Lax793645Proofs.Simplifications.OnePhasePreparedOutcomes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M} {P : OneCampaign p M}

set_option maxHeartbeats 1200000 in
/-- The zero-discrepancy branch uses the linear-cell contradiction at
the dosed mixed law, before subsequent trimming or compatibility restrictions. -/
theorem one_phase_absent_linear (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hroom : ∃ d : ℕ,(p.g-1)/2+2*q.D≤d ∧
      2*oneScreenRank p q.e+1≤privateWidth p.g*(p.g-d)*p.r)
    (hjoins : ∀ᶠ n in l,(s n).within (fun x=>oneJoins x≤2*q.D))
    (hb : OneDosed q l m w s b P)
    (hlin : ∀ᶠ n in l,∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (b.g i n) R)
    (he : ∀ᶠ n in l,∀ x,P n x → oneMarkedDelta x (b.m n x)=0) :
    oneFinished q l m w b := by
  classical
  obtain ⟨d,h1,h2⟩:=hroom
  have hB : q.B<Fintype.card (Label p.b) := by
    have he : (↑(Fintype.card (Label p.b)):ℝ)=bp ((p.b:ℕ):ℝ) := by
      simp [Label,bp_nat,F,ZMod.card]
    exact_mod_cast (hq.hB.trans_le ((bp_le (by linarith [(Nat.cast_nonneg p.j :
      0≤(p.j:ℝ))])).trans_eq he.symm))
  obtain ⟨ε,hε,h⟩:=one_linear_silicon_calendar p M q.e q.D d q.B h1 hB hq.hJ hq.hg hq.hR
    h2 q.spear
  refine one_by_torch hl hq hw hx (hb.citable hl hq.hM) ?_
  filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hx,hb.mark,h.filter_mono hl,
    hb.forecast.small ε hε,hb.capped,hlin,hjoins]
    with n hn ht hv hx hs hh hδ hz hlin hjoins
  obtain ⟨R,hR,hlin⟩:=hlin
  let v:=onePotion s w P n
  have heq (x) (hh : v x≠0) :
      (oneRawHoles (m n)).unit (x true,x false) ∧ oneJoins x≤2*q.D ∧ oneFrameSide (m n) x ∧
        oneMarkedDelta x (b.m n x)=0 ∧ oneEngrave b q m s n x := by
    obtain ⟨hp,hx'⟩:=onW_ne hh
    obtain ⟨⟨i,hi,hx'⟩,_⟩:=ImageLeafMixture.present hx'
    obtain ⟨_,h1,h3⟩:=hx.onTile i hi x hx'
    exact ⟨h1,hjoins i hi x hx',h3,hv x hp,hs x hp⟩
  have hi : b.α true=b.α false := by
    have hroom : Fintype.card (Row p n)+2*p.h+1≤M*n := by
      have hr:=ht.1
      rw [one_full_dimension] at hr
      omega
    refine hh _ hroom ht.2.1 v b.α (fun i=>b.g i n) R hR hlin hn.1 hn.2.1 (fun x hc=>?_)
    obtain ⟨_,h2,h3,h4,⟨h5,h6⟩,_,_⟩:=heq x hc
    refine ⟨h2,b.m n x,b.L n x,fun i=>⟨(h5 i).1,((one_effective_mem _ _ _).mp (h5 i).2).1,
      hz x i,h3 i⟩,one_zero_delta (b.m n) x h4,?_⟩
    exact fun i z h l g=>(h6 i z h l g).trans hδ
  have hm (x) (h : pairW v v x≠0) : oneMatchProg b n x := by
    have hx:=heq x.1 (left_ne_zero_of_mul h)
    have hy:=heq x.2 (right_ne_zero_of_mul h)
    refine one_fade b.c b.α b.r hb.forecast.light hi (fun HD=>?_) _ x
      hx.2.2.2.1 hy.2.2.2.1
    obtain ⟨he,_,hF,hD,⟨hg,_⟩,hh,hx⟩:=hx
    exact hh.symm.trans (one_delta_dusk (m n) (b.m n) _ (fun i=>((one_effective_mem _ _ _).mp (hg i).2).1)
      (hx HD) hD he hF)
  have hi : oneCharm s w P b n=pr (pairW v v) (fun _=>True) := avg_congr (fun i hi=>
    (ind_one (hm i hi)).trans ind_true.symm)
  have hv : IsLaw v:=hn.1
  rw [hi,pr_true,(pairW_law hv hv).total]
  norm_num

end
end Lax793645Proofs.Simplifications
