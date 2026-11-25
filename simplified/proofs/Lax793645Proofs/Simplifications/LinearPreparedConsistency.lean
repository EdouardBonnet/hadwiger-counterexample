import Lax793645Proofs.Simplifications.LinearZeroDiscrepancy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PreliminaryRestrictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P : Campaign p M}

set_option maxHeartbeats 1200000 in
/-- The zero-discrepancy branch uses the linear-cell contradiction at
the dosed mixed law, before subsequent trimming or compatibility restrictions. -/
theorem phaseAbsent_linear_fixed (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (hlin : ∀ᶠ n in l,∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,LinearAugur (b.g i n) R)
    (he : ∀ᶠ n in l,(s n).within (fun x=>P n x→delta (b.m n) x=0)) :
    finished q l p M m w b := by
  classical
  obtain ⟨d,h1,h2⟩:=hq.room
  have hB : q.B<Fintype.card (Label p.b) := by
    have he : (↑(Fintype.card (Label p.b)):ℝ)=bp ((p.b:ℕ):ℝ) := by
      simp [Label,bp_nat,F,ZMod.card]
    exact_mod_cast (hq.hB.trans_le ((bp_le (by linarith [(Nat.cast_nonneg p.j :
      0≤(p.j:ℝ))])).trans_eq he.symm))
  obtain ⟨ε,hε,h⟩:=linear_silicon_calendar p M q.e q.D d q.B h1 hq.hD hB hq.hJ hq.hg hq.hR
    h2 q.spear
  refine byTorch_fixed hl hq hw hx hb.cite ?_
  filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hx,hb.cite.mark,h.filter_mono hl,
    hb.cite.forecast.small ε hε,hb.capped,hlin]
    with n hn ht hv hx hs hh hδ hz hlin
  obtain ⟨R,hR,hlin⟩:=hlin
  let v:=potion s w P n
  have heq (x) (hh : v x≠0) :
      (rawHoles (m n)).unit x ∧ joins x≤2*q.D ∧ frameSide p (m n) x ∧
        delta (b.m n) x=0 ∧ engrave b q m s n x := by
    obtain ⟨hp,hx'⟩:=onW_ne hh
    obtain ⟨⟨i,hi,hx'⟩,_⟩:=LeafMixture.present hx'
    obtain ⟨_,h1,h2,h3⟩:=hx.onTile i hi x hx'
    exact ⟨h1,h2,h3,hv i hi x hx' hp,hs i hi x hx' hp⟩
  have hi : b.α true=b.α false := by
    refine hh _ ht.1 v b.α (fun i=>b.g i n) R hR hlin hn.1 hn.2.1 (fun x hc=>?_)
    obtain ⟨_,h2,h3,h4,⟨h5,h6⟩,_,_⟩:=heq x hc
    refine ⟨h2,b.m n x,b.L n x,fun i=>⟨(h5 i).1,(effective_mem.mp (h5 i).2).1,
      hz x i,h3 i⟩,zero_delta (b.m n) x h4,?_⟩
    exact fun i z h l g=>(h6 i z h l g).trans hδ
  have hm (x) (h : pairW v v x≠0) : matchProg b n x := by
    have hx:=heq x.1 (left_ne_zero_of_mul h)
    have hy:=heq x.2 (right_ne_zero_of_mul h)
    refine fade b.c b.α b.r hb.cite.forecast.light hi (fun HD=>?_) _ x
      hx.2.2.2.1 hy.2.2.2.1
    obtain ⟨he,_,hF,hD,⟨hg,_⟩,hh,hx⟩:=hx
    exact hh.symm.trans (delta_dusk (m n) (b.m n) _ (fun i=>(effective_mem.mp (hg i).2).1)
      (hx HD) hD he hF)
  have hi : charm s w P b n=pr (pairW v v) (fun _=>True) := avg_congr (fun i hi=>
    (ind_one (hm i hi)).trans ind_true.symm)
  have hv : IsLaw v:=hn.1
  rw [hi,pr_true,(pairW_law hv hv).total]
  norm_num

end
end Lax793645Proofs.Simplifications
