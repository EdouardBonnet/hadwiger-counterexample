/- Prepared one-frame injection and compatibility bounds. Probability
bookkeeping is adapted from the vendored Apache-2.0 PreparedOutcomes. -/
import Lax793645Proofs.Simplifications.OnePreparedTrimming
import Lax793645Proofs.Simplifications.OneCoverCompatibility

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}

def oneGlowOutcome (l : Filter ℕ) (w : OneTale p M) (s : OneRhythms p M)
    (b : OneSketch p M):=∃ e : ℝ,0<e ∧ ∀ᶠ n in l,e≤oneGilded s w b n

/-- Inside each pair of independently drawn leaves, every positive
compatibility probability has at least the specified mass. -/
def oneCompatibilityFloor (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N))
    (C : OneUnit p n N × OneUnit p n N → Prop) (γ : ℝ) :=
  ∀ i j : s.T,0<pr (pairW (partW w i.val) (partW w j.val)) C →
    γ≤pr (pairW (partW w i.val) (partW w j.val)) C

theorem one_floor_mono {s : OneLeafMixture p n N} {w : Wgt (OneUnit p n N)}
    {C : OneUnit p n N × OneUnit p n N → Prop} {a b : ℝ} (hab : a≤b)
    (h : oneCompatibilityFloor s w C b) : oneCompatibilityFloor s w C a :=
  fun i j hp=>hab.trans (h i j hp)

theorem one_floor_of_code (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N))
    (R : OneUnit p n N × OneUnit p n N → Prop)
    (hw : ∀ i : s.T,IsLaw (partW w i.val)) (hh : oneCodedLeaves q s R) :
    oneCompatibilityFloor s w R 1 := by
  rintro i j hpos
  obtain ⟨code,hlabels,hread⟩:=hh
  let μ:=pairW (partW w i.val) (partW w j.val)
  have law : IsLaw μ:=pairW_law (hw i) (hw j)
  obtain ⟨v,hv,hpos⟩:=exists_of_pr_pos law.nz hpos
  have tiles (x) (hx : μ x≠0) : x.1∈i.val ∧ x.2∈j.val :=
    ⟨(onW_ne (left_ne_zero_of_mul hx)).1,(onW_ne (right_ne_zero_of_mul hx)).1⟩
  obtain ⟨hi,hj⟩:=tiles _ hpos.ne'
  have hcell:= (hread _ _ ⟨_,i.property,hi⟩ ⟨_,j.property,hj⟩).2 hv
  have hall x (hx : μ x≠0) : R x := by
    obtain ⟨hi',hj'⟩:=tiles _ hx
    apply (hread _ _ ⟨_,i.property,hi'⟩ ⟨_,j.property,hj'⟩).1
    change code.test (code.label x.1,code.label x.2)
    rw [hlabels _ i.property _ hi' _ hi,hlabels _ j.property _ hj' _ hj]
    exact hcell
  calc 1 = pr μ (fun _=>True) := by rw [pr_true,law.total]
       _ ≤ _ := (avg_congr (fun x hx=>ind_true.trans (ind_one (hall x hx)).symm)).le

def oneGlimmer (q : PreparationParameters) (l : Filter ℕ) (w : OneTale p M)
    (s : OneRhythms p M) (b : OneSketch p M):=
  ∃ e : ℝ,0<e ∧ ∀ᶠ n in l,oneCompatibilityFloor (s n) (w n) (oneMatchProg b n) e ∧
    e/((2*(M*n):ℕ):ℝ)^4≤oneGlow s w b n ∧ oneGleam s w b n≤0.001*oneGlow s w b n

theorem OneDurable.gripped (h : OneDurable q l m w s) (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n)) :
    ∀ᶠ n in l,let N:=M*n; let v:=(s n).sap (w n); let x:=(s n).rooting;
    IsLaw v ∧ ∀ P:OneUnit p n N×OneUnit p n N→Prop, named P (bp (3*(onePreparationCover q)*(2*N:ℝ))) →
      named (P ∘ Prod.swap) (bp (3*(onePreparationCover q)*(2*N:ℝ))) →
    pr (pairW v v) (fun y=>P y∧¬oneSecureAt (s n) y) ≤
      0.0005* pr (pairW v v) P +edgeError (2*N) := by
  let N (n:ℕ):=M*n
  let z (i:ℕ):ℝ:=(2*N i:ℕ)
  have hz := (one_trend_sizes l hl hq.hM).2
  let a := (0.005:ℝ)
  have ha : 0<a:=by norm_num [a]
  filter_upwards [h.mass.inv_cap a ha, expO_const hz q.L a ha, h.shape,hq.wrap.filter_mono hl,
    hw,h.mass.positive] with n hn ht hh hB hW hS
  obtain ⟨h,hF⟩:=hh
  let v:=(s n).sap (w n)
  let C := ((s n).amount (w n))⁻¹
  have hc : 0≤C := (inv_pos_of_pos hS).le
  have hm : IsLaw v:= ImageLeafMixture.sap_law hS hW.law
  have hg : oneBySide v (m n) (shine (2*N n)) := by
    refine one_upper_side hW.border (ImageLeafMixture.upper_sap hW.law hS) hc ?_
    rw [abs_of_nonneg hq.early.hL] at ht
    change |C|≤bp (a*z n) at hn
    rw [abs_of_nonneg hc] at hn
    refine (mul_le_mul hn ht hq.early.hL (bp_pos _).le).trans_eq ?_
    rw [←bp_add]; unfold a shine z; congr 1
    ring
  refine ⟨hm,fun P hp hP=> hB.2.2.2.2.2 P hp hP v (s n) (m n)
    (ImageLeafMixture.root_bound h) hm hg (fun x hx => ?_)⟩
  by_contra hzero
  exact hx (ImageLeafMixture.in_parent hF (ImageLeafMixture.present hzero).1)

theorem OneDurable.unconditional (h : OneDurable q l m w s) (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n)) :
    ∀ᶠ n in l,let v:=(s n).sap (w n);
      pr (pairW v v) (fun x=>¬oneSecureAt (s n) x) <0.01 ∧
      0.99 < pr (pairW v v) (oneSecureAt (s n)) := by
  have he :
      ∀ᶠ n in l,edgeError (2*(M*n))<0.0005 :=
    (((bp_tendsto_zero (by norm_num : 0 < (0.005:ℝ))).comp
      (one_trend_sizes l hl hq.hM).2).eventually (gt_mem_nhds (by norm_num)))
  filter_upwards [h.gripped hl hq hw,he] with n hn ht
  obtain ⟨hm,hg⟩:=hn
  let v:=(s n).sap (w n)
  let P := oneSecureAt (s n)
  have hp : 1≤bp (3*(onePreparationCover q)*(2*(M*n:ℕ):ℝ)) := by
    rw [←bp_zero]; exact bp_le (by positivity)
  have hx := hg (fun _=>True) (named_true hp) (named_true hp)
  have hv : IsLaw (pairW v v):=pairW_law hm hm
  change pr (pairW v v) (fun x=>True∧¬P x) ≤ 0.0005*pr (pairW v v) (fun _=>True)+ _ at hx
  simp only [true_and,pr_true,hv.total,mul_one] at hx
  have hh : pr (pairW v v) (fun x=>¬P x)<0.01 := by linarith only [hx,ht]
  refine ⟨hh,?_⟩; rw [pr_not,hv.total] at hh
  linarith only [hh]

variable {b : OneSketch p M}

theorem OneDurable.kindles (h : OneDurable q l m w s) (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hf : ∀ᶠ n in l,0.04 ≤ oneGlow s w b n) :
    oneGlowOutcome l w s b := by
  refine ⟨0.02, by norm_num,?_⟩
  filter_upwards [h.gripped hl hq hw,h.unconditional hl hq hw,hf] with n hn ht hv
  obtain ⟨hm,_⟩:=hn
  have hi : oneGleam s w b n <0.01 :=
    lt_of_le_of_lt (pr_mono (pairW_law hm hm).nz (fun i hi=>hi.2)) ht.1
  have hg := one_gilding s w b n hm
  linarith only [hi,hg,hv]

theorem OneDurable.coded_safety (h : OneDurable q l m w s) (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hd : ∀ᶠ n in l,oneCodedLeaves q (s n) (oneMatchProg b n)) :
    ∀ᶠ n in l,oneGleam s w b n≤0.0005*oneGlow s w b n+edgeError (2*(M*n)) := by
  filter_upwards [h.gripped hl hq hw,hd] with n hn hd
  obtain ⟨code,_,hc⟩:=hd
  let v:=(s n).sap (w n)
  let Q:=code.read
  obtain ⟨h1,h2⟩:=code.named_both
  have h3 (x) (hx : pairW v v x≠0) : Q x ↔ oneMatchProg b n x :=
    hc x.1 x.2 (ImageLeafMixture.present (left_ne_zero_of_mul hx)).1
      (ImageLeafMixture.present (right_ne_zero_of_mul hx)).1
  have hi : pr (pairW v v) Q=oneGlow s w b n := avg_congr
    (fun x hx=> congrArg ind (propext (h3 x hx)))
  have hf : oneGleam s w b n=pr (pairW v v) (fun y=> Q y∧¬oneSecureAt (s n) y) :=
    avg_congr (fun x hx=> congrArg ind (propext (and_congr_left fun _=>(h3 x hx).symm)))
  rw [hf,←hi]; exact hn.2 _ h1 h2

theorem OneDurable.coded_rare_pairs (h : OneDurable q l m w s) (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hb : ∀ᶠ n in l,oneCodedLeaves q (s n) (oneMatchProg b n))
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ᶠ n in l,δ/((2*(M*n):ℕ):ℝ)^4 ≤ oneGlow s w b n) :
    oneGlimmer q l w s b := by
  let z (n:ℕ):ℝ:=(2*(M*n):ℕ)
  have hz : Tendsto z l atTop := (one_trend_sizes l hl hq.hM).2
  have hi : ExpSmall l z (fun n=>edgeError (2*(M*n))*(z n)^4) :=
    (ExpSmall.bp_n (by norm_num)).poly hz 4
  refine ⟨min δ 1,lt_min hδ zero_lt_one,?_⟩
  filter_upwards [h.shape,hw,h.coded_safety hl hq hw hb,hb,hg,hz.eventually (eventually_gt_atTop 0),
    (hi.lim hz).eventually (gt_mem_nhds (show 0<0.0005*δ from mul_pos (by norm_num) hδ))]
    with n hs hw h hb hg he hi
  have floor := one_floor_of_code (s n) (w n) (oneMatchProg b n)
    (fun i=>on_law hw.law.nz (hs.1.leaf _ i.property).pos) hb
  refine ⟨one_floor_mono (min_le_right ..) floor,
    (div_le_div_of_nonneg_right (min_le_left ..) (by positivity)).trans hg,h.trans ?_⟩
  have hz : edgeError (2*(M*n)) ≤ 0.0005*oneGlow s w b n := calc
      _ ≤ 0.0005*δ/(z n)^4 := (le_div_iff₀ (by positivity)).mpr hi.le
      _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hg (by norm_num)
  linarith only [hz]

end
end Lax793645Proofs.Simplifications
