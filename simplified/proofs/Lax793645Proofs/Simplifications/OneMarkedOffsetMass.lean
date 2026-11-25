import Lax793645Proofs.Simplifications.OnePreparedPhase
import Lax793645Proofs.Simplifications.TensorQuotientReduction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function Filter PreparationParameters
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

/-- The sum of two symmetric tensors supported on the two primal images
cannot have a nonzero column space disjoint from both images. -/
theorem one_offset_column_meets_primal (x : OneUnit p n N) (z : Bool → Profile p n)
    (hz : ∀ i, z i ∈ Xspace p n) (e : Comp p.g) (he : oneMarkedDelta x z e ≠ 0) :
    ∃ i, ¬Disjoint (onePrimalImages x i e) (colSp (oneMarkedDelta x z e)) := by
  classical
  let A i := oneImageProfile (x i) (z i) e
  let T i := onePrimalImages x i e
  let W := oneMarkedDelta x z e
  have hsym i : (A i)ᵀ = A i := one_image_profile_symmetric _ _ (hz i) e
  have hcol i : colSp (A i) ≤ T i := ((box_mem ..).mp (one_image_profile_box x i (z i) e)).1
  have hleft (i : Bool) (a b : Vec (Fin (2*N))) (ha : a ∈ annih (T i)) : evmat (A i) a b = 0 :=
    evmat_annih_column _ _ _ (annih_antitone (hcol i) ha)
  have hre : W = A true + A false := rfl
  have hv : vanish (T true) (T false) W := by
    intro a ha b hb
    rw [hre,evmat_addM,hleft true a b ha,zero_add,←evmat_transpose,hsym]
    exact hleft false b a hb
  have hs : Wᵀ = W := by rw [hre,transpose_add,hsym,hsym]
  by_contra! hd
  have hq := vanish_column_intersections W hs _ _ hv
  rw [(hd true).symm.eq_bot,(hd false).symm.eq_bot] at hq
  have hh := rank_vanish hq
  have hzero : dim (⊥ : Space (Vec (Fin (2*N)))) = 0 := by simp [dim]
  rw [hzero,zero_add] at hh
  have hpos := matrix_nonzero_rank he
  change 1 ≤ W.rank at hpos
  omega

/-- Under the genuine endpoint caps a list of prescribed nonzero offsets has
small mass. The marks may vary arbitrarily with the entire sampled unit. -/
theorem one_offset_list_mass (m : Mixer p n) (w : Wgt (OneUnit p n N)) (hw : SubLaw w)
    (marks : OneUnit p n N → Bool → Profile p n) (H : ℝ) (hH : 0 ≤ H)
    (hside : ∀ i o,mapW w (fun x => x i) o ≤ H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1 ≤ N) (hN : 5 ≤ N)
    (hmarks : ∀ x, w x ≠ 0 → ∀ i, marks x i ∈ Xspace p n)
    (r : ℕ) (hr : ∀ x, w x ≠ 0 → epoch p (oneMarkedDelta x (marks x)) ≤ r)
    (S : Finset (Ambient p (2*N))) :
    pr w (fun x => oneMarkedDelta x (marks x) ∈ S ∧ oneMarkedDelta x (marks x) ≠ 0) ≤
      S.card * (2*H*bp (num (Row p n)+r+3-2*(N:ℝ))) := by
  classical
  let Δ x := oneMarkedDelta x (marks x)
  let price := H*bp (num (Row p n)+r+3-2*(N:ℝ))
  have hprice : 0 ≤ price := mul_nonneg hH (bp_pos _).le
  let E (v : Ambient p (2*N)) x := Δ x = v ∧ v ≠ 0
  have hv (v : Ambient p (2*N)) : pr w (E v) ≤ 2*price := by
    by_cases realized : ∃ x, w x ≠ 0 ∧ E v x
    · obtain ⟨x,hx,hxv,hv0⟩ := realized
      obtain ⟨e,he⟩ : ∃ e, v e ≠ 0 := by
        by_contra! h; exact hv0 (funext h)
      have hle : (v e).rank ≤ r := by
        have hall := hr x hx
        change epoch p (Δ x) ≤ r at hall; rw [hxv] at hall
        exact (single_le_sum (f:=fun c => (v c).rank) (fun _ _ => Nat.zero_le _) (mem_univ e)).trans hall
      let bad (i : Bool) (y : OneUnit p n N) := ¬Disjoint (onePrimalImages y i e) (colSp (v e))
      have hbad i : pr w (bad i) ≤ price := by
        refine (one_unit_cover_component m i hH hw (hside i) hroom hN e (colSp (v e))).trans ?_
        have hd : dim (colSp (v e)) ≤ r := hle
        dsimp only [price]
        gcongr
      refine ((pr_mono_support w hw.nz (Q:=fun y => ∃ i, bad i y) ?_).trans (pr_exists_le hw.nz bad)).trans ?_
      · intro y hy hyE
        obtain ⟨i,hi⟩ := one_offset_column_meets_primal y (marks y) (hmarks y hy) e
          (by change Δ y e ≠ 0; rw [hyE.1]; exact he)
        exact ⟨i,by change ¬Disjoint _ (colSp (Δ y e)) at hi; rwa [hyE.1] at hi⟩
      simp only [Fintype.sum_bool]
      linarith only [hbad false,hbad true]
    have hz : pr w (E v) ≤ pr w (fun _ => False) :=
      pr_mono_support w hw.nz fun x hx hxv => realized ⟨x,hx,hxv⟩
    rw [pr_false] at hz; linarith only [hz,hprice]
  refine ((pr_mono hw.nz (q:=fun x => ∃ v ∈ S, E v x)
    (fun x (hx : Δ x ∈ S ∧ Δ x ≠ 0) => ⟨Δ x,hx.1,rfl,hx.2⟩)).trans (pr_union_le hw.nz S E)).trans ?_
  simpa only [sum_const,nsmul_eq_mul,mul_assoc] using
    (sum_le_sum (s:=S) (g:=fun _ => 2*price) (fun v _ => hv v))

/-- Nonzero offsets of a prepared marked population avoid every subspace of
dimension at most half the ambient vector dimension, with exponentially small
error. The subspace can be chosen after the population and its marks are fixed. -/
theorem OneDosed.offset_span_dispersion {M : ℕ} {q : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
    {P : OneCampaign p M} (h : OneDosed q l m w s b P) (hl : l ≤ atTop)
    (hq : OnePlanted q p M) (hw : ∀ᶠ n in l, OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l, OneEntered q (m n) (w n) (s n)) :
    ∀ᶠ n in l, let N := M*n
      ∀ V : Space (Ambient p (2*N)), dim V ≤ N →
      pr (onePotion s w P n) (fun x => oneMarkedDelta x (b.m n x) ∈ V ∧
        oneMarkedDelta x (b.m n x) ≠ 0) ≤ bp (-(1/4:ℝ)*N) := by
  classical
  have hH : 0 ≤ q.spear := mul_nonneg (bp_pos _).le hq.early.hL
  have ht := (trend_sizes l hl (M:=M) hq.hM).1
  have pay := ht.eventually (pay_nat (a:=1/2) (b:=1/4) (2*q.spear*bp ((q.rank:ℝ)+3)) (by norm_num))
  filter_upwards [h.stake hl hq hw hx,hq.wrap.filter_mono hl,h.capped,h.mark,
    ht.eventually (eventually_ge_atTop 5),pay]
    with n hu hwrap hcap hmark h5 hpay N V hV
  let u := onePotion s w P n
  let Δ (x : OneUnit p n N) := oneMarkedDelta x (b.m n x)
  let emb : V ↪ Ambient p (2*N) := ⟨Subtype.val,Subtype.val_injective⟩
  let S : Finset (Ambient p (2*N)) := univ.map emb
  have hs (v : Ambient p (2*N)) : v ∈ S ↔ v ∈ V := by
    constructor
    · intro h
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp h
      exact a.property
    · intro hv
      exact Finset.mem_map.mpr ⟨⟨v,hv⟩,mem_univ _,rfl⟩
  have hr := hwrap.1
  rw [one_full_dimension] at hr
  have hroom : Fintype.card (Row p n)+2*p.h+1 ≤ N := by dsimp only [N]; omega
  have bound := one_offset_list_mass (m n) u hu.1.sub (b.m n) q.spear hH hu.2.1 hroom h5
    (fun x hx i => ((one_effective_mem _ _ _).mp (((hmark x (onW_ne hx).1).1.1 i).2)).1)
    q.rank (fun x _ => one_epic_bounds x (b.m n x) (hcap x)) S
  simp_rw [hs] at bound
  rw [show S.card = Fintype.card V by simp [S],card_space] at bound
  refine bound.trans ?_
  have hrow : (num (Row p n):ℝ) ≤ N/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact_mod_cast (show Fintype.card (Row p n)*2 ≤ N by dsimp only [N]; omega)
  calc
    _ = 2*q.spear * (bp (dim V)*bp (num (Row p n)+q.rank+3-2*N)) := by ring
    _ = 2*q.spear * bp ((dim V:ℝ)+num (Row p n)+q.rank+3-2*N) := by rw [←bp_add]; congr 2; ring
    _ ≤ 2*q.spear * bp (((q.rank:ℝ)+3)+(-(1/2:ℝ)*N)) := by
      apply mul_le_mul_of_nonneg_left (bp_le _) (by positivity)
      linarith only [hrow,show (dim V:ℝ) ≤ N by exact_mod_cast hV]
    _ = (2*q.spear*bp ((q.rank:ℝ)+3))*bp (-(1/2:ℝ)*N) := by rw [bp_add]; ring
    _ ≤ _ := hpay

end
end Lax793645Proofs.Simplifications
