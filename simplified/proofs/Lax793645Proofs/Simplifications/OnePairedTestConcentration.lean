import Lax793645Proofs.Simplifications.OneTemplateConcentration
import Lax793645Proofs.Simplifications.OneGraphLaws
import Lax793645Proofs.Simplifications.OneAnalyticAsymptotics
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PairedTemplateConcentration

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter PreparationParameters
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] [Fintype A] {p : Shape} {n N : ℕ}

/-- For a fixed number of batches, keeping all Gram equations costs a constant.
The bound is relative to the individual probabilities and holds for arbitrarily small sets. -/
theorem one_pooled_hit_product {g : Route I G} (m : Mixer p n)
    (B : J → NomQuery p n g) (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N)
    (hB : ∀ i, Injective (pooled B i).mulVec)
    (hroom : ∀ i, 2*num (Port (tied g J) i)+2 ≤ (N:ℝ)) (P : J → Rack I N → Prop) :
    let μ := oneForumLaw (G:=G) m N
    pr μ (fun o => ∀ j, P j (onePeek g (B j) o)) ≤
      quadraticNetFact (tied g J) * ∏ j, pr μ (fun o => P j (onePeek g (B j) o)) := by
  classical
  let Z := database m (pooled B) (pooled B)
  let lane (j : J) := quadraticFramePart (laneM Z j) (N:=N)
  let μ := oneForumLaw (G:=G) m N
  have hj j : pr μ (fun o => P j (onePeek g (B j) o)) = pr (unifOn (lane j)) (P j) := by
    rw [←mapW_pr, one_frame_images g m hN (B j) (pool_injective hB j)]
    simp only [lane,Z,lane_pooled,quadraticStation]
  let event (x : Rack (J×I) N) := ∀ j, P j (led j x)
  have h := mapW_pr μ (onePeek (tied g J) (pooled B)) event
  rw [one_frame_images _ m hN _ hB] at h
  simp only [event,one_peek_pooled] at h
  change pr μ _ ≤ _
  rw [←h,quadraticStation,←on_unif,pr_on]
  let C := quadraticNetFact (tied g J)
  have hprod : pr unif (fun x : Rack (J×I) N => ∀ j, lane j (led j x) ∧ P j (led j x)) =
      ∏ j, pr unif (fun x => lane j x ∧ P j x) := by
    unfold pr
    simp_rw [ind_all]
    exact led_piece (Finset.univ : Finset J) (fun j x => lane j x ∧ P j x)
  have hh := pr_mono (q := fun x : Rack (J×I) N => ∀ j, lane j (led j x) ∧ P j (led j x))
    unif_law.nz (fun x (hx : quadraticFramePart Z x ∧ event x) j =>
    ⟨((quadratic_frame_road _ Z x).mp hx.1).1.2 j,hx.2 j⟩)
  have hC := quadratic_net_fact_pos (tied g J)
  refine (div_le_div₀ (pr_nonneg unif_law.nz) hh (inv_pos_of_pos hC) (quadratic_net_norm _ Z hroom)).trans ?_
  rw [hprod,div_eq_mul_inv,inv_inv,mul_comm]
  apply mul_le_mul_of_nonneg_left _ hC.le
  refine Finset.prod_le_prod (fun _ _ => pr_nonneg unif_law.nz) (fun j _ => ?_)
  rw [pr_of_on unif_law.nz (lane j),on_unif,hj]
  exact (mul_le_mul_of_nonneg_right ((pr_le_tot unif_law.nz).trans unif_law.total.le)
    (pr_nonneg (unifOn_sub _).nz)).trans_eq (one_mul _)

def oneQueryData {g : Route I G} (s : Program p n g A) (w : Wgt A)
    (o : OneForum p n N G) : Wgt (A × Rack I N) :=
  mapW w (fun x => (x,onePeek g (s.left x) o))

/-- Amplify a small-set estimate using a fixed number of independent inputs at
the same frame. Nominal dependencies are subtracted from the lower hit bound. -/
theorem one_query_small_set {g : Route I G} (m : Mixer p n) (s : Program p n g A)
    (w : Wgt A) (hw : IsLaw w) (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N)
    (l : ℕ) (hroom : ∀ i, 2*num (Port (tied g (Fin l)) i)+2 ≤ (N:ℝ))
    (r η : ℝ) (hη : 0 ≤ η) (hr : pr (draws (Fin l) w) (fun z => ¬s.free z) ≤ r)
    (S : A × Rack I N → Prop) :
    let μ := oneForumLaw (G:=G) m N
    let f o := pr (oneQueryData s w o) S
    (η^l-r)*pr μ (fun o => η ≤ f o) ≤ quadraticNetFact (tied g (Fin l)) * (avg μ f)^l := by
  classical
  let μ := oneForumLaw (G:=G) m N
  let f (o : OneForum p n N G) := pr w (fun x => S (x,onePeek g (s.left x) o))
  let D := draws (Fin l) w
  let allHit (o : OneForum p n N G) (z : Fin l → A) := ∀ j, S (z j,onePeek g (s.left (z j)) o)
  let single (x : A) := pr μ (fun o => S (x,onePeek g (s.left x) o))
  have hμ := one_forum_law (G:=G) m (show Fintype.card (Row p n)+2*p.h+1 ≤ N by omega)
  have hD : IsLaw D := draws_law hw
  have hmean : avg μ f = avg w single := avg_avg ..
  have hpow o : pr D (allHit o) = (f o)^l := by
    unfold allHit D draws
    rw [prodW_pr (fun _ : Fin l => w) (fun _ x => S (x,onePeek g (s.left x) o))]
    simp only [Finset.prod_const,card_univ,Fintype.card_fin,f]
  let event (o : OneForum p n N G) (z : Fin l → A) := allHit o z ∧ s.free z
  have hlo o : (η^l-r)*ind (η ≤ f o) ≤ pr D (event o) := by
    by_cases he : η ≤ f o
    · rw [ind_one he,mul_one]
      apply (sub_le_sub (pow_le_pow_left₀ hη he l) hr).trans
      rw [←hpow]; exact pr_shield hD.nz _ _
    rw [ind_zero he,mul_zero]; exact pr_nonneg hD.nz
  have hhi z : pr μ (fun o => event o z) ≤ quadraticNetFact (tied g (Fin l)) * ∏ j, single (z j) := by
    by_cases hz : s.free z
    · simpa only [event,allHit,hz,and_true,single,Function.comp_apply] using
        one_pooled_hit_product m (s.left ∘ z) hN hz.1 hroom (fun j k => S (z j,k))
    simp only [event,hz,and_false,pr_false]
    exact mul_nonneg (quadratic_net_fact_pos _).le (prod_nonneg fun _ _ => pr_nonneg hμ.nz)
  dsimp only
  simp_rw [oneQueryData,mapW_pr]
  refine (show (η^l-r)*pr μ (fun o => η ≤ f o) ≤ avg μ (fun o => pr D (event o)) by
    rw [pr,←avg_mul']; exact avg_mono hμ.nz hlo).trans ?_
  rw [show avg μ (fun o => pr D (event o)) = avg D (fun z => pr μ (fun o => event o z)) from avg_avg ..]
  refine (avg_mono hD.nz hhi).trans_eq ?_
  rw [avg_mul',hmean,poweravg]

private theorem one_query_thin {g : Route I G} (M : ℕ) (hM : 1 ≤ M)
    (b η c : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ l : ℕ, ∀ r : ℝ, ∀ᶠ n : ℕ in atTop, let N := M*n
      ∀ (m : Mixer p n) (A : Type) [Fintype A] (s : Program p n g A) (w : Wgt A), IsLaw w →
      Fintype.card (Row p n)+2*p.h+3 ≤ N →
      pr (draws (Fin l) w) (fun x => ¬s.free x) ≤ bp (r-n) →
      thinData (oneForumLaw m N) (oneQueryData s w) (bp (-c*n)) η (bp (-b*n)) := by
  obtain ⟨l,hl⟩ := exists_nat_gt (b/c)
  let d := η^l/2
  have hd : 0 < d := by dsimp [d]; positivity
  let t := tied g (Fin l)
  let k := num (Fin l × I)
  refine ⟨l,fun r => ?_⟩
  filter_upwards [pay_div_nat (a:=1) (bp r) d hd (b:=0) (by norm_num),
    pay_div_nat (a:=c*l) (quadraticNetFact t) d hd (b:=b)
      (by rwa [div_lt_iff₀ hc,mul_comm] at hl),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+2))]
    with n hn hh hk N m A _ s w hw hN hr P hP
  let μ := oneForumLaw (G:=G) m N
  let f o := pr (oneQueryData s w o) P
  have hi : bp (r-n) ≤ d := by
    simpa only [neg_zero,zero_mul,bp_zero,mul_one,←bp_add,neg_mul,one_mul,←sub_eq_add_neg] using hn
  have hz : avg μ f ≤ bp (-c*n) := by
    rw [←show avg (mixW μ (oneQueryData s w)) (fun x => ind (P x)) = avg μ f from mixW_avg ..]
    exact hP
  have hμ := one_forum_law (G:=G) m (show Fintype.card (Row p n)+2*p.h+1 ≤ N by omega)
  have hpower := one_query_small_set m s w hw hN l (fun i => by
    have := port_limit t i; change 2*k+2 ≤ (N:ℝ) at hk; linarith only [this,hk])
    (bp (r-n)) η hη.le hr P
  apply le_of_mul_le_mul_left _ hd
  calc
    d * pr μ (fun o => η ≤ f o) ≤ (η^l-bp (r-n))*pr μ (fun o => η ≤ f o) := by
      apply mul_le_mul_of_nonneg_right _ (pr_nonneg hμ.nz)
      dsimp only [d] at hi ⊢; linarith only [hi]
    _ ≤ _ := hpower
    _ ≤ quadraticNetFact t * bp (-c*n)^l := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (avg_nonneg hμ.nz fun o => pr_nonneg (mapW_law hw _).nz) hz l)
      (quadratic_net_fact_pos _).le
    _ ≤ _ := by rw [←bp_mul_nat,show -c*n*l = -(c*l)*n by ring]; exact hh

private theorem one_query_deviation {g : Route I G} (M : ℕ) (hM : 1 ≤ M)
    (r η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, let N := M*n
      ∀ (m : Mixer p n) (A : Type) [Fintype A] (s : Program p n g A) (w : Wgt A), IsLaw w →
      Fintype.card (Row p n)+2*p.h+3 ≤ N →
      pr (draws Bool w) (fun x => ¬s.free x) ≤ bp (r-n) →
      approxData (oneForumLaw m N) (oneQueryData s w) η (bp (-(1/4:ℝ)*n)) := by
  filter_upwards [one_variance_calendar p M g r (η^2) (by positivity) hM]
    with n hn N m A _ s w hw hN he T hT
  have hμ := one_forum_law (G:=G) m (show Fintype.card (Row p n)+2*p.h+1 ≤ N by omega)
  rw [mixW_avg]
  simp_rw [oneQueryData,mapW_avg]
  refine (outlier hμ.nz _ η hη
    (hn m _ s (fun x y => T (x,y)) w hw (fun x y => hT _) hN he)).trans_eq ?_
  field_simp

/-- A test of both complete endpoint samples, fixed before the unit is drawn.
It may read every nominal input as well as every key. The endpoint frames of
the unit may be correlated. Only its two marginal caps and joint cap enter. -/
theorem one_paired_fixed_test (v : Template p I) (z : Template p J)
    (M : ℕ) (hM : 1 ≤ M) (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n
      ∀ (m : Mixer p n) (ρ : Wgt (OneUnit p n N)), IsLaw ρ →
      (∀ i o, mapW ρ (fun x => x i) o ≤ bp ((1/32:ℝ)*n)*oneRaw m N o) →
      (∀ x, ρ x ≤ bp (C*N)*oneUnitRaw m N x) →
      Fintype.card (Row p n)+2*p.h+3 ≤ N →
      ∀ (u : I → Wgt (Knobs p.g n)) (w : J → Wgt (Knobs p.g n)),
      (∀ i, IsLaw (u i)) → (∀ i, mapW (u i) (freePart p)=unif) →
      (∀ j, IsLaw (w j)) → (∀ j, mapW (w j) (freePart p)=unif) →
      ∀ T : Wgt (v.Datum n N × z.Datum n N), (∀ y, |T y| ≤ 1) →
      let f (x : OneUnit p n N) := avg (pairW (oneQueryData (v.singleP n) (prodW u) (x true))
        (oneQueryData (z.singleP n) (prodW w) (x false))) T
      pr ρ (fun x => ε ≤ |f x-avg (oneUnitRaw m N) f|) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let η := ε/5
  have hη : 0 < η := by dsimp [η]; positivity
  let g := ownPort (p:=p) v.t
  let g' := ownPort (p:=p) z.t
  obtain ⟨l,hl⟩ := one_query_thin (p:=p) (g:=g') M hM (C*M+1) η (1/8) (by norm_num) hη
  filter_upwards [one_query_deviation (p:=p) (g:=g) M hM (num Bool*num I) η hη,
    one_query_deviation (p:=p) (g:=g') M hM (num Bool*num J) η hη,
    hl (num (Fin l)*num J),paired_price M C]
    with n ha hb ht hc N m ρ hρ hm hj hN u w hu hzu hw hzw T hT f
  let μ := oneRaw m N
  let E := onePairEquiv p n N
  let ρ' := mapW ρ E.symm
  have hcap i : ∀ o, mapW ρ' (fun x => E x i) o ≤ bp ((1/32:ℝ)*n)*μ o := by
    intro o
    simpa only [ρ',mapW_nested,Function.comp_def,Equiv.apply_symm_apply] using hm i o
  have hA : ∀ o, mapW ρ' Prod.fst o ≤ _ := hcap true
  have hB : ∀ o, mapW ρ' Prod.snd o ≤ _ := hcap false
  have hJ x : ρ' x ≤ bp (C*N)*pairW μ μ x := by
    have h := hj (E x)
    rwa [←one_pair_raw m,mapW_equiv_val,Equiv.symm_apply_apply,
      ←show ρ' x = ρ (E x) from mapW_equiv_val ..] at h
  let left := oneQueryData (v.singleP n) (prodW u) (N:=N)
  let right := oneQueryData (z.singleP n) (prodW w) (N:=N)
  have hraw := one_raw_law m (show Fintype.card (Row p n)+2*p.h+1 ≤ N by omega)
  have H := paired_spread T left right hraw hraw (mapW_law hρ E.symm)
    (fun _ => mapW_law (prodW_law hu) _) (fun _ => mapW_law (prodW_law hw) _) hT
    η _ _ _ hη (bp_pos _) (bp_pos _).le
    (ha m _ _ _ (prodW_law hu) hN (v.free_price n u hu hzu g v.own_inj))
    (hb m _ _ _ (prodW_law hw) hN (z.free_price n w hw hzw g' z.own_inj))
    (ht m _ _ _ (prodW_law hw) hN (z.free_price n w hw hzw g' z.own_inj))
    _ _ (bp_pos _).le (bp_pos _).le hA hB hJ
  have H' := H.trans hc
  change pr ρ' (fun x => 5*η ≤ |f (E x) - avg (pairW μ μ) (fun y => f (E y))|) ≤ _ at H'
  dsimp only [ρ'] at H'
  rw [show 5*η=ε by dsimp [η]; ring, ←mapW_avg,one_pair_raw,mapW_pr] at H'
  simpa only [Equiv.apply_symm_apply] using H'

/-- Fix the opposite leaf before applying the mixed-law bound. Both leaves
may select the test from its finite family and further restrict the unit. -/
theorem independent_leaf_tests {X : Type} [Fintype X] (u : Wgt X) (T : Tiles X)
    (hu : ∀ o, 0 ≤ u o) (hT : apart T) (hp : ∀ i ∈ T, 0 < partMass u i)
    (hm : 0 < allMass u T) {L : Type} [Fintype L] (B : T → L → X → Prop)
    (chooseTest : T × T → L) (P : T × T → X → Prop) (δ : ℝ)
    (hbad : ∀ j k, pr (allW u T) (B j k) ≤ δ) :
    let π := portionW u T
    avg (pairW π π) (fun ij => pr (partW u ij.1.val)
      (fun o => P ij o ∧ B ij.2 (chooseTest ij) o)) ≤ Fintype.card L * δ := by
  obtain ⟨hπ,hmix⟩ := rebuild hu hT hp hm
  dsimp only
  rw [pairW_avg,avg_avg]
  apply hπ.avg_le
  intro j
  let Q o := ∃ k, B j k o
  have h := avg_mono hπ.nz (fun i : T => pr_mono (w:=partW u i.val) (normW_nonneg (subW_nonneg hu _))
    (q:=Q) (fun o (h : P (i,j) o ∧ B j (chooseTest (i,j)) o) => ⟨_,h.2⟩))
  refine h.trans ?_
  rw [show avg (portionW u T) (fun i => pr (partW u i.val) Q) = pr (allW u T) Q from
    hmix ▸ (mixW_avg (portionW u T) (fun i => partW u i.val) (fun o => ind (Q o))).symm]
  refine (pr_exists_le (w:=allW u T) (normW_nonneg (subW_nonneg hu _)) (B j)).trans ?_
  simpa only [Finset.sum_const,card_univ,nsmul_eq_mul] using
    (sum_le_sum (s:=univ) (g:=fun _ => δ) (fun k _ => hbad j k))

set_option maxHeartbeats 800000 in
/-- Both endpoint frames in a unit come from the actual prepared law. The
size of the opposite leaf's test family enters only as a multiplicative factor.
The exceptional mass is charged before any restriction to compatible pairs. -/
theorem OneVeil.opposite_leaf_tests {M s0 : ℕ} {q : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} (h : OneVeil p M q s0 l m s w)
    (v : Template p I) (z : Template p J) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in l, let N := M*n
      ∀ (u : I → Wgt (Knobs p.g n)) (u' : J → Wgt (Knobs p.g n)),
      (∀ i, IsLaw (u i)) → (∀ i, mapW (u i) (freePart p)=unif) →
      (∀ j, IsLaw (u' j)) → (∀ j, mapW (u' j) (freePart p)=unif) →
      ∀ (L : Type) [Fintype L] (test : (s n).T → L → Wgt (v.Datum n N × z.Datum n N)),
      (∀ j k y, |test j k y| ≤ 1) →
      ∀ (select : (s n).T × (s n).T → L) (P : (s n).T × (s n).T → OneUnit p n N → Prop),
      let π := portionW (w n) (s n).T
      let f j k (x : OneUnit p n N) :=
        avg (pairW (oneQueryData (v.singleP n) (prodW u) (x true))
          (oneQueryData (z.singleP n) (prodW u') (x false))) (test j k)
      avg (pairW π π) (fun ij => pr (partW (w n) ij.1.val) (fun x =>
        P ij x ∧ ε ≤ |f ij.2 (select ij) x - avg (oneUnitRaw (m n) N) (f ij.2 (select ij))|)) ≤
        Fintype.card L * bp (-(1/16:ℝ)*n) := by
  have hpair := one_paired_fixed_test v z M h.parameters.planted.hM (2*q.spJoint) ε hε
  filter_upwards [hpair.filter_mono h.time,h.query_caps,h.durable.shape,h.moment,
    h.durable.mass.positive,h.parameters.planted.unary_room.filter_mono h.time]
    with n hc hcaps hshape hgood hmass hroom N u u' hu hzu hu' hzu' L _ test hb select P
  let ρ := (s n).sap (w n)
  have cap x : ρ x ≤ bp ((2*q.spJoint)*(M*n : ℕ))*oneUnitRaw (m n) (M*n) x := by
    rw [show (2*q.spJoint)*((M*n : ℕ):ℝ) = q.spJoint*(2*((M*n : ℕ):ℝ)) by ring]
    simpa only [Nat.cast_mul] using hcaps.2.2 x
  let f j k (x : OneUnit p n N) := avg (pairW
    (oneQueryData (v.singleP n) (prodW u) (x true))
    (oneQueryData (z.singleP n) (prodW u') (x false))) (test j k)
  let bad (j : (s n).T) (k : L) x := ε ≤ |f j k x-avg (oneUnitRaw (m n) N) (f j k)|
  have hbad j k : pr ρ (bad j k) ≤ bp (-(1/16:ℝ)*n) :=
    hc (m n) ρ hcaps.1 hcaps.2.1 cap hroom u u' hu hzu hu' hzu' (test j k) (hb j k)
  exact independent_leaf_tests (w n) (s n).T hgood.1.law.nz hshape.1.part
    (fun i hi => (hshape.1.leaf i hi).pos) hmass bad select P _ hbad

end
end Lax793645Proofs.Simplifications
