import Lax793645Proofs.Simplifications.OneNaturalHistograms
import Lax793645Proofs.Simplifications.OnePairedCollisionBounds
import Lax793645Proofs.Simplifications.PredictedRareEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem uniform_weights_instances {A:Type} (i j:Fintype A) (P:A→Prop):
    @unifOn A i P=@unifOn A j P := by
  cases Subsingleton.elim i j
  rfl

theorem overlap_of_mixtures {A B T : Type} [Fintype A] [Fintype B] [Fintype T]
    (ν : Wgt T) (μ : Wgt A) (π : Wgt B) (f : A→Wgt T) (g : B→Wgt T) :
    overlap ν (mixW μ f) (mixW π g)=
      avg (pairW μ π) (fun o=>overlap ν (f o.1) (g o.2)) := by
  unfold overlap density
  rw [avg_avg (pairW μ π) ν]
  apply avg_congr
  intro k _
  rw [pairW_avg]
  simp only [mixW,div_eq_mul_inv,avg_mul',avg_mul]

/-- Choose the cheaper side separately at each key. The mass lost by this cut
is at most the square root of the collision overlap, also for unnormalized queries. -/
theorem key_cut_sq_le_overlap {T : Type} [Fintype T] (ν a b : Wgt T)
    (hν : SubLaw ν) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hs : ∀ k, ν k = 0 → a k = 0) :
    let C := fun k => a k ≤ b k
    (pr a C + pr b (fun k => ¬ C k))^2 ≤ overlap ν a b := by
  classical
  let f k := min (a k) (b k) / ν k
  have cut : pr a (fun k => a k ≤ b k) + pr b (fun k => ¬ a k ≤ b k) = avg ν f := by
    unfold pr avg
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro k _
    have hm : ν k * f k = min (a k) (b k) := by
      by_cases h : ν k = 0
      · simp [h,hs k h,min_eq_left (hb k)]
      dsimp [f]
      field_simp
    rw [hm]
    by_cases h : a k ≤ b k
    · simp [ind,h]
    simp [ind,h,min_eq_right (le_of_not_ge h)]
  change (_ + _)^2 ≤ _
  rw [cut]
  have hcs := avg_CS hν.nz f (fun _ => 1)
  simp only [mul_one, one_pow, avg_const] at hcs
  apply hcs.trans
  calc
    _ ≤ avg ν (fun k => (f k)^2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hν.total
        (avg_nonneg hν.nz (fun k => sq_nonneg (f k)))
    _ ≤ _ := by
      apply avg_mono hν.nz
      intro k
      rw [sq]
      exact mul_le_mul (div_le_div_of_nonneg_right (min_le_left ..) (hν.nz k))
        (div_le_div_of_nonneg_right (min_le_right ..) (hν.nz k))
        (div_nonneg (le_min (ha k) (hb k)) (hν.nz k)) (div_nonneg (ha k) (hν.nz k))

namespace OneQuill
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}

def keyWeight (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (P : OneUnit p n N→Prop)
    (m : Mixer p n) (s : Charts p n d) (o : OneUnit p n N) (k : OneKeys t N) :=
  mapW ((w.pen t).state z n) (fun x=>oneVolleyKeys ((w.pen t).draw x) t o) k *
    ind (P o ∧ feasibleKey w t z pin K m s o k)

theorem key_weight_mono (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) {P Q : OneUnit p n N→Prop}
    (m : Mixer p n) (s : Charts p n d) (o : OneUnit p n N) (k : OneKeys t N)
    (h : ∀ o,P o → Q o) : 0≤keyWeight w t z pin K P m s o k ∧
      keyWeight w t z pin K P m s o k≤keyWeight w t z pin K Q m s o k := by
  have hn : ∀ x,0≤(w.pen t).state z n x :=
    prodW_nonneg fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _)
  have hr := pr_nonneg (p:=fun x=>oneVolleyKeys ((w.pen t).draw x) t o=k) hn
  exact ⟨mul_nonneg hr (ind_nonneg _),
    mul_le_mul_of_nonneg_left (ind_mono fun hx=>⟨h o hx.1,hx.2⟩) hr⟩
/-- A positive atom of the input law conditioned on the diagonal bits
weighs at least as much as an unconditioned uniform input. -/
theorem state_atom_lower {I : Type} [Fintype I] [DecidableEq I] (v : Template p I)
    (z : I → F) (x : Inputs p n I) (hx : v.state z n x ≠ 0) :
    (Fintype.card (Inputs p n I) : ℝ)⁻¹ ≤ v.state z n x := by
  classical
  rw [←unif_apply x,draws_unif]
  change (∏ i, unif (x i)) ≤ ∏ i, scopedBit p n (v.t i) (v.f i) (z i) (x i)
  apply prod_le_prod (fun i _ => (unif_law (α := Knobs p.g n)).nz (x i))
  intro i _
  have hne := (prod_ne_zero_iff.mp hx) i (mem_univ i)
  change scopedBit p n (v.t i) (v.f i) (z i) (x i) ≠ 0 at hne
  let D := fun y : Knobs p.g n => dialed p (v.t i) (v.f i) y = z i
  have hD : D (x i) := (onW_ne hne).1
  have hspin : spins p n = unif := by unfold spins; rw [←draws_unif]
  have hpos : 0 < spins p n (x i) := by rw [hspin,unif_apply]; positivity
  have hm := weight_le_pr (spins_law p n).nz hD
  change unif (x i) ≤ onW (spins p n) D (x i)
  rw [←hspin,onW_val,ind_one hD,mul_one]
  exact (le_div_iff₀ (hpos.trans_le hm)).mpr
    (mul_le_of_le_one_right hpos.le ((pr_le_tot (spins_law p n).nz).trans_eq (spins_law p n).total))

/-- A retained orientation can reach a set if an input with positive sampling
weight passes every test and has its complete key in the set. -/
def reachesKeySet (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (P : OneUnit p n N → Prop)
    (m : Mixer p n) (s : Charts p n d) (C : OneKeys t N → Prop) (o : OneUnit p n N) : Prop :=
  ∃ x, (w.pen t).state z n x ≠ 0 ∧ C (oneVolleyKeys ((w.pen t).draw x) t o) ∧
    OneProtectedInput (w.pen t) pin K x ∧ P o ∧ oneDeposit w t z m o s x

theorem reaches_key_set_mass (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (μ : Wgt (OneUnit p n N))
    (P : OneUnit p n N → Prop) (m : Mixer p n) (s : Charts p n d) (C : OneKeys t N → Prop)
    (hμ : ∀ o, 0 ≤ μ o) :
    (Fintype.card (Inputs p n (Messenger q)) : ℝ)⁻¹ *
      pr μ (reachesKeySet w t z pin K P m s C) ≤ pr (oneGoodHistogram w t z pin K μ P m s) C := by
  unfold oneGoodHistogram oneHistogram pr
  rw [← avg_mul',input_histogram_mean,avg_avg]
  apply avg_mono hμ
  intro o
  let ρ := (w.pen t).state z n
  have hρ : ∀ x, 0 ≤ ρ x := prodW_nonneg fun _ => normW_nonneg (subW_nonneg (spins_law ..).nz _)
  simp only [←ind_and]
  by_cases h : reachesKeySet w t z pin K P m s C o
  · rw [ind_one h,mul_one]
    obtain ⟨x,hx,hC,haccept⟩ := h
    exact (state_atom_lower (w.pen t) z x hx).trans (weight_le_pr hρ ⟨hC,haccept⟩)
  rw [ind_zero h,mul_zero]
  exact pr_nonneg hρ

end OneQuill

namespace OneStation
variable {p:Shape} {n N K:ℕ} {q:Format} {d e:Rates} {pop:OneLeafMixture p n N}
    (v:OneStation p n N K pop)

theorem natural_match_score (x:Typus p q d e) (m:Mixer p n) (μ:Wgt (OneUnit p n N))
    (i j:pop.T) (k:Fin (2^oneDeckMax p K)):
    overlap (oneLawNu p N x.t x.z)
      (OneQuill.oneGoodHistogram x.qA x.t x.z (pop.pin i.val).sp K
        (partW μ i.val) (v.frontPage x m i j k) m (v.cAxes i d))
      (OneQuill.oneGoodHistogram x.qB x.t x.z (pop.pin j.val).sp K
        (partW μ j.val) (v.backPage x m i j k) m (v.cAxes j e))=
      v.matchScore x m μ i j k := by
  unfold matchScore leftSales rightSales OneQuill.oneGoodSales
  have href : mapW (oneLawNu p N x.t x.z) (oneQueryCoordinateEquiv x.t N).symm=
      unifOn (oneOwnPart (N:=N) x.t x.z):=
    (one_reference_coordinates x.t x.z).trans (uniform_weights_instances _ _ _)
  rw [←href,overlap_map_equiv]

/-- This identity includes every position, the protected rejection and the
prescribed binary tests. The two orientation filters can depend on both leaves. -/
theorem full_key_overlap (x : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (i j : pop.T) (P Q : OneUnit p n N→Prop) (hg : 2≤p.g)
    (hP : ∀ o,P o → ∀ a,oneFrameLaw m (o a)) (hQ : ∀ o,Q o → ∀ a,oneFrameLaw m (o a)) :
    overlap (oneLawNu p N x.t x.z)
      (OneQuill.oneGoodHistogram x.qA x.t x.z (pop.pin i.val).sp K (partW μ i.val) P m (v.cAxes i d))
      (OneQuill.oneGoodHistogram x.qB x.t x.z (pop.pin j.val).sp K (partW μ j.val) Q m (v.cAxes j e))=
    avg (pairW (partW μ i.val) (partW μ j.val)) (fun o=>overlap (oneLawNu p N x.t x.z)
      (OneQuill.keyWeight x.qA x.t x.z (pop.pin i.val).sp K P m (v.cAxes i d) o.1)
      (OneQuill.keyWeight x.qB x.t x.z (pop.pin j.val).sp K Q m (v.cAxes j e) o.2)) := by
  rw [←overlap_of_mixtures]
  exact congrArg₂ (overlap _) (funext (OneQuill.good_histogram_eq_feasible x.qA x.t x.z _ K _ P m _ hg hP))
    (funext (OneQuill.good_histogram_eq_feasible x.qB x.t x.z _ K _ Q m _ hg hQ))

theorem filtered_match_le (x : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (i j : pop.T) (k : Fin (2^oneDeckMax p K)) (hg : 2≤p.g)
    (hμ : ∀ o,0≤μ o) {P Q : OneUnit p n N→Prop}
    (hP : ∀ o,P o → v.frontPage x m i j k o) (hQ : ∀ o,Q o → v.backPage x m i j k o) :
    overlap (oneLawNu p N x.t x.z)
      (OneQuill.oneGoodHistogram x.qA x.t x.z (pop.pin i.val).sp K (partW μ i.val) P m (v.cAxes i d))
      (OneQuill.oneGoodHistogram x.qB x.t x.z (pop.pin j.val).sp K (partW μ j.val) Q m (v.cAxes j e))≤
    v.matchScore x m μ i j k := by
  rw [←v.natural_match_score x m μ i j k,v.full_key_overlap x m μ i j P Q hg
    (fun o h=>(hP o h).2.2.1) (fun o h=>(hQ o h).2.2.1),
    v.full_key_overlap x m μ i j _ _ hg (fun _ h=>h.2.2.1) (fun _ h=>h.2.2.1)]
  apply avg_mono (w:=pairW (partW μ i.val) (partW μ j.val))
  · intro o
    exact mul_nonneg (normW_nonneg (subW_nonneg hμ _) _) (normW_nonneg (subW_nonneg hμ _) _)
  intro o
  have ha k:=OneQuill.key_weight_mono x.qA x.t x.z (pop.pin i.val).sp K m (v.cAxes i d) o.1 k hP
  have hb k:=OneQuill.key_weight_mono x.qB x.t x.z (pop.pin j.val).sp K m (v.cAxes j e) o.2 k hQ
  exact overlap_mono_nonnegative _ _ _ _ _ (unifOn_sub _).nz
    (fun k=>(ha k).1) (fun k=>(hb k).1) (fun k=>(ha k).2) (fun k=>(hb k).2)

/-- For a pair of leaves, a cut of the complete keys separates the accepted
orientations. The cost is charged to the actual score of the numerical option.
Both filters may be chosen after the leaf pair is known. -/
theorem exists_full_key_cut (x : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (i j : pop.T) (k : Fin (2^oneDeckMax p K)) (hg : 2 ≤ p.g) (hμ : ∀ o, 0 ≤ μ o)
    {P Q : OneUnit p n N → Prop} (hP : ∀ o, P o → v.frontPage x m i j k o)
    (hQ : ∀ o, Q o → v.backPage x m i j k o) :
    ∃ C : OneKeys x.t N → Prop,
      (((Fintype.card (Inputs p n (Messenger q)) : ℝ)⁻¹) *
        (pr (partW μ i.val) (OneQuill.reachesKeySet x.qA x.t x.z (pop.pin i.val).sp K
          P m (v.cAxes i d) C) +
         pr (partW μ j.val) (OneQuill.reachesKeySet x.qB x.t x.z (pop.pin j.val).sp K
          Q m (v.cAxes j e) (fun y => ¬ C y))))^2 ≤ v.matchScore x m μ i j k := by
  classical
  let ν := oneLawNu p N x.t x.z
  let A := OneQuill.oneGoodHistogram x.qA x.t x.z (pop.pin i.val).sp K (partW μ i.val) P m (v.cAxes i d)
  let B := OneQuill.oneGoodHistogram x.qB x.t x.z (pop.pin j.val).sp K (partW μ j.val) Q m (v.cAxes j e)
  let C := fun y => A y ≤ B y
  have hn (a : pop.T) : ∀ o, 0 ≤ partW μ a.val o := normW_nonneg (subW_nonneg hμ _)
  have hA := OneQuill.one_good_natural_nonneg x.qA x.t x.z (pop.pin i.val).sp K _ P m (v.cAxes i d) (hn i)
  have hB := OneQuill.one_good_natural_nonneg x.qB x.t x.z (pop.pin j.val).sp K _ Q m (v.cAxes j e) (hn j)
  have hs (y) (hy : ν y = 0) : A y = 0 := by
    apply OneQuill.one_good_natural_carried
    intro h
    have hp := weight_le_tot (fun y => ind_nonneg (oneOwnKeyPart x.t x.z y)) y
    rw [ind_one h] at hp
    have hpos : 0 < nbr (oneOwnKeyPart (N:=N) x.t x.z) := lt_of_lt_of_le zero_lt_one hp
    change unifOn _ _ = 0 at hy
    rw [unifOn_val,ind_one h] at hy
    exact (div_pos zero_lt_one hpos).ne' hy
  have hcut := key_cut_sq_le_overlap ν A B (unifOn_sub _) hA hB hs
  have ha := OneQuill.reaches_key_set_mass x.qA x.t x.z (pop.pin i.val).sp K _ P m (v.cAxes i d) C (hn i)
  have hb := OneQuill.reaches_key_set_mass x.qB x.t x.z (pop.pin j.val).sp K _ Q m (v.cAxes j e)
    (fun y => ¬ C y) (hn j)
  refine ⟨C, le_trans ?_ (hcut.trans (v.filtered_match_le x m μ i j k hg hμ hP hQ))⟩
  apply pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (add_nonneg
    (pr_nonneg (hn i)) (pr_nonneg (hn j))))
  rw [mul_add]
  exact add_le_add ha hb

/-- Average over two independently drawn leaves. Each pair gets its own cut
and both orientation filters. No bound on an individual leaf marginal is used. -/
theorem full_key_cuts_of_collision (x : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (k : Fin (2^oneDeckMax p K)) {A ζ : ℝ} (hg : 2 ≤ p.g)
    (hp : oneLeafStrength pop μ m A ζ K) (hw : IsLaw μ) (hm : 0 < pop.amount μ)
    (he : OneEarnsScore p n N K ζ)
    (P Q : pop.T × pop.T → OneUnit p n N → Prop)
    (hP : ∀ ij o, P ij o → v.frontPage x m ij.1 ij.2 k o)
    (hQ : ∀ ij o, Q ij o → v.backPage x m ij.1 ij.2 k o) :
    ∃ cut : pop.T × pop.T → OneKeys x.t N → Prop,
      let u := portionW μ pop.T
      let t := (Fintype.card (Inputs p n (Messenger q)) : ℝ)⁻¹
      avg (pairW u u) (fun ij => (t *
        (pr (partW μ ij.1.val) (OneQuill.reachesKeySet x.qA x.t x.z (pop.pin ij.1.val).sp K
          (P ij) m (v.cAxes ij.1 d) (cut ij)) +
         pr (partW μ ij.2.val) (OneQuill.reachesKeySet x.qB x.t x.z (pop.pin ij.2.val).sp K
          (Q ij) m (v.cAxes ij.2 e) (fun y => ¬ cut ij y))))^2) ≤
        oneBeamPrice p N * pr (pairW (pop.sap μ) (pop.sap μ)) (oneClash m) +
          2 * bp (-0.005 * (2*N)) := by
  classical
  choose cut hcut using fun ij : pop.T × pop.T =>
    v.exists_full_key_cut x m μ ij.1 ij.2 k hg hw.nz (hP ij) (hQ ij)
  have hu := (rebuild hw.nz hp.part (fun i hi => (hp.leaf i hi).pos) hm).1
  exact ⟨cut, (avg_mono (pairW_law hu hu).nz hcut).trans (v.arena_bound x m μ k hp hw hm he)⟩

end OneStation
end
end Lax793645Proofs.Simplifications
