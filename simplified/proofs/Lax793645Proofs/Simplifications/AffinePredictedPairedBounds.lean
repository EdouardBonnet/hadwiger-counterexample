/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.PairedEventBounds.
This variant uses base-query hits and uniform prediction errors on a retained cell.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Simplifications.AffinePredictedEvents
import Lax793645Proofs.Simplifications.ExactBaseQueryHits
import Lax793645Proofs.Simplifications.LinearSuperlevels
import Lax793645Proofs.Simplifications.ProductQueryCells
import Lax793645Proofs.Simplifications.LightQueryBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample

/-! # Paired Event Bounds -/

noncomputable section
open Filter Finset Matrix
open scoped BigOperators Topology
open Template
namespace AffineOptions
open StatusAnalysis
open Station PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {p:Shape} {M r:ℕ} {m:cycleM p} {s:rhythms p M} {w:tale p M}
    {q:Format} {d e:Rates}

private theorem thick_roster {A:Type} [Fintype A] {P : Wgt A→Prop} {r:ℕ} {ε:ℝ}
    (h:roster P r ε) :
    ∃ f:Fin r→Wgt A,∀ y,P y→∃ i,varOne y (f i)≤ε := by
  classical
  obtain ⟨d,hd,g,hg⟩:=h
  let f(k:Fin r) := if h:k.val<d then g ⟨k.val,h⟩ else 0
  refine ⟨f,fun x h=>?_⟩; obtain ⟨j,hj⟩:=hg x h
  refine ⟨Fin.castLE hd j,?_⟩; unfold f; simpa using hj

set_option maxHeartbeats 2000000 in
theorem predicted_dimBerth (t: Stations p M b.pins s)
    (h:AffineVeil p M b r l m s w)
    (x:Typus p q d e) (k:Fin (2^deckMax p b.pins)) {β:ℝ} (hβ:0<β)
    (α : Party) (g : ∀ n, Bool → Augur p (M*n)) (ε : ℕ → ℝ)
    (heps : Tendsto ε l (𝓝 0)) (E : ∀ n, Keys (p:=p) x.t (M*n) → Prop)
    {e0 : ℝ} (he0 : 0 < e0)
    (hE : ∀ᶠ n in l, e0 ≤ pr (lawNu p (M*n) x.t x.z) (E n))
    (hEdesign : ∀ n,design (x.qB.pen x.t) (fun k=>ind (E n k)) 1 1) :
    ExpSmall l (fun n=>(n:ℝ)) (fun n=>predictedBerth (t n) x (m n) k (w n) β α (g n) (ε n) (E n)) := by
  classical
  by_cases hX:x.permission
  · let K:=b.pins; let N:=fun n:ℕ=>M*n
    have hq:=h.easel; have hp:= hq.enter.first
    have ha:=hX.2.1; have hb:= hX.2.2.1

    obtain ⟨y2,c2,hy2,hc2,hB⟩:= exact_base_sober_calendar x.qB x.t x.z hq.toQueryParameters hb 1 e0 he0
    let y := y2/4
    have hy : 0 < y := by unfold y; positivity

    let a:=β*y/6; have hα:0<a:=by unfold a; positivity
    obtain ⟨δ,_,hd,_,hW⟩:= affine_light_certificate x.qB x.t x.z M hp.hM hp.hR b.leafNew (by unfold leafNew leafOld; positivity) hb a hα

    let Y2:=x.qA.dilate x.t K*(δ/4)
    have hY2 : 0<Y2:=mul_pos (x.qA.dilate_pos x.t K) (by positivity)
    let Y := Y2/4
    have hY : 0 < Y := by unfold Y; positivity
    let b0:=β*Y/4; have h0:0<b0:=by unfold b0; positivity

    obtain ⟨δ',_,he,_,hF⟩:=affine_light_certificate x.qA x.t x.z M hp.hM hp.hR b.leafNew (by unfold leafNew leafOld; positivity) ha b0 h0

    let ξ:=min a (a*δ')
    have hh:0<ξ:=lt_min hα (by positivity)
    obtain ⟨_,_,hlinear⟩:=successful_product_partition x.qB x.t x.z hb hp.hR M hp.hM b.leafNew
    obtain ⟨r0,paints,hQ⟩:=hlinear (ξ/2) (half_pos hh)
    let count:=Fintype.card (Fin r0→Bool)
    obtain ⟨c,hc,hA⟩:=exact_base_sober_gain x.qA x.t x.z hq.toQueryParameters ha paints δ hd
    let b1:=fun n:ℕ=>bp (-c*n); let b2:=fun n:ℕ=>bp (-c2*n)

    obtain ⟨f,hf,hξ⟩ := h.score_cost t
    let e_ (n:ℕ):=(num (Fin count)*(b1 n/β)+b2 n/β)
    let D : ℕ→ℝ:=fun n=> e_ n+|f n|/(a*b0)
    have ht:= (trend_sizes l h.timeL hp.hM).2
    have hz : Tendsto (fun n:ℕ=>(n:ℝ)) l atTop := tendsto_natCast_atTop_atTop.mono_left h.timeL
    have hD : ExpSmall l (fun n:ℕ=>(n:ℝ)) D := by
      have h1 := ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc
      have h2:=ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc2
      have hg : ExpSmall l (fun n:ℕ=>(n:ℝ)) e_ := by
        have hi := (h1.mul (expO_const hz (num (Fin count)/β))).add hz (h2.mul (expO_const hz β⁻¹))
        refine hi.mono (.of_forall (fun i=>?_))
        exact le_of_eq (congrArg abs (by unfold e_ b1 b2; ring))
      obtain ⟨C,hC,hf⟩:= hf
      have h : ExpSmall l (fun n:ℕ=>(n:ℝ)) (fun n=>|f n|) := by
        refine ⟨C*M, by have hm:=hp.hM; positivity,?_⟩
        filter_upwards [hf] with n hn
        rw [abs_abs]; push_cast at hn; rwa [←mul_assoc,neg_mul] at hn
      simpa [D,div_eq_mul_inv] using hg.add hz (h.mul (expO_const hz (a*b0)⁻¹))
    refine hD.mono ?_
    have hsmall : ∀ᶠ n in l,
        Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε n) ≤ min y Y := by
      have hlim := (heps.const_mul ((scanPrice p)⁻¹)).const_mul (Fintype.card (Messenger q):ℝ)
      simpa only [mul_zero] using hlim.eventually (eventually_le_nhds
        (by simpa only [mul_zero] using lt_min hy hY))
    have hreject : ∀ᶠ n : ℕ in l,
        bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) ≤ β*min y Y := by
      apply ((affine_rejection_vanish p K (Fintype.card (Messenger q))).eventually
        (eventually_le_nhds (mul_pos hβ (lt_min hy hY)))).filter_mono h.timeL
    have hrejectnet : ∀ᶠ n : ℕ in l,
        bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) ≤ ξ/2 := by
      exact ((affine_rejection_vanish p K (Fintype.card (Messenger q))).eventually
        (eventually_le_nhds (half_pos hh))).filter_mono h.timeL
    have hl := h.timeL
    filter_upwards [h.upright,h.durableS.shape,h.moment,h.durableS.mass.positive,
       hF.filter_mono hl,hQ.filter_mono hl,hW.filter_mono hl,hB.filter_mono hl,hA.filter_mono hl,hξ,
       ht.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1)),hsmall,hE,hreject,hrejectnet]
       with n hn hr ht hx hf hg hh hB hA hξ hN hsmall hE hreject hrejectnet
    let W:=w n; let s':=s n; let I:=s'.T; let V (i:↑I):=partW W i.val
    let u:=portionW W I; let R:=pairW u u; let G:=t n; let m':=m n
    let ν:= lawNu p (N n) x.t x.z; have hm:=ht.1.law
    let P := s'.sap W
    have hν:IsLaw ν:=nuLaw _ _ (show 2*num (Messenger q×Toast p)-((M*n:ℕ):ℝ)≤ -1 from
      by change _ ≤((M*n:ℕ):ℝ) at hN; linarith only [hN])
    let A i:= custom x.qA (V i) (G.cAxes i d) x.t x.z m' (s'.pin i.val) K

    let B i:= custom x.qB (V i) (G.cAxes i e) x.t x.z m' (s'.pin i.val) K
    let J := predictedCharter G x m' k W β α (g n) (ε n) (E n)
    choose PA PB hselect using fun i : ↑I×↑I => show ∃ PA PB,
        (∀ o, PA o → frontPage G x m' i.1 i.2 k o) ∧
        (∀ o, PB o → backPage G x m' i.1 i.2 k o) ∧
        (J i → x.qA.predictedQualified x.t x.z (G.cAxes i.1 d) m' K (V i.1) PA β α (g n) (ε n) (E n) ∧
          x.qB.predictedQualified x.t x.z (G.cAxes i.2 e) m' K (V i.2) PB β α (g n) (ε n) (E n)) from by
      by_cases hj : J i
      · obtain ⟨_,PA,PB,hPA,hPB,hQA,hQB⟩ := hj
        exact ⟨PA,PB,hPA,hPB,fun _ => ⟨hQA,hQB⟩⟩
      · exact ⟨fun _ => False,fun _ => False,fun _ h => h.elim,fun _ h => h.elim,fun h => (hj h).elim⟩
    let X (i:↑I×↑I) := sales x.qA x.t x.z (s'.pin i.1.val) K (V i.1) (PA i) m' (G.cAxes i.1 d)
    let Z (i:↑I×↑I) := sales x.qB x.t x.z (s'.pin i.2.val) K (V i.2) (PB i) m' (G.cAxes i.2 e)
    have huv := hr.1
    have hV i : IsLaw (V i):=on_law hm.nz (huv.leaf i.val i.property).pos
    have hC (i:↑I) := (huv.leaf (Subtype.val i) i.property).density
    choose Cpart hCpart using fun i : ↑I=>hg m' hn.cols (V i) (hV i) (hC i) (G.cAxes i e)
    obtain ⟨hu,hO⟩:=rebuild hm.nz huv.part (fun i hi=>(huv.leaf _ hi).pos) hx
    have ho : P=mixW u V:= hO
    let cellWords:=Fintype.equivFin (Fin r0→Bool)
    let S (i : ↑I) (j : Fin count) := fun k => E n k ∧ cellWords.symm j (Cpart i k)=true
    have hSdesign (i : ↑I) (j : Fin count) :
        design (x.qA.pen x.t) (fun k=>ind (S i j k)) 1 paints := by
      have hpB:=(hCpart i).1 (fun v=>cellWords.symm j v=true)
      have hpA:=quill_design_transfer x.qB x.qA x.t _ paints hpB
      have hpE:=quill_design_transfer x.qB x.qA x.t _ 1 (hEdesign n)
      have hh:=design_mul_one (x.qA.pen x.t) _ _ paints hpA hpE
      simpa only [S,ind_and,mul_comm] using hh
    let T : UnitType p n (N n)→Prop:= fun i=>¬x.qB.baseSober x.t x.z K (E n) m' y2 i
    let U i j o:= δ ≤ pr ν (S i j) ∧ ¬x.qA.baseSober x.t x.z K (S i j) m' Y2 o
    let O (i:↑I×↑I) := (∃ j, β < pr (V i.1) (U i.2 j)) ∨ β < pr (V i.2) T
    have hT : pr R O ≤ e_ n := by
      refine vacantBound u V U T hu hV hβ (fun i j=>?_) ?_
      · by_cases h:δ ≤ pr ν (S i j)
        · simp_rw [U,h,true_and,← ho]; exact hA m' P hn (S i j) (hSdesign i j) h
        have hf : U i j = (fun _=>False) := funext fun i=> eq_false (fun hh=> h hh.1)
        rw [hf,pr_false]; exact (bp_pos _).le
      rw [← ho]
      exact hB m' P hn (E n) (hEdesign n) hE
    let L i := overlap ν (X i) (Z i)
    have hL0 i: IsLaw (x.qA.policies x.t x.z n i):= Appearance.witLaw
       (x.qA.allure_apt x.t x.z ha _) hp.hR hn.age
    have hL1 i:IsLaw (x.qB.policies x.t x.z n i):= Appearance.witLaw
       (x.qB.allure_apt x.t x.z hb _) hp.hR hn.age
    have hX (i:↑I×↑I):A i.1 (X i):= sales_custom x.qA _ _ _ _ _ _ _ _
    have hZ (i:↑I×↑I):B i.2 (Z i):= sales_custom x.qB _ _ _ _ _ _ _ _
    have heq (i) (hj:J i) (hk:¬O i) : a*b0≤ L i := by
      have hpos : 0 < pr (V i.1) (PA i) :=
        (show 0 < 2*β by positivity).trans_le (((hselect i).2.2 hj).1.1)
      obtain ⟨o,ho,_⟩ := exists_of_pr_pos (hV i.1).nz hpos
      have hnews : news G x i.1 i.2 k := ((hselect i).1 o ho).1
      have hpenA := hnews.2.1.2.1
      have hpenB := hnews.2.2.2.1
      let Z0:=x.qB.sales x.t x.z (V i.2) (PB i) m' (G.cAxes i.2 e)
      let d0:=density ν Z0
      let g0:=banner ν (Cpart i.2) d0
      let f0:=fun k=>ν k*g0 k
      let words : Fin r0→Bool:=fun k=>decide (2*a≤cashbook ν (Cpart i.2) d0 k)
      let j : Fin count:=cellWords words
      have hS : S i.2 j=fun k=>E n k ∧ 2*a≤g0 k := by
        funext k
        change (E n k ∧ cellWords.symm (cellWords words) (Cpart i.2 k)=true)=_
        rw [Equiv.symm_apply_apply]
        change (E n k ∧ decide (2*a≤cashbook ν (Cpart i.2) d0 (Cpart i.2 k))=true)=
          (E n k ∧ 2*a≤cashbook ν (Cpart i.2) d0 (Cpart i.2 k))
        simp only [decide_eq_true_eq]
      have hsupp0 : lsupp Z0 ν := by
        intro k hk
        have he:=density_hung (ownPart x.t x.z) Z0
          (x.qB.sales_part (V i.2) (G.cAxes i.2 e) x.t x.z m' (PB i)) k
        exact left_ne_zero_of_mul (he.symm ▸ hk)
      have happrox0 : varOne Z0 f0≤ξ/2 := by
        rw [var_one_density_reconstruction ν Z0 g0 hν.nz hsupp0]
        exact ((hCpart i.2).2 (PB i)).2
      have hrj : varOne (Z i) Z0≤ξ/2 := by
        rw [show varOne (Z i) Z0=varOne Z0 (Z i) from by
          unfold varOne
          apply Finset.sum_congr rfl
          intro k _
          exact abs_sub_comm _ _]
        exact (affine_sales_rejection_of_filter x.qB x.t x.z (s'.pin i.2.val) K
          (V i.2) (PB i) m' (G.cAxes i.2 e) (hV _).sub hb hp.hR hn.age
          (fun o ho=>((hselect i).2.1 o ho).1.2.2.2.1)).2.trans hrejectnet
      have hj' : varOne (Z i) f0≤ξ :=
        (var_tri (Z i) f0 Z0).trans ((add_le_add hrj happrox0).trans_eq (by ring))
      obtain ⟨hP,hX',_⟩:=hf m' (G.cAxes i.1 _) (V i.1) (s'.pin i.1.val) K hn.cols (hV _) (hC _)
      obtain ⟨hR',hY',_⟩:=hh m' (G.cAxes i.2 _) (V i.2) (s'.pin i.2.val) K hn.cols (hV _) (hC _)
      let F:=S i.2 j
      have hFt : δ≤ pr ν F := by
        have hi := predicted_qualify_hit x.qB x.t x.z (G.cAxes i.2 e) m' K (s'.pin i.2.val) (V i.2) (PB i)
          α (g n) (ε n) (E n) (E n) (fun _ h => h) hy ((hselect i).2.2 hj).2
          (hV _) hb hp.hR hn.age hpenB (hsmall.trans (min_le_left ..))
          (hreject.trans (mul_le_mul_of_nonneg_left (min_le_left ..) hβ.le))
          (by simpa only [y, mul_div_cancel₀ _ (by norm_num : (4:ℝ) ≠ 0)] using
            (le_of_not_gt (mt Or.inr hk)))
        change β*y ≤ pr (Z i) (E n) at hi
        have hset : pr ν (S i.2 j)=pr ν (fun k=>E n k ∧ cliff ν f0 a k) := by
          rw [hS]
          exact projected_superlevel_pr ν ν hν.nz (fun _ h=>h) (Cpart i.2)
            (cashbook ν (Cpart i.2) d0) (E n) a
        change δ≤pr ν (S i.2 j)
        rw [hset]
        exact (Lax793645Proofs.Simplifications.cliff_thick_on (B i.2) _ f0 ν (E n)
          hν (hR' _ (hZ i)).1.nz (hZ i) a δ hα hY' (hj'.trans (min_le_left ..))
          (show 5*a ≤ pr (Z i) (E n) from by unfold a; nlinarith only [hi,hβ,hy])).le
      have hbad : pr (V i.1) (fun o => ¬x.qA.baseSober x.t x.z K F m' Y2 o) ≤ β := by
        apply le_of_not_gt
        intro hbad
        apply hk
        refine Or.inl ⟨j,?_⟩
        have heq : U i.2 j = fun o => ¬x.qA.baseSober x.t x.z K F m' Y2 o :=
          funext fun o => propext ⟨And.right,fun h => ⟨hFt,h⟩⟩
        rw [heq]
        exact hbad
      have hM : β*Y ≤ pr (X i) F :=
        predicted_qualify_hit x.qA x.t x.z (G.cAxes i.1 d) m' K (s'.pin i.1.val) (V i.1) (PA i)
          α (g n) (ε n) (E n) F (fun _ h => h.1) hY ((hselect i).2.2 hj).1
          (hV _) ha hp.hR hn.age hpenA (hsmall.trans (min_le_right ..))
          (hreject.trans (mul_le_mul_of_nonneg_left (min_le_right ..) hβ.le))
          (by simpa only [Y, mul_div_cancel₀ _ (by norm_num : (4:ℝ) ≠ 0)] using hbad)
      obtain ⟨hx,hz⟩:= hP _ (hX i)
      refine Lax793645Proofs.Simplifications.cliff_score_on _ (X i) (Z i) f0 ν (E n)
        hx (hR' _ (hZ i)).1 hν hz b0 a ξ hα (hX i) hj'
        (fun z hz S hS => hX' z hz S (hS.trans ?_)) ?_
      · exact (div_le_iff₀ hα).mpr ((min_le_right ..).trans_eq (mul_comm ..))
      have hset : pr (X i) (S i.2 j)=pr (X i) (fun k=>E n k ∧ cliff ν f0 a k) := by
        rw [hS]
        exact projected_superlevel_pr (X i) ν hν.nz hz (Cpart i.2)
          (cashbook ν (Cpart i.2) d0) (E n) a
      exact (show 2*b0 ≤ pr (X i) F from by
        unfold b0
        nlinarith only [hM,hβ,hY]).trans_eq hset
    have hn0 (i:↑I×↑I) : 0 ≤ L i := by
      have h1 i j : 0≤X i j := sales_pos x.qA _ _ _ _ m' _ _ _ (hV _).nz j
      have h2 i j : 0 ≤ Z i j:= sales_pos x.qB _ _ _ _ m' _ _ _ (hV _).nz j
      refine avg_nonneg hν.nz fun j=>mul_nonneg (div_nonneg (h1 i j) (hν.nz _))
        (div_nonneg (h2 i j) (hν.nz _))
    have hv := pairW_law hu hu
    have hscore : avg R L ≤ arena G x m' W k := by
      apply avg_mono hv.nz
      intro i
      exact overlap_mono_nonnegative ν (X i) (Z i)
        (leftSales G x m' W i.1 i.2 k) (rightSales G x m' W i.1 i.2 k) hν.nz
        (sales_pos x.qA _ _ _ _ _ _ _ _ (hV _).nz) (sales_pos x.qB _ _ _ _ _ _ _ _ (hV _).nz)
        (sales_mono_filter x.qA _ _ _ _ _ _ _ _ _ (hV _).nz (hselect i).1)
        (sales_mono_filter x.qB _ _ _ _ _ _ _ _ _ (hV _).nz (hselect i).2.1)
    have hi := le_avg_markov hv.nz hn0 (a*b0)
    change |pr R J| ≤ _
    rw [abs_of_nonneg (pr_nonneg hv.nz)]
    apply le_trans _ (le_abs_self (D n))

    have hg (i) (h:J i): O i ∨ a*b0 ≤ L i := by
      by_cases hi:O i
      · exact Or.inl hi
      exact Or.inr (heq i h hi)
    refine ((pr_mono hv.nz hg).trans (pr_or_le hv.nz)).trans (add_le_add hT ?_)
    refine (le_div_iff₀ (by positivity)).mpr (le_trans ?_ (hscore.trans ((le_abs_self _).trans
      ((hξ q d _ x k).trans (le_abs_self _)))))
    rw [mul_comm]; exact hi
  · refine (ExpSmall.zero l (fun n=>(n:ℝ))).mono (.of_forall (fun n=>?_))
    have hh i : ¬predictedCharter (t n) x (m n) k (w n) β α (g n) (ε n) (E n) i :=fun he=>hX he.1
    unfold predictedBerth pr
    simp only [ind_zero (hh _),avg_const,mul_zero,le_refl]
end AffineOptions

end

end Lax793645Proofs.Simplifications
