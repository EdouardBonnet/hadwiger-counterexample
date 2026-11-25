import Lax793645Proofs.Simplifications.OneRareQueryAdapters
import Lax793645Proofs.Simplifications.OneQueryAlignment
import Lax793645Proofs.Simplifications.OneSuccessfulProductPartitions
import Lax793645Proofs.Simplifications.FiniteCellOverlap
import Lax793645Proofs.Simplifications.LinearSuperlevels
import Lax793645Proofs.Simplifications.ProjectionRefinementBounds
import Lax793645Proofs.Simplifications.PredictedRareEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function PreparationParameters
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneStation
variable {l:Filter ℕ} {b:PreparationParameters} {p:Shape} {M r:ℕ}
    {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M} {q:Format} {d e:Rates}

set_option maxHeartbeats 2000000 in
theorem one_predicted_dim_berth (t: OneStations p M (onePreparationPins b) s)
    (h:OneVeil p M b r l m s w)
    (x:Typus p q d e) (k:Fin (2^oneDeckMax p (onePreparationPins b))) {β:ℝ} (hβ:0<β)
    (α : Party) (g : ∀ n, Bool → OneAugur p (M*n)) (ε : ℕ → ℝ)
    (heps : Tendsto ε l (𝓝 0)) (E : ∀ n, OneKeys x.t (M*n) → Prop)
    {e0 : ℝ} (he0 : 0 < e0)
    (hE : ∀ᶠ n in l, e0 ≤ pr (oneLawNu p (M*n) x.t x.z) (E n))
    (hEdesign : ∀ n,OneDesign x.t (fun k=>ind (E n k)) 1) :
    ExpSmall l (fun n=>(n:ℝ)) (fun n=>predictedBerth (t n) x (m n) k (w n) β α (g n) (ε n) (E n)) := by
  classical
  by_cases hX:(onePermission x)
  · let K:=(onePreparationPins b); let N:=fun n:ℕ=>M*n
    have hq:=h.parameters; have hp:= hq.unary
    have ha:=hX.2.1; have hb:= hX.2.2.1

    obtain ⟨c2,hc2,hB⟩:=OneQuill.one_aligned_base_hit x.qB x.t x.z hb hq 1 e0 he0
    let y2:=OneQuill.oneDilate x.qB x.t K*(e0/4)
    have hy2:0<y2:=mul_pos (OneQuill.one_dilate_pos ..) (by positivity)
    let y := y2/4
    have hy : 0 < y := by unfold y; positivity

    let b0:=β*y
    have h0:0<b0:=mul_pos hβ hy
    let κ:=β*OneQuill.oneDilate x.qA x.t K/16
    have hκ:0<κ:=div_pos (mul_pos hβ (OneQuill.one_dilate_pos ..)) (by norm_num)
    obtain ⟨B,hBbound,hlinear⟩:=one_successful_product_partition x.qB x.t x.z hb hp.hR M hp.hM (2*b.leafNew)
    have hBpos:0<B:=lt_of_lt_of_le zero_lt_one hBbound
    let η:=κ*b0/(8*B)
    have hη:0<η:=by dsimp only [η]; positivity
    obtain ⟨_,Tclip,_,hclip,hF⟩:=one_light_certificate x.qA x.t x.z M hp.hM hp.hR (2*b.leafNew)
      (by unfold leafNew leafOld; positivity) ha η hη
    let ξ:=κ*b0/(8*(κ+Tclip+1))
    have hh:0<ξ:=by dsimp only [ξ]; positivity
    obtain ⟨r0,paints,hQ⟩:=hlinear (ξ/2) (half_pos hh)
    let δ:=b0/(8*B*(r0+1:ℝ))
    have hd:0<δ:=by dsimp only [δ]; positivity
    let Y:=OneQuill.oneDilate x.qA x.t K*(δ/16)
    have hY:0<Y:=mul_pos (OneQuill.one_dilate_pos ..) (by positivity)
    let score:=κ*b0/2
    have hscorepos:0<score:=by dsimp only [score]; positivity
    obtain ⟨c,hc,hA⟩:=OneQuill.one_aligned_relative_hit x.qA x.t x.z ha hq paints δ hd
    let b1:=fun n:ℕ=>bp (-c*n); let b2:=fun n:ℕ=>bp (-c2*n)

    obtain ⟨f,hf,hξ⟩ := h.score_cost t
    let e_ (n:ℕ):=(num (Fin r0)*(b1 n/β)+b2 n/β)
    let D : ℕ→ℝ:=fun n=> e_ n+|f n|/score
    have ht:= (trend_sizes l h.time hp.hM).2
    have hz : Tendsto (fun n:ℕ=>(n:ℝ)) l atTop := tendsto_natCast_atTop_atTop.mono_left h.time
    have hD : ExpSmall l (fun n:ℕ=>(n:ℝ)) D := by
      have h1 := ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc
      have h2:=ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc2
      have hg : ExpSmall l (fun n:ℕ=>(n:ℝ)) e_ := by
        have hi := (h1.mul (expO_const hz (num (Fin r0)/β))).add hz (h2.mul (expO_const hz β⁻¹))
        refine hi.mono (.of_forall (fun i=>?_))
        exact le_of_eq (congrArg abs (by unfold e_ b1 b2; ring))
      obtain ⟨C,hC,hf⟩:= hf
      have h : ExpSmall l (fun n:ℕ=>(n:ℝ)) (fun n=>|f n|) := by
        refine ⟨C*(2*M), by have hm:=hp.hM; positivity,?_⟩
        filter_upwards [hf] with n hn
        rw [abs_abs]
        convert hn using 1 <;> push_cast <;> ring
      simpa [D,div_eq_mul_inv] using hg.add hz (h.mul (expO_const hz score⁻¹))
    refine hD.mono ?_
    have hsmall : ∀ᶠ n in l,
        Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε n) ≤ min y Y := by
      have hlim := (heps.const_mul ((scanPrice p)⁻¹)).const_mul (Fintype.card (Messenger q):ℝ)
      simpa only [mul_zero] using hlim.eventually (eventually_le_nhds
        (by simpa only [mul_zero] using lt_min hy hY))
    have hreject : ∀ᶠ n : ℕ in l,
        bp (num (Messenger q)+(oneBaseProtectionDim p K : ℝ)-(n : ℝ)) ≤ β*min y Y := by
      apply ((one_rejection_vanish p K (Fintype.card (Messenger q))).eventually
        (eventually_le_nhds (mul_pos hβ (lt_min hy hY)))).filter_mono h.time
    have hrejectnet : ∀ᶠ n : ℕ in l,
        bp (num (Messenger q)+(oneBaseProtectionDim p K : ℝ)-(n : ℝ)) ≤ ξ/2 := by
      exact ((one_rejection_vanish p K (Fintype.card (Messenger q))).eventually
        (eventually_le_nhds (half_pos hh))).filter_mono h.time
    have hl := h.time
    filter_upwards [h.upright,h.durable.shape,h.moment,h.durable.mass.positive,
       hF.filter_mono hl,hQ.filter_mono hl,hB.filter_mono hl,hA.filter_mono hl,hξ,
       ht.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2)),hsmall,hE,hreject,hrejectnet]
       with n hn hr ht hx hf hg hB hA hξ hN hsmall hE hreject hrejectnet
    let W:=w n; let s':=s n; let I:=s'.T; let V (i:↑I):=partW W i.val
    let u:=portionW W I; let R:=pairW u u; let G:=t n; let m':=m n
    let ν:= oneLawNu p (N n) x.t x.z; have hm:=ht.1.law
    let P := s'.sap W
    have hν:IsLaw ν:=one_nu_law x.t x.z hN
    let A i:= custom x.qA (V i) (G.cAxes i d) x.t x.z m' (s'.pin i.val) K

    let CB i:= custom x.qB (V i) (G.cAxes i e) x.t x.z m' (s'.pin i.val) K
    let J := predictedCharter G x m' k W β α (g n) (ε n) (E n)
    choose PA PB hselect using fun i : ↑I×↑I => show ∃ PA PB,
        (∀ o, PA o → frontPage G x m' i.1 i.2 k o) ∧
        (∀ o, PB o → backPage G x m' i.1 i.2 k o) ∧
        (J i → OneQuill.OnePredictedQualified x.qA x.t x.z (G.cAxes i.1 d) m' K (V i.1) PA β α (g n) (ε n) (E n) ∧
          OneQuill.OnePredictedQualified x.qB x.t x.z (G.cAxes i.2 e) m' K (V i.2) PB β α (g n) (ε n) (E n)) from by
      by_cases hj : J i
      · obtain ⟨_,PA,PB,hPA,hPB,hQA,hQB⟩ := hj
        exact ⟨PA,PB,hPA,hPB,fun _ => ⟨hQA,hQB⟩⟩
      · exact ⟨fun _ => False,fun _ => False,fun _ h => h.elim,fun _ h => h.elim,fun h => (hj h).elim⟩
    let X (i:↑I×↑I) := sales x.qA x.t x.z (s'.pin i.1.val) K (V i.1) (PA i) m' (G.cAxes i.1 d)
    let Z (i:↑I×↑I) := sales x.qB x.t x.z (s'.pin i.2.val) K (V i.2) (PB i) m' (G.cAxes i.2 e)
    have huv := hr.1
    have hV i : IsLaw (V i):=on_law hm.nz (huv.leaf i.val i.property).pos
    have hC (i:↑I) (o:OneUnit p n (N n)):
        V i o≤bp ((2*b.leafNew)*(M*n:ℕ))*oneUnitRaw m' (M*n) o:=by
      have hc:=(huv.leaf (Subtype.val i) i.property).density o
      convert hc using 2 <;> push_cast <;> ring
    choose Cpart hCpart using fun i : ↑I=>hg m' hn.cols (V i) (hV i) (hC i) (G.cAxes i e)
    obtain ⟨hu,hO⟩:=rebuild hm.nz huv.part (fun i hi=>(huv.leaf _ hi).pos) hx
    have ho : P=mixW u V:= hO
    let S (i : ↑I) (j : Fin r0) := fun k => E n k ∧ Cpart i k=j
    have hSdesign (i : ↑I) (j : Fin r0) :
        OneDesign x.t (fun k=>ind (S i j k)) paints := by
      have hpA:=(hCpart i).1 (fun v=>v=j)
      have hh:=one_design_mul_one x.t _ _ paints hpA (hEdesign n)
      simpa only [S,ind_and,mul_comm] using hh
    let T : OneUnit p n (N n)→Prop:= fun i=>¬OneQuill.OneBaseSober x.qB x.t x.z K (E n) m' y2 i
    let U i j o:= δ ≤ pr ν (S i j) ∧ ¬OneQuill.OneBaseSober x.qA x.t x.z K (S i j) m'
      (OneQuill.oneDilate x.qA x.t K*(pr ν (S i j)/4)) o
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
    have hZ (i:↑I×↑I):CB i.2 (Z i):= sales_custom x.qB _ _ _ _ _ _ _ _
    have heq (i) (hj:J i) (hk:¬O i) : score≤ L i := by
      have hpos : 0 < pr (V i.1) (PA i) :=
        (show 0 < 2*β by positivity).trans_le (((hselect i).2.2 hj).1.1)
      obtain ⟨o,ho,_⟩ := exists_of_pr_pos (hV i.1).nz hpos
      have hnews : news G x i.1 i.2 k := ((hselect i).1 o ho).1
      have hpenA := hnews.2.1.2.1
      have hpenB := hnews.2.2.2.1
      let Z0:=OneQuill.oneNaturalSales x.qB x.t x.z (V i.2) (PB i) m' (G.cAxes i.2 e)
      let d0:=density ν Z0
      let g0:=banner ν (Cpart i.2) d0
      let f0:=fun k=>ν k*g0 k
      have hsupp0:lsupp Z0 ν:=OneQuill.one_natural_sales_support x.qB x.t x.z
        (V i.2) (PB i) m' (G.cAxes i.2 e)
      have happrox0 : varOne Z0 f0≤ξ/2 := by
        rw [var_one_density_reconstruction ν Z0 g0 hν.nz hsupp0]
        exact ((hCpart i.2).2 (PB i)).2
      have hrj : varOne (Z i) Z0≤ξ/2 := by
        rw [show varOne (Z i) Z0=varOne Z0 (Z i) from by
          unfold varOne
          apply Finset.sum_congr rfl
          intro k _
          exact abs_sub_comm _ _]
        exact (OneQuill.one_good_natural_rejection x.qB x.t x.z (s'.pin i.2.val).sp K
          (V i.2) (PB i) m' (G.cAxes i.2 e) (hV _).sub hpenB hL1).2.trans hrejectnet
      have hj' : varOne (Z i) f0≤ξ :=
        (var_tri (Z i) f0 Z0).trans ((add_le_add hrj happrox0).trans_eq (by ring))
      obtain ⟨hP,_,htail⟩:=hf m' (G.cAxes i.1 _) (V i.1) (s'.pin i.1.val).sp K hn.cols (hV _) (hC _)
      obtain ⟨hx,hxs⟩:=hP _ (hX i)
      have hdom:= (OneQuill.one_good_natural_rejection x.qB x.t x.z (s'.pin i.2.val).sp K
        (V i.2) (PB i) m' (G.cAxes i.2 e) (hV _).sub hpenB hL1).1
      have hzs:lsupp (Z i) ν := by
        intro a ha
        apply hsupp0 a
        intro hz
        exact ha (le_antisymm ((hdom a).2.trans_eq hz) (hdom a).1)
      have hzpos a:0≤Z i a:=(hdom a).1
      have hmass : b0≤pr (Z i) (E n) :=
        predicted_qualify_hit x.qB x.t x.z (G.cAxes i.2 e) m' K (s'.pin i.2.val) (V i.2) (PB i)
          α (g n) (ε n) (E n) (E n) (fun _ h=>h) hy ((hselect i).2.2 hj).2
          (hV _) hb hp.hR hn.age hpenB (hsmall.trans (min_le_left ..))
          (hreject.trans (mul_le_mul_of_nonneg_left (min_le_left ..) hβ.le))
          (by simpa only [y,mul_div_cancel₀ _ (by norm_num:(4:ℝ)≠0)] using
            (le_of_not_gt (mt Or.inr hk)))
      have hcell (j:Fin r0):κ*pr ν (S i.2 j)-κ*δ≤pr (X i) (S i.2 j) := by
        by_cases hmass:δ≤pr ν (S i.2 j)
        · let gain:=OneQuill.oneDilate x.qA x.t K*(pr ν (S i.2 j)/16)
          have hgain:Y≤gain:=mul_le_mul_of_nonneg_left (by linarith only [hmass])
            (OneQuill.one_dilate_pos ..).le
          have hbad:pr (V i.1) (fun o=>¬OneQuill.OneBaseSober x.qA x.t x.z K (S i.2 j) m' (4*gain) o)≤β := by
            have he:U i.2 j=fun o=>¬OneQuill.OneBaseSober x.qA x.t x.z K (S i.2 j) m' (4*gain) o := by
              funext o; simp only [U,hmass,true_and]
              congr 2; dsimp only [gain]; ring
            rw [←he]
            exact le_of_not_gt (fun hh=>hk (Or.inl ⟨j,hh⟩))
          have hh:=predicted_qualify_hit x.qA x.t x.z (G.cAxes i.1 d) m' K (s'.pin i.1.val) (V i.1) (PA i)
            α (g n) (ε n) (E n) (S i.2 j) (fun _ h=>h.1) (hY.trans_le hgain)
            ((hselect i).2.2 hj).1 (hV _) ha hp.hR hn.age hpenA
            (hsmall.trans ((min_le_right ..).trans hgain))
            (hreject.trans (mul_le_mul_of_nonneg_left ((min_le_right ..).trans hgain) hβ.le)) hbad
          have he:β*gain=κ*pr ν (S i.2 j):=by dsimp only [gain,κ]; ring
          rw [he] at hh
          nlinarith only [hh,hκ,hd]
        · have hh:=pr_nonneg hx.nz (p:=S i.2 j)
          nlinarith only [le_of_not_ge hmass,hκ,hh]
      have hg0:∀ a,0≤g0 a ∧ g0 a≤B:=(hCpart i.2).2 (PB i) |>.1
      have hcash:=cashbook_bound_of_banner ν d0 hν.nz (Cpart i.2) B hBpos.le hg0
      have hlower:=actual_cell_overlap ν (X i) (Z i) (Cpart i.2) (cashbook ν (Cpart i.2) d0)
        (E n) κ (κ*δ) B Tclip hκ.le (mul_nonneg hκ.le hd.le) hBpos.le hclip.le
        hν.nz hx.nz hzpos hxs hzs hcash hcell
      simp only [Fintype.card_fin] at hlower
      change κ*pr (Z i) (E n)≤overlap ν (X i) (Z i)+B*r0*(κ*δ)+
        (κ+Tclip)*varOne (Z i) f0+B*pr (X i) (fun a=>Tclip≤density ν (X i) a) at hlower
      have he1:=mul_le_mul_of_nonneg_left hj' (add_nonneg hκ.le hclip.le)
      have he2:=mul_le_mul_of_nonneg_left (htail _ (hX i)) hBpos.le
      have he3: (κ+Tclip)*ξ≤κ*b0/8 := by
        have he:8*(κ+Tclip+1)*ξ=κ*b0:=by dsimp only [ξ]; field_simp
        nlinarith only [he,hh.le]
      have he4:B*η=κ*b0/8:=by dsimp only [η]; field_simp
      have he5:B*r0*(κ*δ)≤κ*b0/8 := by
        have he:8*B*(r0+1:ℝ)*δ=b0:=by dsimp only [δ]; field_simp
        have he':=congrArg (κ*·) he
        nlinarith only [he',mul_nonneg hκ.le (mul_nonneg hBpos.le hd.le)]
      change B*pr (X i) (fun a=>Tclip≤density ν (X i) a)≤B*η at he2
      change score≤overlap ν (X i) (Z i)
      dsimp only [score]
      nlinarith only [hlower,mul_le_mul_of_nonneg_left hmass hκ.le,he1,he2,he3,he4,he5,mul_pos hκ h0]
    have hn0 (i:↑I×↑I) : 0 ≤ L i := by
      have h1 i j : 0≤X i j := sales_pos x.qA _ _ _ _ m' _ _ _ (hV _).nz j
      have h2 i j : 0 ≤ Z i j:= sales_pos x.qB _ _ _ _ m' _ _ _ (hV _).nz j
      refine avg_nonneg hν.nz fun j=>mul_nonneg (div_nonneg (h1 i j) (hν.nz _))
        (div_nonneg (h2 i j) (hν.nz _))
    have hv := pairW_law hu hu
    have hscore:avg R L≤G.arena x m' W k:=by
      apply avg_mono hv.nz
      intro i
      exact G.filtered_match_le x m' W i.1 i.2 k (by have := hq.planted.hG; omega)
        hm.nz (hselect i).1 (hselect i).2.1
    have hi := le_avg_markov hv.nz hn0 score
    change |pr R J| ≤ _
    rw [abs_of_nonneg (pr_nonneg hv.nz)]
    apply le_trans _ (le_abs_self (D n))

    have hg (i) (h:J i): O i ∨ score ≤ L i := by
      by_cases hi:O i
      · exact Or.inl hi
      exact Or.inr (heq i h hi)
    refine ((pr_mono hv.nz hg).trans (pr_or_le hv.nz)).trans (add_le_add hT ?_)
    refine (le_div_iff₀ (by positivity)).mpr (le_trans ?_ (hscore.trans
      ((hξ q d e x k).trans (le_abs_self _))))
    rw [mul_comm]; exact hi
  · refine (ExpSmall.zero l (fun n=>(n:ℝ))).mono (.of_forall (fun n=>?_))
    have hh i : ¬predictedCharter (t n) x (m n) k (w n) β α (g n) (ε n) (E n) i :=fun he=>hX he.1
    unfold predictedBerth pr
    simp only [ind_zero (hh _),avg_const,mul_zero,le_refl]
end OneStation

end

end Lax793645Proofs.Simplifications
