import Lax793645Proofs.Simplifications.OneFixedCommonProjection
import Lax793645Proofs.Simplifications.OneAverageSurrogateBounds
import Lax793645Proofs.Simplifications.OneLinearComparisonCalendar

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Function Finset
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {p : Shape} {q : Format} {d e : Rates} {M K s0 : ℕ}

private theorem uniform_law_instances {D : Type} (i j k l : Fintype D) (P : D→Prop) :
    @IsLaw D i (@unifOn D j P) ↔ @IsLaw D k (@unifOn D l P) := by
  cases Subsingleton.elim i k
  cases Subsingleton.elim j l
  rfl

private def projectionCost {Λ D A : Type} [Fintype Λ] [Fintype D] [Fintype A]
    (μ : Wgt Λ) (K : D→Prop) (P : D→A) (p q : Λ→Wgt D) :=
  let ν:=unifOn K
  avg μ (fun l=>dip ν (banner ν P (density ν (p l))) (banner ν P (density ν (q l))))

private theorem projection_cost_instances {Λ D A : Type} [Fintype Λ] [Fintype A]
    (i j : Fintype D) (μ : Wgt Λ) (K : D→Prop) (P : D→A) (p q : Λ→Wgt D) :
    @projectionCost Λ D A _ i _ μ K P p q=@projectionCost Λ D A _ j _ μ K P p q := by
  cases Subsingleton.elim i j
  rfl

namespace OneTypus

def oneScoreGood {n N r : ℕ} (w : Typus p q d e) (m : Mixer p n)
    (Y : OneSilhouette p N r) (θ : ℝ) (o : OneUnit p n N) :=
  (∀ i,oneFrameLaw m (o i)) ∧
    OneQuill.oneMatchesArea w.qA w.t w.z Y o θ ∧
    OneQuill.oneMatchesArea w.qB w.t w.z Y o θ ∧ oneLitFire o

/-- Finite score replacement for the common-limit argument. The common
linear partition precedes all pair-dependent filters and all permitted
small-mass rejections. Its dimension is independent of n. -/
theorem one_finite_score_calendar (w : Typus p q d e)
    [DecidableEq (KeySlots p w.t)]
    (hA : w.qA.moral w.t w.z) (hB : w.qB.moral w.t w.z)
    (h : OneUnaryParameters p M K s0) (c ε : ℝ) (hε : 0<ε) :
    ∃ S : ℕ,∃ δ θ σ : ℝ,0<δ ∧ 0<θ ∧ 0<σ ∧
    ∀ᶠ n : ℕ in atTop,∀ m : Mixer p n,reducedBinaryGood m →
      Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (OneUnit p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      ∃ L : KeyCoordinates (KeySlots p w.t) (M*n)→ₗ[F]Vec (Fin S),
      ∀ r (Y : OneSilhouette p (M*n) r),
        OneRefines Y (oneLinearKeyPalette w.t (L.comp (oneKeyCoordinatesMap w.t (M*n)))) →
      ∀ F G : Λ×Λ→OneUnit p n (M*n)→Prop,
      ∀ QA QB : Λ×Λ→Wgt (KeyCoordinates (KeySlots p w.t) (M*n)),
        (∀ l x,0≤QA l x ∧ QA l x≤oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1) x) →
        (∀ l x,0≤QB l x ∧ QB l x≤oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2) x) →
        (∀ l,varOne (oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1)) (QA l)≤δ) →
        (∀ l,varOne (oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2)) (QB l)≤δ) →
        avg (pairW μ μ) (fun l=>overlap (unifOn (oneOwnPart w.t w.z)) (QA l) (QB l))≤σ →
        pr (mixW μ π) (fun o=>¬oneScoreGood w m Y θ o)≤σ →
        avg (pairW μ μ) (fun l=>oneFilteredScore w (π l.1) (π l.2)
          (F l) (G l) (a l.1) (a' l.2) m Y)≤ε := by
  let σ:=ε^2/64
  have hσ : 0<σ:=div_pos (sq_pos_of_pos hε) (by norm_num)
  obtain ⟨S,δ,hδ,hproj⟩:=one_fixed_rejected_common_projection
    w.qA w.qB w.t w.z hA hB h.hR M h.hM c σ hσ
  obtain ⟨θA,hθA,_,hcalA⟩:=OneQuill.one_linear_comparison_calendar w.qA w.t w.z hA M h S σ hσ
  obtain ⟨θB,hθB,_,hcalB⟩:=OneQuill.one_linear_comparison_calendar w.qB w.t w.z hB M h S σ hσ
  let θ:=min θA θB
  have hθ : 0<θ:=lt_min hθA hθB
  have hz:=(trend_sizes atTop (le_refl _) h.hM).2
  have href : ∀ᶠ n : ℕ in atTop,
      2*quadraticNetFact (trayPort p w.t)*bp (-((M*n:ℕ):ℝ)/2)≤ε/2 := by
    have he:=((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul
      (2*quadraticNetFact (trayPort p w.t))
    filter_upwards [he.eventually (eventually_le_nhds
      (by simpa only [mul_zero] using half_pos hε))] with n hn
    simpa only [Function.comp_apply,
      show -(1/2:ℝ)*((M*n:ℕ):ℝ)= -((M*n:ℕ):ℝ)/2 from by ring] using hn
  refine ⟨S,δ,θ,σ,hδ,hθ,hσ,?_⟩
  filter_upwards [hproj,hcalA,hcalB,href,eventually_ge_atTop (2*p.r),
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+2))]
    with n hn hCA hCB href hnR hdim m hm hN Λ _ μ hμ π hπ hcap a a'
  obtain ⟨L,hL⟩:=hn m hN Λ μ hμ π hπ hcap a a'
  refine ⟨L,fun r Y hY F G QA QB hQA hQB hvarA hvarB hover hbad=>?_⟩
  let Z (o : OneUnit p n (M*n)):=¬oneScoreGood w m Y θ o
  have hν:=one_nu_law w.t w.z hdim
  have hν' : IsLaw (unifOn (oneOwnPart (N:=M*n) w.t w.z)):=by
    have he:=one_reference_coordinates (N:=M*n) w.t w.z
    have hh:=mapW_law hν (oneQueryCoordinateEquiv w.t (M*n)).symm
    rw [he] at hh
    convert hh using 1
    congr 1
    exact Subsingleton.elim _ _
  have ha i : IsLaw (w.qA.policies w.t w.z n i):=
    Appearance.witLaw (w.qA.allure_apt w.t w.z hA i) h.hR hnR
  have hb i : IsLaw (w.qB.policies w.t w.z n i):=
    Appearance.witLaw (w.qB.allure_apt w.t w.z hB i) h.hR hnR
  have htestA (l : Λ×Λ) (φ : Wgt (Vec (Fin S))) (hφ : ∀ x,|φ x|≤1)
      (o : OneUnit p n (M*n)) (_ : F l o) (ho : ¬Z o) :
      |OneQuill.oneProwl w.qA w.t w.z o m (a l.1) (φ ∘ L.comp (oneKeyCoordinatesMap w.t (M*n)))-
        OneQuill.oneSheen w.qA w.t w.z o m (a l.1) Y
          (φ ∘ L.comp (oneKeyCoordinatesMap w.t (M*n)))|≤σ := by
    have hg : oneScoreGood w m Y θ o:=not_not.mp ho
    have harea : OneQuill.oneMatchesArea w.qA w.t w.z Y o θA:=
      fun i=>(hg.2.1 i).trans (min_le_left θA θB)
    exact hCA m hm r Y o hg.1 harea hg.2.2.2 _ _ hY φ hφ
  have htestB (l : Λ×Λ) (φ : Wgt (Vec (Fin S))) (hφ : ∀ x,|φ x|≤1)
      (o : OneUnit p n (M*n)) (_ : G l o) (ho : ¬Z o) :
      |OneQuill.oneProwl w.qB w.t w.z o m (a' l.2) (φ ∘ L.comp (oneKeyCoordinatesMap w.t (M*n)))-
        OneQuill.oneSheen w.qB w.t w.z o m (a' l.2) Y
          (φ ∘ L.comp (oneKeyCoordinatesMap w.t (M*n)))|≤σ := by
    have hg : oneScoreGood w m Y θ o:=not_not.mp ho
    have harea : OneQuill.oneMatchesArea w.qB w.t w.z Y o θB:=
      fun i=>(hg.2.2.1 i).trans (min_le_right θA θB)
    exact hCB m hm r Y o hg.1 harea hg.2.2.2 _ _ hY φ hφ
  have hEA:=OneQuill.one_average_projected_error w.qA w.t w.z μ hμ π hπ true F a m Y L
    ha hν Z hσ.le (by simpa only [oneLeafOfSide,if_true] using htestA)
  have hEB:=OneQuill.one_average_projected_error w.qB w.t w.z μ hμ π hπ false G a' m Y L
    hb hν Z hσ.le (by simpa only [oneLeafOfSide,Bool.false_eq_true,if_false] using htestB)
  simp only [oneLeafOfSide,if_true,Bool.false_eq_true,if_false] at hEA hEB
  have hp:= (hL F G QA QB hQA hQB hvarA hvarB).trans (add_le_add hover le_rfl)
  apply one_average_score_bound w μ π F G a a' m Y L hμ hπ ha hb
    ((uniform_law_instances _ _ _ _ _).mp hν') hdim ε (2*σ) (6*σ) hε.le
  · rw [←two_mul] at hp
    exact (projection_cost_instances _ _ (pairW μ μ) (oneOwnPart w.t w.z) L
      (fun l=>oneSales w.qA w.t w.z (π l.1) (F l) m (a l.1))
      (fun l=>oneSales w.qB w.t w.z (π l.2) (G l) m (a' l.2))).trans_le hp
  · rw [avg_add]
    have hh:=add_le_add hEA hEB
    dsimp only [Z] at hh
    linarith only [hh,hbad]
  · dsimp only [σ]; nlinarith only [sq_nonneg ε]
  · exact href

end OneTypus
end
end Lax793645Proofs.Simplifications
