import Lax793645Proofs.Simplifications.ExactPredictionCatalog
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionExtraction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {p : Shape} {r : ℕ} {d e : Rates}

def TesterSeparated (u : Terrain p r) (Free : Pulsar p r→Prop) : Prop :=
  ∀ f g γ,Free f→Free g→
    SamePrediction u f (fun l q c=>g l q c+γ*q)→γ=0

theorem exact_status_congr {u : Terrain p r} {s : Gazette p r d}
    {i : Nodes} {E : Finset (Label p.b)} {a : RhymeSet (d i)} {f g : Pulsar p r}
    (h : ExactStatusPrediction u s i E a f) (he : SamePrediction u f g) :
    ExactStatusPrediction u s i E a g := by
  intro x hx hapt c hc v hv
  exact (h x hx hapt c hc v hv).trans (he x.l x.q c hc)

/-- An edge with a nonzero first internal-bit coefficient forces the
first endpoint to use either zero or the second endpoint's canonical
predictor. The tester shift disappears by exact separation. -/
theorem exact_edge_catalog {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    {β δ : ℝ} (hg : 3≤p.g) (hu : origami p r u δ)
    (ht : reports p r u t β δ) (hβ : 0<β)
    (B : ℕ) (hB : B<Fintype.card (Label p.b))
    (Free : Pulsar p r→Prop) (hzero : Free 0) (hsep : TesterSeparated u Free)
    (hnorm : ∀ i E,E.card≤B→∀ w α f,
      ExactStatusPrediction u s i E (yokeSet w α) f→Free f)
    (cat : Nodes→Pulsar p r) (hcat : ExactCatalog u t B cat) (hcatfree : ∀ i,Free (cat i))
    (i j : Nodes) (E G : Finset (Label p.b)) (hE : E.card≤B) (hF : G.card≤B)
    (a : RhymeSet (d i)) (b : RhymeSet (e j)) (ha : a.bit=1) (f : Pulsar p r)
    (hleft : ExactStatusPrediction u s i E a f)
    (hright : ExactStatusPrediction u t j G b f) :
    ExactStatusPrediction u s i E (yokeSet a.coal (1+a.headBit))
      (if b.bit=0 then 0 else cat j) := by
  classical
  let fA : Pulsar p r:=fun l q c=>f l q c+a.gamma*q
  have hA : ExactStatusPrediction u s i E (yokeSet a.coal (1+a.headBit)) fA :=
    exact_prediction_shift i E a f ha hleft
  have hfree : Free fA:=hnorm i E hE a.coal (1+a.headBit) fA hA
  have hshift (l : Tag p.g) (q : F) (c : Fin r) :
      fA l q c=(f l q c+b.gamma*q)+(a.gamma+b.gamma)*q := by
    dsimp only [fA]
    rw [add_mul]
    have hc:=char_two (b.gamma*q)
    linear_combination -hc
  rcases bit_cases b.bit with hb|hb
  · rw [if_pos hb]
    obtain ⟨_,_,hf⟩:=exact_zero_bit_prediction hg hu ht hβ j b f G (hF.trans_lt hB) hright hb
    have he : SamePrediction u fA (fun _ q _=>0+(a.gamma+b.gamma)*q) := by
      intro l q c hc
      rw [hshift,hf l q c hc,char_two]
    have hγ:=hsep fA 0 (a.gamma+b.gamma) hfree hzero he
    apply exact_status_congr hA
    intro l q c hc
    simpa only [hγ,zero_mul,add_zero,Pi.zero_apply] using he l q c hc
  · rw [if_neg (by rw [hb]; exact one_ne_zero)]
    have hC:=hcat j G hF b.coal (1+b.headBit)
      (fun l q c=>f l q c+b.gamma*q) (exact_prediction_shift j G b f hb hright)
    have he : SamePrediction u fA (fun l q c=>cat j l q c+(a.gamma+b.gamma)*q) := by
      intro l q c hc
      rw [hshift]
      exact congrArg (fun v=>v+(a.gamma+b.gamma)*q) (hC l q c hc)
    have hγ:=hsep fA (cat j) (a.gamma+b.gamma) hfree (hcatfree j) he
    apply exact_status_congr hA
    intro l q c hc
    simpa only [hγ,zero_mul,add_zero] using he l q c hc

/-- The seven possible pairs consist of the zero pair and three
nonzero endpoint masks for each of the two second-side predictors. -/
def sevenPredictionPairs (f : Nodes→Pulsar p r) : Finset (Nodes→Pulsar p r) := by
  classical
  exact {0} ∪ (univ.image fun j : Nodes=>fun i=>if i then f j else 0) ∪
    (univ.image fun j : Nodes=>fun i=>if i then 0 else f j) ∪
    (univ.image fun j : Nodes=>fun _=>f j)

theorem seven_prediction_pairs_card (f : Nodes→Pulsar p r) :
    (sevenPredictionPairs f).card≤7 := by
  classical
  unfold sevenPredictionPairs
  have h1:=card_union_le ({0} ∪ (univ.image fun j : Nodes=>fun i=>if i then f j else 0) ∪
    (univ.image fun j : Nodes=>fun i=>if i then 0 else f j))
    (univ.image fun j : Nodes=>fun _ : Nodes=>f j)
  have h2:=card_union_le ({0} ∪ (univ.image fun j : Nodes=>fun i=>if i then f j else 0))
    (univ.image fun j : Nodes=>fun i : Nodes=>if i then 0 else f j)
  have h3:=card_union_le ({0} : Finset (Nodes→Pulsar p r))
    (univ.image fun j : Nodes=>fun i : Nodes=>if i then f j else 0)
  have ha:=card_image_le (s:=univ) (f:=fun j : Nodes=>fun i : Nodes=>if i then f j else 0)
  have hb:=card_image_le (s:=univ) (f:=fun j : Nodes=>fun i : Nodes=>if i then 0 else f j)
  have hc:=card_image_le (s:=univ) (f:=fun j : Nodes=>fun _ : Nodes=>f j)
  simp only [card_singleton,card_univ,Nodes,Fintype.card_bool] at *
  omega

theorem masked_prediction_mem_seven (f : Nodes→Pulsar p r) (j : Nodes) (a : Nodes→F) :
    (fun i=>if a i=0 then 0 else f j)∈sevenPredictionPairs f := by
  classical
  rcases bit_cases (a true) with ht|ht <;> rcases bit_cases (a false) with hf|hf
  all_goals
    simp only [sevenPredictionPairs,mem_union,mem_singleton,mem_image,mem_univ,true_and]
  · left; left; left
    funext i
    cases i <;> simp [ht,hf]
  · left; right
    refine ⟨j,?_⟩
    funext i
    cases i <;> simp [ht,hf]
  · left; left; right
    refine ⟨j,?_⟩
    funext i
    cases i <;> simp [ht,hf]
  · right
    refine ⟨j,?_⟩
    funext i
    cases i <;> simp [ht,hf]

def ExactAnnounced (u : Terrain p r) (s : Gazette p r d)
    (cat : Nodes→Pulsar p r) (B : ℕ) : Prop :=
  ∃ f∈sevenPredictionPairs cat,∃ w : styles d,∃ α : Party,∃ E : Stalls p,
    ∀ i,(E i).card≤B ∧ ExactStatusPrediction u s i (E i) (yokeSet (w i) (α i)) (f i)

/-- The coupled dual relation produces one of seven predictor pairs on
one side. This replaces the 128-function approximate dictionary. -/
theorem exact_seven_alternative {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    {β δ : ℝ} (hg : 3≤p.g) (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ) (hβ : 0<β)
    (B : ℕ) (hB : B<Fintype.card (Label p.b))
    (Free : Pulsar p r→Prop) (hzero : Free 0) (hsep : TesterSeparated u Free)
    (hnormS : ∀ i E,E.card≤B→∀ w α f,
      ExactStatusPrediction u s i E (yokeSet w α) f→Free f)
    (hnormT : ∀ i E,E.card≤B→∀ w α f,
      ExactStatusPrediction u t i E (yokeSet w α) f→Free f)
    (catS catT : Nodes→Pulsar p r)
    (hcatS : ExactCatalog u s B catS) (hcatT : ExactCatalog u t B catT)
    (hfreeS : ∀ i,Free (catS i)) (hfreeT : ∀ i,Free (catT i))
    (E G : Stalls p) (hE : ∀ i,(E i).card≤B) (hF : ∀ i,(G i).card≤B)
    (z : DualCoefficients d e) (hz : z.left≠0 ∨ z.right≠0)
    (hpred : ∀ i : Grid,∃ f : Pulsar p r,
      ExactStatusPrediction u s i.1 (E i.1) (leftChime z i) f ∧
      ExactStatusPrediction u t i.2 (G i.2) (rightChime z i) f) :
    ExactAnnounced u s catT B ∨ ExactAnnounced u t catS B := by
  classical
  choose f hf hf' using hpred
  have nonzero (a : Nodes→F) (ha : a≠0) : ∃ i,a i=1 := by
    by_contra! hn
    exact ha (funext fun i=>(bit_cases (a i)).resolve_right (hn i))
  rcases hz with hz|hz
  · obtain ⟨j,hj⟩:=nonzero z.left hz
    refine Or.inl ⟨_,masked_prediction_mem_seven catT j z.right,
      (fun i=>(leftChime z (i,j)).coal),(fun i=>1+(leftChime z (i,j)).headBit),E,?_⟩
    intro i
    refine ⟨hE i,?_⟩
    exact exact_edge_catalog hg hu ht hβ B hB Free hzero hsep hnormS catT hcatT hfreeT
      i j (E i) (G j) (hE i) (hF j) (leftChime z (i,j)) (rightChime z (i,j)) hj
      (f (i,j)) (hf (i,j)) (hf' (i,j))
  · obtain ⟨i,hi⟩:=nonzero z.right hz
    refine Or.inr ⟨_,masked_prediction_mem_seven catS i z.left,
      (fun j=>(rightChime z (i,j)).coal),(fun j=>1+(rightChime z (i,j)).headBit),G,?_⟩
    intro j
    refine ⟨hF j,?_⟩
    exact exact_edge_catalog hg hu hs hβ B hB Free hzero hsep hnormT catS hcatS hfreeS
      j i (G j) (E i) (hF j) (hE i) (rightChime z (i,j)) (leftChime z (i,j)) hi
      (f (i,j)) (hf' (i,j)) (hf (i,j))

end
end Lax793645Proofs.Simplifications
