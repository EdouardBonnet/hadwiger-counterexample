import Lax793645Proofs.Simplifications.ExactStatusDuality
import Lax793645Proofs.Simplifications.ExactSupportFamilies

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {r : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

def ExactStatusPrediction (u : Terrain p r) (s : Gazette p r d)
    (i : Nodes) (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p r) : Prop :=
  ∀ x : Appearance p,x.s∉A→x.apt→∀ c,0<u x.l x.q c→
    ∀ v,0<s i x c v→a.soot x v=f x.l x.q c

/-- The exact support statement implies the old zero-error interface,
without using any comparison of empirical and reference probabilities. -/
theorem exact_status_prediction_zero (hu : ∀ l q,IsLaw (u l q))
    (hs : ∀ i (x : Appearance p),x.apt→∀ c,IsLaw (s i x c))
    (i : Nodes) (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p r)
    (h : ExactStatusPrediction u s i A a f) : praise u s i A a f 0 := by
  intro x hx hapt
  have he : shot u s i x a f=0 := by
    unfold shot avg
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : u x.l x.q c=0
    · rw [hc,zero_mul]
    have hc' : 0<u x.l x.q c:=lt_of_le_of_ne ((hu _ _).nz c) (Ne.symm hc)
    have hp : pr (s i x c) (fun v=>a.soot x v≠f x.l x.q c)=0 := by
      unfold pr avg
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv : s i x c v=0
      · rw [hv,zero_mul]
      have hv' : 0<s i x c v:=lt_of_le_of_ne ((hs i x hapt c).nz v) (Ne.symm hv)
      change s i x c v*ind (a.soot x v≠f x.l x.q c)=0
      rw [ind_zero (not_not.mpr (h x hx hapt c hc' v hv')),mul_zero]
    change u x.l x.q c*pr (s i x c) (fun v=>a.soot x v≠f x.l x.q c)=0
    rw [hp,mul_zero]
  exact he.le

/-- Exact relations on support rectangles give one predictor shared by
all surviving labels. This replaces the majority construction. -/
theorem exact_status_predictors
    (hs : ∀ i (x : Appearance p),x.apt→∀ c,IsLaw (s i x c))
    (ht : ∀ i (x : Appearance p),x.apt→∀ c,IsLaw (t i x c))
    (i : Grid) (A B : Finset (Label p.b))
    (hA : A.card<Fintype.card (Label p.b)) (hB : B.card<Fintype.card (Label p.b))
    (hg : 3≤p.g) (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2))
    (h : ∀ x y : Appearance p,x.s∉A→y.s∉B→x.apt→y.apt→x.l=y.l→x.q=y.q→
      ∀ c,0<u x.l x.q c→∀ v w,0<s i.1 x c v→0<t i.2 y c w→a.soot x v=b.soot y w) :
    ∃ f : Pulsar p r,ExactStatusPrediction u s i.1 A a f ∧
      ExactStatusPrediction u t i.2 B b f := by
  classical
  obtain ⟨a₀,ha₀⟩:=any_label A hA
  obtain ⟨b₀,hb₀⟩:=any_label B hB
  let Left (l : Tag p.g) (q : F):=
    {x : Appearance p // x.l=l ∧ x.q=q ∧ x.s∉A ∧ x.apt}
  let Right (l : Tag p.g) (q : F):=
    {x : Appearance p // x.l=l ∧ x.q=q ∧ x.s∉B ∧ x.apt}
  have choice (l : Tag p.g) (q : F) : ∃ φ : Fin r→F,
      (∀ c,0<u l q c→∀ x : Left l q,∀ v,0<s i.1 x.val c v→a.soot x.val v=φ c) ∧
      (∀ c,0<u l q c→∀ y : Right l q,∀ w,0<t i.2 y.val c w→b.soot y.val w=φ c) := by
    let : Nonempty (Left l q):=
      ⟨⟨amazes p a₀ l q,rfl,rfl,ha₀,generic_apt p hg _ rfl⟩⟩
    let : Nonempty (Right l q):=
      ⟨⟨amazes p b₀ l q,rfl,rfl,hb₀,generic_apt p hg _ rfl⟩⟩
    apply exact_family_predictor
      (fun x : Left l q=>s i.1 x.val) (fun y : Right l q=>t i.2 y.val)
      (fun x c=>hs i.1 x.val x.property.2.2.2 c)
      (fun y c=>ht i.2 y.val y.property.2.2.2 c)
      (fun x=>a.soot x.val) (fun y=>b.soot y.val) (fun c=>0<u l q c)
    intro c hc x y v w hv hw
    apply h x.val y.val x.property.2.2.1 y.property.2.2.1
      x.property.2.2.2 y.property.2.2.2
      (x.property.1.trans y.property.1.symm) (x.property.2.1.trans y.property.2.1.symm) c
    · simpa only [x.property.1,x.property.2.1] using hc
    · exact hv
    · exact hw
  choose f hf hf' using choice
  refine ⟨f,?_,?_⟩
  · intro x hx hapt c hc v hv
    exact hf x.l x.q c hc ⟨x,rfl,rfl,hx,hapt⟩ v hv
  · intro y hy hapt c hc w hw
    exact hf' y.l y.q c hc ⟨y,rfl,rfl,hy,hapt⟩ w hw

/-- Apply the exact extraction directly to the scalar dual obstruction.
The resulting predictor is valid on every positive cell and status. -/
theorem dual_exact_status_predictors (hu : origami p r u δ)
    (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hgap : HasStatusSupportGap u s t η)
    (A B : Stalls p) (S : Straps (Label p.b)) (z : DualCoefficients d e)
    (hz : z.law (chapter (stellar u s t η A B) S))
    (i : Grid) (hg : 3≤p.g)
    (hA : (outstraps A S true i.1).card<Fintype.card (Label p.b))
    (hB : (outstraps B S false i.2).card<Fintype.card (Label p.b)) :
    ∃ f : Pulsar p r,
      ExactStatusPrediction u s i.1 (outstraps A S true i.1) (leftChime z i) f ∧
      ExactStatusPrediction u t i.2 (outstraps B S false i.2) (rightChime z i) f := by
  apply exact_status_predictors hs.law ht.law i _ _ hA hB hg (leftChime z i) (rightChime z i)
  intro x y hx hy hapt hapt' hl hq c hc v w hv hw
  let X:=amends p x y
  have he : X.aspect false=y:=amendsB x y hl hq
  have ht' : X.aspect true=x:=rfl
  have hcommon : X.common := by
    intro side
    cases side
    · rw [he]; exact hapt'
    · rw [ht']; exact hapt
  have hhv : 0<s i.1 (X.aspect true) c v:=hv
  have hhw : 0<t i.2 (X.aspect false) c w:=by rw [he]; exact hw
  have hh:=dual_cell_support_eq hu hs ht hgap A B S z hz X i hcommon hx hy c hc v w hhv hhw
  rwa [ht',he] at hh

end
end Lax793645Proofs.Simplifications
