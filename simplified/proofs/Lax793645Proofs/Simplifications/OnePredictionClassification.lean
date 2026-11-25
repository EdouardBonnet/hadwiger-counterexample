import Lax793645Proofs.Simplifications.OnePredictionPruning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure OneDosed {p : Shape} {M : ℕ} (q : PreparationParameters) (l : Filter ℕ)
    (m : cycleM p) (w : OneTale p M) (s : OneRhythms p M)
    (b : OneSketch p M) (P : OneCampaign p M) : Prop where
  forecast : OneLedger b l
  lower : ∀ᶠ n in l,pollen≤pr ((s n).sap (w n)) (P n)
  capped : ∀ᶠ n in l,∀ x i,totalRank (b.m n x i)≤q.e
  mark : ∀ᶠ n in l,∀ x,P n x → oneEngrave b q m s n x

variable {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {U : Ultrafilter ℕ} {P : OneCampaign p M}

set_option maxHeartbeats 1600000 in
theorem one_cohorts_to_dose_preserving (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n))
    (Inv : ∀ n,(Bool→OneAugur p (M*n))→Prop)
    (ε : ℕ→ℝ) (hε : slight (U:Filter ℕ) ε)
    (h : ∀ᶠ n in U,∃ (z : OneBanners) (i : OneSage p n (M*n)),
      Inv n i.g ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
        crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z (ε n))) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool), OneDosed q (U:Filter ℕ) m w s b P ∧
       (∀ᶠ n in U,Inv n (fun i=>b.g i n)) ∧
       ∀ᶠ n in U, ∀ x,P n x → ((i=true) ↔ oneMarkedDelta x (b.m n x)=0) := by
  classical
  let R (n : ℕ) (z : OneBanners) (i : OneSage p n (M*n)) :=
    Inv n i.g ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧ crowdSeed≤pr ((s n).sap (w n)) (oneTender i q (m n) (s n) z (ε n))
  have hh : ∀ᶠ n in U,∃ (z:OneBanners) (i:OneSage p n (M*n)),R n z i := h
  obtain ⟨z,hz⟩ := Ultrafilter.eventually_exists_iff.mp hh
  obtain ⟨i,hi⟩ := taking hz
  let g (j:Bool): OneSeason p M := fun n => (i n).g j
  obtain ⟨c,τ,hτ,hG,hL,hB⟩:= one_examine U p M g z.1
  let b:= (⟨c,z.1,z.2.1,fun n=>(i n).m,fun n=>(i n).L,g,ε⟩: OneSketch p M)
  let P : OneCampaign p M := fun n => oneTender (i n) q (m n) (s n) z (ε n)
  have hT : OneLedger b (U:Filter ℕ):= ⟨hε,hL⟩
  have hk :
      ∃ Q : OneCampaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→ P n x∧ (b.c=dusk→ oneExactInk (m n) (b.m n) x) := by
    by_cases hC : c=dusk
    · obtain ⟨Q,hQ⟩:= one_prune_whisper hl hq hw hx (show b.c=dusk from hC) hT (hB hC)
       (P:=P) (hi.mono fun n hn=>⟨hn.2.2,fun x h=>h.1⟩)
      exact ⟨Q,hQ.mono (fun n hn=>⟨hn.1,fun i h=>⟨(hn.2 i h).1,fun _=>(hn.2 i h).2⟩⟩)⟩
    exact ⟨P,hi.mono (fun n hn=>⟨le_trans (show pollen≤crowdSeed from
      by unfold crowdSeed; linarith only [pollen_pos]) hn.2.2,fun x h=>⟨h,fun hh=>(hC hh).elim⟩⟩)⟩
  obtain ⟨Q,hQ⟩:=hk
  have hB : ∀ᶠ n in U,pollen ≤ pr ((s n).sap (w n)) (Q n) := hQ.mono fun i hi=>hi.1
  refine ⟨b,Q,z.2.2,⟨hT,hB,hi.mono (fun n hn=>hn.2.1),?_⟩,
    hi.mono (fun n hn=>hn.1),hQ.mono fun n hn x hx=>((hn.2 x hx).1).2.2⟩
  filter_upwards [hQ] with n hn x hx
  obtain ⟨⟨hr,hv,_⟩,hs⟩:=hn.2 x hx
  exact ⟨hr,hv,hs⟩

theorem one_outlook_to_dose_preserving (hl : (U:Filter ℕ)≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in U,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in U,OneEntered q (m n) (w n) (s n))
    (Inv : ∀ n,(Bool→OneAugur p (M*n))→Prop)
    (h : ∃ ε : ℕ→ℝ,slight (U:Filter ℕ) ε ∧ ∀ᶠ n in U,
      ∃ g : Bool→OneAugur p (M*n),Inv n g ∧
        (0.000001:ℝ)≤pr ((s n).sap (w n))
          (fun x=>∃ z L α,oneSeems q (m n) (s n) x g z L α (ε n))) :
    ∃ (b : OneSketch p M) (P : OneCampaign p M) (i : Bool),OneDosed q (U:Filter ℕ) m w s b P ∧
      (∀ᶠ n in U,Inv n (fun i=>b.g i n)) ∧
      ∀ᶠ n in U,∀ x,P n x→((i=true)↔oneMarkedDelta x (b.m n x)=0) := by
  obtain ⟨ε,hε,h⟩:=h
  apply one_cohorts_to_dose_preserving hl hq hw hx Inv ε hε
  filter_upwards [h,hw,hx] with n hn ht hv
  exact one_cohort_preserving (m n) (w n) (s n) hv ht.law (Inv n) hn

end
end Lax793645Proofs.Simplifications
