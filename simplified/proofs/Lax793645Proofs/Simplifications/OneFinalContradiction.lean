import Lax793645Proofs.Simplifications.OneFinitePreparation
import Lax793645Proofs.Simplifications.OneQuietEnd
import Lax793645Proofs.Simplifications.OnePredictedEnds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter PreparationParameters
noncomputable section
variable {p:Shape} {M s0:ℕ} {b:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

/-- Both alternatives produced by one-frame preparation are contradicted
by the actual accepted-query overlap bounds. -/
theorem one_refute_veil (h:OneVeil p M b s0 l m s w) (hl:l.NeBot)
    (hout:oneLinearSilenceOutcome b l m w s ∨ oneLinearPredOutcome b l m w s):False := by
  classical
  let (n:ℕ):Nonempty (OneStation p n (M*n) (onePreparationPins b) (s n)):=
    ⟨⟨fun _ _ _=>0,fun _ _ _ _=>0⟩⟩
  have hex : ∀ᶠ n in l,∃ v:OneStation p n (M*n) (onePreparationPins b) (s n),v.bank := by
    filter_upwards [h.durable.shape] with n hn
    exact OneStation.create (fun i=>(hn.1.leaf _ i.property).bound)
  obtain ⟨v,hv⟩:=taking hex
  rcases hout with hquiet|⟨x,hlin,hx,hpos|hrare⟩
  · exact one_quiet_end v h hv hl hquiet
  · exact OneOptions.predicted_gold_end v h hv hl x hx hlin hpos
  exact OneOptions.predicted_dim_end v h hv hl x hx hlin hrare

/-- Read the finite certificate at each dimension. Taking the maximum of
the finitely many terminal bounds also covers laws whose branch changes. -/
theorem one_refute_finite_preparation (hp : OneAnalyticParameters p M b s0)
    (hl : l≤atTop) [l.NeBot]
    (hm : ∀ᶠ n in l,OneNascent b (m n) (w n) ∧ unaryGood (m n) (onePreparationPins b) s0 ∧
      reducedBinaryGood (m n) ∧ oneConflicted (m n) (w n))
    {k : ℕ} (h : ∀ᶠ n in l,OnePreparedAt b (m n) (w n) k) : False := by
  classical
  obtain ⟨s,hs⟩:=taking h
  have hfalse : ∀ᶠ n in l,False := by
    apply eventually_of_finite_cases (fun n tag=>OneBranchAt b (m n) (w n) (s n) (preparationQuota k) tag)
      (hs.mono fun _ h=>h.2.2)
    intro tag v hv hne htag
    let : v.NeBot := hne
    have ht := hv.trans hl
    have hs := hs.filter_mono hv
    have hd : OneDurable b v m w s :=
      ⟨(warm.const (one_trend_sizes v ht hp.planted.hM).2 (quota_pos k)).mono
        (hs.mono fun _ h=>h.1),hs.mono (fun _ h=>h.2.1),_,quota_pos k,hs.mono (fun _ h=>h.1)⟩
    have veil : OneVeil p M b s0 v m s w := ⟨hp,ht,hd,hm.filter_mono hv⟩
    suffices F : False from F.elim
    apply one_refute_veil veil hne
    rcases tag with _|⟨c,α,r,rare⟩
    · exact Or.inl ⟨0,le_rfl,htag⟩
    have hdata := htag.mono fun n h=>h.2
    obtain ⟨i,hi⟩:=taking hdata
    let x : OneSketch p M := ⟨c,α,r,fun n=>(i n).m,fun n=>(i n).L,fun j n=>(i n).g j,fun _=>0⟩
    have lit := (htag.exists.choose_spec).1
    have bright : OneBright b v m s x :=
      ⟨⟨fun ε he=>Eventually.of_forall fun _=>he.le,lit⟩,hi.mono fun _ h=>h.2.2.1⟩
    refine Or.inr ⟨x,hi.mono (fun _ h=>⟨h.1,h.2.1⟩),bright,?_⟩
    cases rare
    · exact Or.inl ⟨_,quota_pos k,hi.mono fun _ h=>h.2.2.2⟩
    exact Or.inr ⟨_,quota_pos k,hi.mono fun _ h=>h.2.2.2⟩
  exact hfalse.exists.choose_spec

end
end Lax793645Proofs.Simplifications
