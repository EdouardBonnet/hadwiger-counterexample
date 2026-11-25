import Lax793645Proofs.Simplifications.OneConcentrationScales
import Lax793645Proofs.Simplifications.OneJointKeyFiberLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def oneCallOne (v : Template p I) (i : I) (x : Knobs p.g n) (o : OneOrient p n N):=
  oneAtomKeyValue o (v.t i) (v.s i) (lit (v.f i) (v.t i) x)

theorem one_single_show (v : Template p I) (z : Inputs p n I) (o : OneOrient p n N) :
    onePeek (ownPort v.t) ((v.singleP n).left z) o=
      oneScatter v.t N (fun i=>oneCallOne v i (z i) o) := by
  apply Prod.ext
  · ext a i
    change onePrimal (o i.2.val)
      (((v.singleP n).left z i.2.val)*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inl a)=_
    rw [Matrix.mulVec_single_one]
    rfl
  · ext a i
    change onePrimal (o i.2.val)
      (((v.singleP n).left z i.2.val)*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inr a)=_
    rw [Matrix.mulVec_single_one]
    rfl

theorem one_raw_variance (v : Template p I) (M : ℕ) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n) (w : I→Wgt (Knobs p.g n)),
      (∀ i, IsLaw (w i)) → (∀ i,mapW (w i) (freePart p)=unif) → Fintype.card (Row p n)+2*p.h+3≤N →
      ∀ T : Inputs p n I → OneKeys (p:=p) v.t N → ℝ, (∀ x y,|T x y|≤1) →
      let u:= oneRaw m N
      let f:= fun o => avg (prodW w) (fun z => T z (fun i => oneCallOne v i (z i) o))
      avg u (fun x => (f x-avg u f)^2) ≤ bp (-(1/4:ℝ)*n) := by
  let g := ownPort (p:=p) v.t
  filter_upwards [one_variance_calendar p M g (num Bool*num I) 1 zero_lt_one hM]
    with n hn N m w hw hz hN T hT r f
  let s := v.singleP n
  let t (x : Inputs p n I) (y : Rack (KeySlots p v.t) N) := T x ((oneScatter v.t N).symm y)
  have hf : f = oneOexpect s (prodW w) t := by
    unfold s f oneOexpect t
    simp_rw [one_single_show,Equiv.symm_apply_apply]
  have h := hn m _ s t (prodW w) (prodW_law hw) (fun x y => hT _ _) hN
    (Template.free_price v n w hw hz g (Template.own_inj v))
  rw [one_mul] at h
  rw [hf]; exact h

/-- A second moment for a fixed test controls its mean under every dominated
subprobability. Keeping the total mass here permits an arbitrary orientation filter. -/
theorem sublaw_mean_square {A : Type} [Fintype A] (ν μ f : Wgt A) (hμ : SubLaw μ)
    (H : ℝ) (hcap : ∀ x, μ x ≤ H * ν x) :
    (avg μ f - tot μ * avg ν f)^2 ≤ H * avg ν (fun x => (f x - avg ν f)^2) := by
  let d x := f x - avg ν f
  have hmean : avg μ d = avg μ f - tot μ * avg ν f := by
    dsimp only [d]; rw [avg_sub,avg_const]
  rw [←hmean]
  have hcs := avg_CS hμ.nz d (fun _ => 1)
  simp only [mul_one,one_pow,avg_const] at hcs
  apply hcs.trans
  calc
    _ ≤ avg μ (fun x => (d x)^2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ.total
        (avg_nonneg hμ.nz fun x => sq_nonneg (d x))
    _ ≤ avg (fun x => H * ν x) (fun x => (d x)^2) := avg_mono_left (fun x => sq_nonneg _) hcap
    _ = _ := by unfold avg; rw [Finset.mul_sum]; exact sum_congr rfl fun _ _ => mul_assoc ..

/-- All positions in this experiment use one endpoint. Both the nominal input
and the entire key tuple may enter the bounded test. A filter on the original
unit is applied before taking its endpoint marginal. -/
theorem one_filtered_endpoint_test (v : Template p I) (M : ℕ) (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n
      ∀ (m : Mixer p n) (w : I → Wgt (Knobs p.g n)), (∀ i, IsLaw (w i)) →
      (∀ i, mapW (w i) (freePart p) = unif) → Fintype.card (Row p n)+2*p.h+3 ≤ N →
      ∀ (ρ : Wgt (OneUnit p n N)) (i : Bool) (P : OneUnit p n N → Prop) (H : ℝ),
      IsLaw ρ → 0 ≤ H → (∀ o, mapW ρ (fun x => x i) o ≤ H * oneRaw m N o) →
      ∀ T : Inputs p n I → OneKeys (p:=p) v.t N → ℝ, (∀ z k, |T z k| ≤ 1) →
      let f o := avg (prodW w) (fun z => T z (fun j => oneCallOne v j (z j) o))
      (avg (subW ρ P) (fun x => f (x i)) - pr ρ P * avg (oneRaw m N) f)^2 ≤
        H * bp (-(1/4 : ℝ)*n) := by
  filter_upwards [one_raw_variance v M hM] with n hvar N m w hw hz hroom ρ i P H hρ hH hcap T hT
  let μ := mapW (subW ρ P) (fun x => x i)
  have hm : tot μ = pr ρ P := by simpa only [pr_true,subW_tot] using mapW_pr (subW ρ P) (fun x => x i) (fun _ => True)
  have hμ : SubLaw μ := ⟨fun _ => pr_nonneg (subW_nonneg hρ.nz P),
    hm.le.trans ((pr_le_tot hρ.nz).trans_eq hρ.total)⟩
  have hc o : μ o ≤ H * oneRaw m N o :=
    (pr_mono_left (subW_le hρ.nz P) (fun x => x i=o)).trans (hcap o)
  let f o := avg (prodW w) (fun z => T z (fun j => oneCallOne v j (z j) o))
  have ht := sublaw_mean_square (oneRaw m N) μ f hμ H hc
  rw [hm] at ht
  change (avg μ f - _ )^2 ≤ _ at ht
  rw [show avg μ f = avg (subW ρ P) (fun x => f (x i)) from mapW_avg ..] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (hvar m w hw hz hroom T hT) hH)

end
end Lax793645Proofs.Simplifications
