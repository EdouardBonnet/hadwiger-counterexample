import Lax793645Proofs.Simplifications.QueryFilteredComparison
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.StatusCharts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {b : Bool}

abbrev NominalAmounts (p : Shape) (q : Format) (d : Rates) (b : Bool) :=
  ∀ i:Messenger q,Digest p.g×Par (d (parcel b i))

def nominalPrinted (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q→Label p.b) (f : Messenger q→Flavor p.g) (m : Mixer p n)
    (x : Inputs p n (Messenger q)) : NominalAmounts p q d b :=
  fun i=>(scan p (t i) (f i) (x i),
    role p n (useAtom p (t i) (s i) (f i) (x i)),
    roll (v (parcel b i)) (Tsym m (useAtom p (t i) (s i) (f i) (x i))))

def joinPrinted (a : NominalAmounts p q d b) (r : Messenger q→F) : Amounts p q d b :=
  fun i=>(a i|>.1,a i|>.2,r i)

theorem printed_separation (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q→Label p.b) (f : Messenger q→Flavor p.g) (m : Mixer p n)
    (o : UnitType p n N) (x : Inputs p n (Messenger q)) :
    printed b v t s f m o x=joinPrinted (nominalPrinted b v t s f m x)
      (queryPValues (manager b t s f) o x) := rfl

/-- The leaf-uniform Fourier comparison for exactly the status vocabulary
used by the scalar and overlap assemblies. Charts are fixed on the leaf;
filters may use the complete sampled orientation and complete status. -/
theorem printed_status_comparison (b : Bool) (t : Tagging p (Messenger q))
    (s : Messenger q→Label p.b) (f : Messenger q→Flavor p.g)
    [DecidableEq (KeySlots p t)] (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (z : Messenger q→F) (D : Wgt (KeyCoordinates (KeySlots p t) (M*n)))
        (ψ : Wgt (Inputs p n (Messenger q))) (π : Wgt (UnitType p n (M*n))),
      IsLaw π → (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → ownPart t z (queryFromCoordinates t (M*n) x)) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      ∀ (v : Charts p n d) (F : UnitType p n (M*n)→Amounts p q d b→ℝ),
      (∀ o a,|F o a|≤1) →
      avg π (fun o=>|avg unif (fun x=>D (templateKeyCoordinates (manager b t s f) o x)*ψ x*
        F o (printed b v t s f m o x))|)≤ε := by
  haveI : Nonempty (NominalAmounts p q d b):=⟨fun _=>(0,0)⟩
  obtain ⟨δ,hδ,hcal⟩:=capped_filtered_comparison (A:=NominalAmounts p q d b)
    (manager b t s f) M hM c ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal] with n hn m hN z D ψ π hπ hcap hD hsup hFour hψ v F hF
  have hh:=hn m hN z D ψ π hπ hcap hD hsup hFour hψ (nominalPrinted b v t s f m)
    (fun o a r=>F o (joinPrinted a r)) (fun o a r=>hF o _)
  simpa only [←printed_separation] using hh

end
end Lax793645Proofs.Simplifications
