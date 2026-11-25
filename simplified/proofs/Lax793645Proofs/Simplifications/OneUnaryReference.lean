import Lax793645Proofs.Simplifications.OneTemplateConcentration
import Lax793645Proofs.Simplifications.QuadraticReferenceComparison
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UnaryQueryComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

/-- A coordinate equivalence, not a pair of independently sampled frames. -/
def oneAtomSplit (l : Tag p.g) (N : ℕ) : OneAtomKey l N≃AtomKey l N where
  toFun x e b a:=x e (if b then Sum.inl a else Sum.inr a)
  invFun x e:=Sum.elim (x e true) (x e false)
  left_inv x:=by funext e a; cases a <;> rfl
  right_inv x:=by funext e b a; cases b <;> rfl

def oneLawOmega (p : Shape) (N : ℕ) (l : Tag p.g) (q : F) : Wgt (OneAtomKey l N):=
  mapW (lawOmega p N l q) (oneAtomSplit l N).symm

def oneSolEq (v : Template.Solo p) (N : ℕ) : OneKeys v.t N≃OneAtomKey (v.t ()) N where
  toFun x:=x ()
  invFun x i:=i.rec x
  left_inv x:=by funext i; cases i; rfl
  right_inv x:=rfl

def oneDesc (v : Template.Solo p) (x : Knobs p.g n) (o : OneOrient p n N):=
  oneCallOne v () x o

theorem one_solo_coordinates (v : Template.Solo p) (x : Rack (KeySlots p v.t) N) :
    oneSolEq v N ((oneScatter v.t N).symm x)=
      (oneAtomSplit (v.t ()) N).symm (v.soloeq N ((scatter v.t N).symm x)) := by
  funext e a
  cases a <;> rfl

theorem quadratic_code_singleton {I : Type} [Fintype I] [DecidableEq I] [Subsingleton I]
    (A B : Mat I I) : quadraticGramCode A=quadraticGramCode B ↔ A=B := by
  constructor
  · intro h
    ext i j
    have hij : j=i:=Subsingleton.elim ..
    subst j
    have hh:=congrFun (congrArg Subtype.val h) (Pi.single i 1)
    change evmat A (Pi.single i 1) (Pi.single i 1)=evmat B (Pi.single i 1) (Pi.single i 1) at hh
    simpa [evmat] using hh
  · rintro rfl
    rfl

/-- For one column in each component there is only its self-value.
The familiar scalar reference law is therefore unchanged. -/
theorem quadratic_wave_singleton {I G : Type} [Fintype I] [Fintype G]
    [DecidableEq I] [DecidableEq G] (g : Route I G)
    (h : ∀ c,Subsingleton (Port g c)) (Q : GeoM g) :
    quadraticWave Q N=rackWave Q N := by
  unfold quadraticWave rackWave
  congr 1
  funext x
  apply propext
  rw [quadraticWavePart,quadratic_network_traced]
  change (∀ c,quadraticGramCode ((rackEquiv g N x c).1ᵀ*(rackEquiv g N x c).2)=
    quadraticGramCode (Q c)) ↔ _
  change (∀ c,_) ↔ (∀ c,(rackEquiv g N x c).1ᵀ*(rackEquiv g N x c).2=Q c)
  apply forall_congr'
  intro c
  letI:=h c
  exact quadratic_code_singleton _ _

theorem one_solo_read (v : Template.Solo p) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3≤N)
    (x : Knobs p.g n) (q : F) (hj : 1≤p.j)
    (h : dialed p (v.t ()) (v.f ()) x=q)
    (f : Wgt (OneAtomKey (v.t ()) N)) (hf : ∀ i,|f i|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (ownPort v.t) i)≤k) (hK : 2*k+2≤(N:ℝ)) :
    |avg (oneRaw m N) (f∘oneDesc v x)-avg (oneLawOmega p N (v.t ()) q) f|≤
      2*quadraticNetFact (ownPort v.t)*(num (Comp p.g)*(2*bp (k-N))) := by
  let g:=ownPort v.t
  let z:=fun _ : Unit=>x
  let A:=v.queryLaw z (g:=g)
  let T:=onePeek g A (N:=N)
  let u (r : Rack (KeySlots p v.t) N):=f (oneSolEq v N ((oneScatter v.t N).symm r))
  have ht o : u (T o)=f (oneDesc v x o) := by
    unfold u T A
    rw [show v.queryLaw z=(v.singleP n).left z from rfl,one_single_show,Equiv.symm_apply_apply]
    rfl
  obtain ⟨hA,hgram⟩:=v.solo_data x m q hj h
  have hR : mapW (oneRaw m N) T=quadraticStation (ownMap v.t (fun _=>q)) N := by
    rw [←hgram]
    exact one_frame_images g m hN A hA
  have hsing c : Subsingleton (Port g c):=
    ⟨fun a b=>v.own_inj c (Subsingleton.elim _ _)⟩
  have hL:=lawNu_rack (p:=p) v.t (fun _=>q) (N:=N)
  have hmean : avg (oneLawOmega p N (v.t ()) q) f=
      avg (quadraticWave (ownMap v.t (fun _=>q)) N) u := by
    rw [quadratic_wave_singleton g hsing,←hL]
    rw [oneLawOmega,mapW_avg,←v.soloprice q,mapW_avg,mapW_avg]
    apply avg_congr
    intro y _
    unfold u
    rw [one_solo_coordinates]
    simp only [Equiv.symm_apply_apply]
  have hmean' : avg (oneRaw m N) (f∘oneDesc v x)=avg (quadraticStation (ownMap v.t (fun _=>q)) N) u := by
    rw [←hR,mapW_avg]
    exact avg_congr (fun o _=>(ht o).symm)
  rw [hmean',hmean]
  exact quadratic_compare_station _ u (fun r=>hf _) k hk hK

end
end Lax793645Proofs.Simplifications
