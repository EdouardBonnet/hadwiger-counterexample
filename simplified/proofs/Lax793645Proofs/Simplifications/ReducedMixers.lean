import Lax793645Proofs.Simplifications.CycleMixerMasks
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BinaryPrescriptions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

abbrev ReducedIndex (p : Shape):=Fin p.J × Comp p.g
abbrev ReducedArray (p : Shape) (n : ℕ):=ReducedIndex p→Moment p n
abbrev ReducedDraw (p : Shape) (n : ℕ):=
  ReducedArray p n × ReducedArray p n × (Fin p.b→Mat (Fin n) (Fin n))
abbrev ReducedOne (p : Shape):=ReducedIndex p × Bool
abbrev ReducedBits (p : Shape):=ReducedOne p × Bool

def reducedMixer (d : ReducedDraw p n) : Mixer p n where
  mixL j e f:=cycleWeight e f • d.1 (j,e)
  mixR j e _:=d.2.1 (j,e)
  mixM:=d.2.2

def reducedSlot (i : ReducedOne p) : MOne p:=
  ((i.1.1,i.1.2,cycleAnchor i.1.2),i.2)

theorem reduced_slot_injective : Injective (reducedSlot (p:=p)) := by
  rintro ⟨⟨j,e⟩,b⟩ ⟨⟨j',e'⟩,b'⟩ h
  simp only [reducedSlot,Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl,rfl,_⟩,rfl⟩
  rfl

def reducedOrdered (m : Mixer p n) (i : ReducedOne p):=orderedM m (reducedSlot i)
def reducedIndexedSum (m : Mixer p n) (c : Vec (ReducedBits p)):=
  ∑ i,c i •eitherM i.2 (reducedOrdered m i.1)

/-- The expanded storage table contains only one independent L/R pair per
cycle component. It is retained as an adapter to the scalar geometry API. -/
def ReducedMixerLaw (m : Mixer p n) : Prop :=
  3≤p.g ∧
    (∀ j e f,m.mixL j e f=cycleWeight e f •m.mixL j e (cycleAnchor e)) ∧
    (∀ j e f,m.mixR j e f=m.mixR j e (cycleAnchor e))

theorem reduced_mixer_law (hg : 3≤p.g) (d : ReducedDraw p n) :
    ReducedMixerLaw (reducedMixer d) := by
  refine ⟨hg,fun j e f=>?_,fun j e f=>rfl⟩
  simp only [reducedMixer,cycle_weight_anchor hg,one_smul]

theorem reduced_ordered_drawn (hg : 3≤p.g) (d : ReducedDraw p n) (i : ReducedOne p) :
    reducedOrdered (reducedMixer d) i=if i.2 then d.1 i.1 else d.2.1 i.1 := by
  rcases i with ⟨⟨j,e⟩,b⟩
  cases b <;> simp [reducedOrdered,reducedSlot,orderedM,reducedMixer,cycle_weight_anchor hg]

def reducedBinaryGood (m : Mixer p n) : Prop :=
  ReducedMixerLaw m ∧ ∀ s t : Label p.b,s≠t→
    ∀ (c : Vec (ReducedBits p)) (b : Vec Bool),c≠0 ∨ b≠0→
      n≤5*blockRank Block.sharp s t (reducedIndexedSum m c+selfSum m b)

/-- Expand one set of independent prescribed bits along the cycle matchings. -/
def reducedScript {I : Type} (s : Script p I) : Script p I:=fun x y i=>
  if i.2 then cycleWeight i.1.2.1 i.1.2.2*s x y ((i.1.1,i.1.2.1,cycleAnchor i.1.2.1),true)
  else s x y ((i.1.1,i.1.2.1,cycleAnchor i.1.2.1),false)

theorem reduced_script_slot {I : Type} (hg : 3≤p.g) (s : Script p I) (x y : I)
    (i : ReducedOne p) : reducedScript s x y (reducedSlot i)=s x y (reducedSlot i) := by
  rcases i with ⟨⟨j,e⟩,b⟩
  cases b <;> simp [reducedScript,reducedSlot,cycle_weight_anchor hg]

theorem reduced_script_idempotent {I : Type} (hg : 3≤p.g) (s : Script p I) :
    reducedScript (reducedScript s)=reducedScript s := by
  funext x y i
  rcases i with ⟨⟨j,e,f⟩,b⟩
  cases b <;> simp [reducedScript,cycle_weight_anchor hg]

theorem reduced_ordered_law (m : Mixer p n) (hm : ReducedMixerLaw m) (i : MOne p) :
    orderedM m i=if i.2 then cycleWeight i.1.2.1 i.1.2.2 •
      reducedOrdered m ((i.1.1,i.1.2.1),true)
    else reducedOrdered m ((i.1.1,i.1.2.1),false) := by
  rcases i with ⟨⟨j,e,f⟩,b⟩
  cases b
  · exact hm.2.2 j e f
  exact hm.2.1 j e f

theorem reduced_reads_iff {I : Type} [Fintype I] (v : Volley p n I)
    (s : Script p I) (m : Mixer p n) (hm : ReducedMixerLaw m) :
    v.reads (reducedScript s) m ↔ ∀ x y,x≠y→v.obj x=v.obj y→∀ i:ReducedOne p,
      s x y (reducedSlot i)=evmat (reducedOrdered m i) (v.rayAt x) (v.rayAt y) := by
  constructor
  · intro h x y hxy hobj i
    simpa only [reduced_script_slot hm.1,reducedOrdered] using h x y hxy hobj (reducedSlot i)
  intro h x y hxy hobj i
  rw [reduced_ordered_law m hm i]
  rcases i with ⟨⟨j,e,f⟩,b⟩
  cases b
  · exact h x y hxy hobj ((j,e),false)
  change cycleWeight e f*s x y (reducedSlot ((j,e),true))=evmat (_ •_) _ _
  rw [h x y hxy hobj]
  simp only [←mpair_outer,mpair_smul,smul_eq_mul]

end
end Lax793645Proofs.Simplifications
