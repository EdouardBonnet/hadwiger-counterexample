import Lax793645Proofs.Simplifications.OnePreparationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def genericRestriction (f : Flavor p.g) (l : Tag p.g) (z : Knobs p.g n) : Knobs p.g n:=
  fun b i=>if f.keeps l b then z b i else 0

theorem lit_generic_restriction (f : Flavor p.g) (l : Tag p.g) (z : Knobs p.g n) :
    lit Flavor.full l (genericRestriction f l z)=lit f l z := by
  funext i
  have hk : f.keeps l i.1→Flavor.full.keeps l i.1 := by
    cases f <;> cases i.1 <;> simp [Flavor.keeps]
  by_cases h : f.keeps l i.1
  · simp [lit,genericRestriction,h,hk h]
  · simp [lit,genericRestriction,h]

theorem dial_generic_restriction (f : Flavor p.g) (l : Tag p.g) (z : Knobs p.g n) :
    dialed p l Flavor.full (genericRestriction f l z)=dialed p l f z := by
  unfold dialed
  rw [etaScan p l (0 : Label p.b),etaScan p l (0 : Label p.b),lit_generic_restriction]

theorem one_generic_identity_all (o : OneOrient p n N) (g : OneAugur p N)
    (w : Pdual p n) (l : Tag p.g) (s : Label p.b)
    (h : ∀ y : Knobs p.g n,w (useAtom p l s Flavor.full y)=
      g l (dialed p l Flavor.full y) (oneAtomKeyValue o l s (lit Flavor.full l y))) :
    ∀ f y,w (useAtom p l s f y)=g l (dialed p l f y) (oneAtomKeyValue o l s (lit f l y)) := by
  intro f y
  have he:=h (genericRestriction f l y)
  simpa only [useAtom,lit_generic_restriction,dial_generic_restriction] using he

def oneGenericPostulates (o : OneOrient p n N) (g : OneAugur p N) (w : Pdual p n)
    (E : Finset (Label p.b)) (δ : ℝ):=
  ∀ s,s∉E→∀ l,pr (spins p n) (oneMismatch g w l s Flavor.full o)≤δ

theorem one_generic_zero_all (o : OneOrient p n N) (g : OneAugur p N)
    (w : Pdual p n) (E : Finset (Label p.b)) (h : oneGenericPostulates o g w E 0) :
    onePostulates o g w E 0 := by
  intro s hs l f
  have hid : ∀ y,w (useAtom p l s Flavor.full y)=
      g l (dialed p l Flavor.full y) (oneAtomKeyValue o l s (lit Flavor.full l y)) := by
    intro y
    by_contra he
    have hy : 0<spins p n y := by
      rw [spins]
      exact Finset.prod_pos (fun _ _=>by change 0<unif _; rw [unif_apply]; positivity)
    exact hy.not_ge ((weight_le_pr (spins_law p n).nz he).trans (h s hs l))
  have he : oneMismatch g w l s f o=(fun _=>False) := by
    funext y
    exact propext ⟨fun hn=>hn (one_generic_identity_all o g w l s hid f y),False.elim⟩
  rw [he,pr_false]
theorem one_postulates_generic (o : OneOrient p n N) (g : OneAugur p N)
    (w : Pdual p n) (E : Finset (Label p.b)) (δ : ℝ)
    (h : onePostulates o g w E δ) : oneGenericPostulates o g w E δ :=
  fun s hs l=>h s hs l Flavor.full

def oneGenericSeems (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→OneAugur p N) (z : Bool→Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) (ε : ℝ):=
  (∀ i,(L i).card≤q.B ∧ z i∈oneEffectivePins (oneEndpointPrimalPins (s.rooting x)) i) ∧
    ∀ i,oneGenericPostulates (x i) (g i) (oneYoke m x i (z i) (α i)) (L i) ε

theorem one_seems_generic (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→OneAugur p N) (z : Bool→Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) (ε : ℝ)
    (h : oneSeems q m s x g z L α ε) : oneGenericSeems q m s x g z L α ε :=
  ⟨h.1,fun i=>one_postulates_generic _ _ _ _ _ (h.2 i)⟩

theorem one_generic_seems_zero_iff (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→OneAugur p N) (z : Bool→Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) :
    oneGenericSeems q m s x g z L α 0 ↔ oneSeems q m s x g z L α 0 := by
  constructor
  · intro h
    exact ⟨h.1,fun i=>one_generic_zero_all _ _ _ _ (h.2 i)⟩
  exact one_seems_generic _ _ _ _ _ _ _ _ _

end
end Lax793645Proofs.Simplifications
