import Lax793645Proofs.Simplifications.OnePredictorLabelExtension

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N : ℕ} {T : Type}

/-- One fixed-accuracy fit supplies common quadratic polynomials for
an entire population. The identities hold at every point and every label;
only one constant tester slope per tag remains at this stage. -/
theorem one_common_quadratic_fit (r : Tag p.g→ℕ)
    (A : ∀ l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r l)))
    (φ : ∀ l,F→Vec (Fin (r l))→F) (P : T→Prop)
    (o : T→OneOrient p n N) (w : T→Pdual p n) (E : T→Finset (Label p.b))
    (hP : ∃ t,P t) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (ε : ℝ) (hε : 5*ε<1/16)
    (hE : ∀ t,P t→((E t).card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hfree : ∀ t,P t→∀ s,s∉E t→∀ l,
      Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (o t)))))
    (he : ∀ t,P t→∀ s,s∉E t→∀ l f,
      pr (spins p n) (fun x=>φ l (dialed p l f x)
        (A l (oneAtomKeyValue (o t) l s (lit f l x)))≠w t (useAtom p l s f x))≤ε) :
    ∃ (Q : ∀ l,Vec (Fin (r l))→F) (γ : Tag p.g→F),
      (∀ l,Q l∈Stocks (Fin (r l)) 2) ∧
      (∀ l d,pr unif (fun c=>φ l d c≠Q l c+γ l*d)≤4*ε) ∧
      (∀ t,P t→∀ l s f x,w t (useAtom p l s f x)=
        Q l (A l (oneAtomKeyValue (o t) l s (lit f l x)))+γ l*dialed p l f x) ∧
      ∃ t,P t ∧ ∀ l,∃ (s : Label p.b) (y : Knobs p.g n)
        (S : Vec (Fin (r l))→ₗ[F]Vec (Fin n)),
          Q l=(fun c=>w t (useAtom p l s Flavor.full (y+freeKnob p n (S c)))) := by
  classical
  obtain ⟨t0,ht0⟩:=hP
  have hcard : (E t0).card<Fintype.card (Label p.b) := by
    have hb := (hE t0 ht0).trans_le (bp_le (show (p.b:ℝ)-2*p.j≤p.b by
      have hh : 0≤(p.j:ℝ):=Nat.cast_nonneg _
      linarith only [hh]))
    have hc : bp (p.b:ℝ)=(Fintype.card (Label p.b):ℝ) := by
      simp [Label,F,bp_nat,ZMod.card]
    rw [hc] at hb
    exact_mod_cast hb
  obtain ⟨s0,hs0⟩ : ∃ s,s∉E t0 := by
    by_contra! hh
    have hc:=card_le_card (show univ⊆E t0 from fun s _=>hh s)
    rw [card_univ] at hc
    omega
  choose Q γ hQ hv hfit hslice using fun l=>one_affine_cell_fit l (A l) (o t0) s0 Flavor.full
    (hfree t0 ht0 s0 hs0 l) (w t0) (φ l) hr hn ε hε (he t0 ht0 s0 hs0 l Flavor.full)
  refine ⟨Q,γ,hQ,hfit,?_,t0,ht0,fun l=>⟨s0,hslice l⟩⟩
  intro t ht l s f x
  apply one_predictor_label_extension l (A l) (o t) (w t) (Q l) (hQ l) (γ l) (E t) (hE t ht) f x
  intro u hu
  exact one_affine_cell_transfer l (A l) (o t) u f (hfree t ht u hu l) (w t) (φ l)
    (Q l) (hQ l) (γ l) ε (by linarith only [hε]) (hfit l) (he t ht u hu l f) x

end
end Lax793645Proofs.Simplifications
