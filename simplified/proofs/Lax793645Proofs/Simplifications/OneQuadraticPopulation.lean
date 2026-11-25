import Lax793645Proofs.Simplifications.OneCommonQuadraticFit
import Lax793645Proofs.Simplifications.OneQuadraticNormalForm

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n N : ℕ}

/-- On a good population, fixed accuracy gives exact common quadratic
predictions with a construction-dependent coordinate bound and no
separate tester bit. -/
theorem one_quadratic_population (m : Mixer p n) (P : OneUnit p n N→Prop)
    (g : Bool→OneAugur p N) (u : OneUnit p n N→Bool→Profile p n)
    (α : Bool→F) (E : OneUnit p n N→Bool→Finset (Label p.b))
    (r : Bool→Tag p.g→ℕ)
    (A : ∀ i l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r i l)))
    (φ : ∀ i l,F→Vec (Fin (r i l))→F)
    (hφ : ∀ i l q x,g i l q x=φ i l q (A i l x))
    (K : ℕ) (hk : ∀ x,P x→∀ i,totalRank (u x i)≤K)
    (hP : ∃ x,P x) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r)
    (ε : ℝ) (hε : 5*ε<1/16)
    (hE : ∀ x,P x→∀ i,((E x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hfree : ∀ x,P x→∀ i s,s∉E x i→∀ l,
      Surjective ((A i l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (x i)))))
    (H : Bool→Space (OneJointKey p N))
    (hfactor : ∀ i l a b,oneJointCell (H i) a=oneJointCell (H i) b→
      A i l (oneStarKey l a)=A i l (oneStarKey l b))
    (hjoint : ∀ x,P x→∀ i s,
      Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp (H i).subtype))
    (he : ∀ x,P x→ oneClaimed x g m (u x) α (E x) ε) :
    ∃ g' : Bool→OneAugur p N,
      (∀ i,OneLinearAugur (g' i) (2*oneScreenRank p K)) ∧
      (∀ x,P x→ oneClaimed x g' m (u x) α (fun _=>∅) 0) ∧
      (∀ x,P x→∀ i,(bitSupport (testerCoefficients (u x i) (α i))).card*p.r≤
        2*oneScreenRank p K) ∧
      ∃ Q : ∀ i l,Vec (Fin (r i l))→F,
        (∀ i l,Q i l∈Stocks (Fin (r i l)) 2) ∧
        ∀ i l q x,g' i l q x=Q i l (A i l x) := by
  classical
  have hp (i : Bool) (x : OneUnit p n N) (hx : P x) (s : Label p.b)
      (hs : s∉E x i) (l : Tag p.g) (f : Flavor p.g) :
      pr (spins p n) (fun y=>φ i l (dialed p l f y)
        (A i l (oneAtomKeyValue (x i) l s (lit f l y)))≠oneYoke m x i (u x i) (α i)
          (useAtom p l s f y))≤ε := by
    have hh:=he x hx i s hs l f
    refine (pr_mono (spins_law p n).nz (fun y hy=>?_) |>.trans hh)
    change oneYoke m x i (u x i) (α i) (useAtom p l s f y)≠
      g i l (dialed p l f y) (oneAtomKeyValue (x i) l s (lit f l y))
    rw [hφ]
    exact hy.symm
  choose Q γ hQ hfit hval x0 hx0 hslice using fun i=>one_common_quadratic_fit (r i) (A i)
    (φ i) P (fun x=>x i) (fun x=>oneYoke m x i (u x i) (α i)) (fun x=>E x i)
    hP hr hn ε hε (fun x hx=>hE x hx i) (fun x hx s hs=>hfree x hx i s hs) (hp i)
  obtain ⟨g',hg',hc,hs,_,hv'⟩:=one_quadratic_population_of_forms m P u α r A K hk hg h3 hj hr hn hroom
    H hfactor hjoint Q γ hQ hval (fun i=>⟨x0 i,hx0 i,hslice i⟩)
  exact ⟨g',hg',hc,hs,Q,hQ,hv'⟩

end
end Lax793645Proofs.Simplifications
