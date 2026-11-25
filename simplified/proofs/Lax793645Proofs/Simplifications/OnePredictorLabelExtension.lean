import Lax793645Proofs.Simplifications.OneAffineCellFit

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Submodule Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {p : Shape} {n N r : ℕ}

theorem point_selector_polynomial (z : Base p.g n) (i : Row p n) :
    (fun s=>point p s z i)∈Stocks (Fin p.b) p.j := by
  rcases i with ⟨a,b⟩
  have he : (fun s=>point p s z (a,b))=baseV z b • poly1 a.val := by
    funext s
    exact mul_comm _ _
  rw [he]
  exact Submodule.smul_mem _ _ (subset_span ⟨a.val,a.property,rfl⟩)

theorem atom_selector_polynomial (w : Pdual p n) (l : Tag p.g) (z : Base p.g n) :
    (fun s=>w (atom p l s z))∈Stocks (Fin p.b) (2*p.j) := by
  let L := w.comp ((cut p n).comp (LinearMap.single F (fun _ : Tag p.g=>Moment p n) l))
  exact pointPoly L (fun s=>point p s z) p.j (point_selector_polynomial z)

theorem key_selector_polynomial (l : Tag p.g) (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r))
    (o : OneOrient p n N) (z : Base p.g n) (Q : Vec (Fin r)→F)
    (hQ : Q∈Stocks (Fin r) 2) :
    (fun s=>Q (A (oneAtomKeyValue o l s z)))∈Stocks (Fin p.b) (2*p.j) := by
  let L:=A.comp ((oneStarKey l).comp (onePrimalKey o))
  apply polynomial_degree_substitution 2 p.j Q hQ
  intro i
  have hh:=polynomial_degree_substitution 1 p.j (fun v=>L v i)
    (linear_coordinate_stocks L i) (fun s=>point p s z) (point_selector_polynomial z)
  rw [Nat.one_mul] at hh
  exact hh

/-- Once predictions are identities on the allowed labels, the Boolean
minimum-weight bound extends them to every excluded label as well. -/
theorem one_predictor_label_extension (l : Tag p.g)
    (A : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin r)) (o : OneOrient p n N)
    (w : Pdual p n) (Q : Vec (Fin r)→F) (hQ : Q∈Stocks (Fin r) 2)
    (γ : F) (E : Finset (Label p.b)) (hE : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (f : Flavor p.g) (x : Knobs p.g n)
    (he : ∀ s,s∉E→w (useAtom p l s f x)=
      Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x) :
    ∀ s,w (useAtom p l s f x)=Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x := by
  let F:=fun s=>w (useAtom p l s f x)-
    (Q (A (oneAtomKeyValue o l s (lit f l x)))+γ*dialed p l f x)
  have hF : F∈Stocks (Fin p.b) (2*p.j) := Submodule.sub_mem _
    (atom_selector_polynomial w l (lit f l x))
    (Submodule.add_mem _ (key_selector_polynomial l A o (lit f l x) Q hQ)
      (stocks_one _ _ _))
  have hb : (E.card:ℝ)<bp ((Fintype.card (Fin p.b):ℝ)-(2*p.j:ℕ)) := by
    simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hE
  have hh:=polynomial_vanish_outside (2*p.j) F hF E hb
    (fun s hs=>sub_eq_zero.mpr (he s hs))
  exact fun s=>sub_eq_zero.mp (hh s)

end
end Lax793645Proofs.Simplifications
