import Lax793645Proofs.Simplifications.OneLinearKeyPalette
import Lax793645Proofs.Simplifications.FullLinearCells

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Module Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N r s K R : ℕ} {I T : Type} [Fintype I] [DecidableEq I]

def OneFullLinearSilhouette (Y : OneSilhouette p N r) (K : ℕ) :=
  ∀ l,HasFullLinearCells (Y l) K

theorem OneFullLinearSilhouette.linear {Y : OneSilhouette p N r}
    (h : OneFullLinearSilhouette Y K) : OneLinearSilhouette Y K :=
  fun l=>(h l).hasLinearCells

theorem one_full_linear_constant (Y : ∀ l : Tag p.g,F→Fin r) :
    OneFullLinearSilhouette (fun l q (_ : OneAtomKey (p:=p) l N)=>Y l q) 0 :=
  fun l=>full_linear_cells_constant (Y l)

theorem one_full_linear_bundle [Fintype T] [DecidableEq T]
    (f : T→ℕ) (Y : ∀ t,OneSilhouette p N (f t)) (R : T→ℕ)
    (h : ∀ t,OneFullLinearSilhouette (Y t) (R t)) :
    OneFullLinearSilhouette (oneBundleY f Y) (∑ t,R t) := by
  intro l
  exact full_linear_cells_postprocess
    (full_linear_cells_bundle R (fun t=>Y t l) (fun t=>h t l))
    (fun _ x=>Fintype.equivFin _ x) (fun _=>(Fintype.equivFin _).injective)

theorem one_full_linear_duo {Y : OneSilhouette p N r} {X : OneSilhouette p N s}
    (hY : OneFullLinearSilhouette Y K) (hX : OneFullLinearSilhouette X R) :
    OneFullLinearSilhouette (oneDuoY Y X) (K+R) := by
  intro l
  let dims (b : Bool):=if b then r else s
  let f : ∀ b : Bool,F→OneAtomKey (p:=p) l N→Fin (dims b):=
    fun b=>match b with | true=>Y l | false=>X l
  let budget (b : Bool):=if b then K else R
  have hf : ∀ b,HasFullLinearCells (f b) (budget b):=by
    intro b
    cases b
    · exact hX l
    · exact hY l
  obtain ⟨a,ha,L,hL⟩:=full_linear_cells_bundle budget f hf
  have hsize : (∑ b,budget b)=K+R:=by simp [budget]
  rw [hsize] at ha
  refine ⟨a,ha,L,fun q x y=>?_⟩
  have he : oneDuoY Y X l q x=oneDuoY Y X l q y ↔
      (fun b=>f b q x)=(fun b=>f b q y):=by
    change finProdFinEquiv (Y l q x,X l q x)=finProdFinEquiv (Y l q y,X l q y) ↔ _
    rw [finProdFinEquiv.injective.eq_iff]
    constructor
    · intro h
      funext b
      cases b
      · exact congrArg Prod.snd h
      · exact congrArg Prod.fst h
    · intro h
      exact Prod.ext (congrFun h true) (congrFun h false)
  exact he.trans (hL q x y)

/-- The palette records the complete unary pieces of the tuple rows.
No nonlinear coarsening is hidden in the common partition. -/
theorem one_full_linear_key_palette (t : Tagging p I)
    (L : OneKeys t N→ₗ[F]Vec (Fin R)) :
    OneFullLinearSilhouette (oneLinearKeyPalette t L) (Fintype.card I*R) := by
  intro l
  let H (i : I) : OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin R):=
    if h:t i=l then h ▸ (L.comp (oneKeySingle t i)) else 0
  have hi (i : I) : HasFullLinearCells (fun (_ : F) x=>H i x) R:=by
    simpa only [dim_vec,Fintype.card_fin] using full_linear_cells_map (Q:=F) (H i)
  have hh:=full_linear_cells_postprocess
    (full_linear_cells_bundle (fun _ : I=>R) (fun i (_ : F) x=>H i x) hi)
    (fun _ x=>Fintype.equivFin (I→Vec (Fin R)) x)
    (fun _=>(Fintype.equivFin _).injective)
  have he : (fun (q : F) (x : OneAtomKey (p:=p) l N)=>
      Fintype.equivFin (I→Vec (Fin R)) (fun i=>H i x))=
      oneLinearKeyPalette t L l:=by
    funext q x
    congr 1
    funext i
    dsimp only [H,oneLinearKeyPalette]
    by_cases h:t i=l
    · subst l
      simp only [dif_pos rfl]
      rfl
    · simp only [dif_neg h,LinearMap.zero_apply]
  rw [he] at hh
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hh

end
end Lax793645Proofs.Simplifications
