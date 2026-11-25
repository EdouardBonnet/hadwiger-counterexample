import Lax793645Proofs.Simplifications.LinearCellCoordinates
import Lax793645Proofs.Simplifications.PreparedLinearRank
import Lax793645Proofs.Simplifications.AffineFiberLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Submodule Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E U I J : Type} [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

abbrev PairedKeys (E U : Type) := E→Vec U×Vec U

def pairedDot (v x : PairedKeys E U) : F :=
  ∑ e,(dotProduct (v e).1 (x e).1+dotProduct (v e).2 (x e).2)

def pairedDotL (v : PairedKeys E U) : PairedKeys E U→ₗ[F] F where
  toFun:=pairedDot v
  map_add' x y:=by
    simp only [pairedDot,Pi.add_apply,Prod.fst_add,Prod.snd_add,dotProduct_add]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    abel
  map_smul' a x:=by
    rcases bit_cases a with h|h <;> subst a <;> simp [pairedDot]

omit [DecidableEq E] [DecidableEq U] in
theorem paired_dot_symm (v x : PairedKeys E U) : pairedDot v x=pairedDot x v := by
  simp only [pairedDot,dotProduct_comm]

theorem paired_dot_surj (f : PairedKeys E U→ₗ[F] F) :
    ∃ v,f=pairedDotL v := by
  classical
  let ins (e : E) : Vec U×Vec U→ₗ[F]PairedKeys E U:=
    LinearMap.single F (fun _ : E=>Vec U×Vec U) e
  choose u hu using fun e=>dotL_surj (f.comp ((ins e).comp (LinearMap.inl F _ _)))
  choose v hv using fun e=>dotL_surj (f.comp ((ins e).comp (LinearMap.inr F _ _)))
  refine ⟨fun e=>(u e,v e),LinearMap.ext fun x=>?_⟩
  have hh : x=∑ e,ins e (x e) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hh]
  rw [map_sum]
  change (∑ e,f (ins e (x e)))=∑ e,(dotProduct (u e) (x e).1+dotProduct (v e) (x e).2)
  apply Finset.sum_congr rfl
  intro e _
  have he : x e=((x e).1,0)+(0,(x e).2) := by simp
  conv_lhs => rw [he,map_add,map_add]
  exact congrArg₂ (·+·) (LinearMap.congr_fun (hu e) (x e).1)
    (LinearMap.congr_fun (hv e) (x e).2)

/-- Joint cells use the span of the actual frequencies. Repeated
coordinates in different tag stars do not create extra dimensions. -/
def jointCell (H : Space (PairedKeys E U)) :
    PairedKeys E U→ₗ[F]Module.Dual F H where
  toFun x:=(pairedDotL x).comp H.subtype
  map_add' x y:=by
    apply LinearMap.ext
    intro v
    change pairedDot (x+y) v.val=pairedDot x v.val+pairedDot y v.val
    rw [paired_dot_symm,paired_dot_symm x,paired_dot_symm y]
    exact (pairedDotL v.val).map_add x y
  map_smul' a x:=by
    rcases bit_cases a with h|h <;> subst a <;> ext v <;> simp [pairedDotL,pairedDot]

def frameFreeKey (J₀ : Mat I J) (o : E→Mat U I×Mat U I) :
    Vec J→ₗ[F]PairedKeys E U where
  toFun z:=fun e=>((o e).1*ᵥ(J₀*ᵥz),(o e).2*ᵥ(J₀*ᵥz))
  map_add' x y:=by ext e <;> simp [Matrix.mulVec_add]
  map_smul' a x:=by
    rcases bit_cases a with h|h <;> subst a <;> ext e <;> simp

omit [DecidableEq E] [DecidableEq U] [DecidableEq I] [DecidableEq J] in
theorem paired_free_key (J₀ : Mat I J) (o : E→Mat U I×Mat U I)
    (v : PairedKeys E U) (z : Vec J) :
    pairedDot v (frameFreeKey J₀ o z)=dotProduct (mixedFrameRow J₀ v o) z := by
  simp only [pairedDot,frameFreeKey,LinearMap.coe_mk,AddHom.coe_mk,mixedFrameRow,
    sum_dotProduct,add_dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  all_goals
    conv_rhs => rw [dotProduct_comm,dotProduct_transpose_mulVec,
      dotProduct_comm,dotProduct_transpose_mulVec]

/-- Injectivity of the frequency pullback is exactly the condition
needed to prescribe every joint cell using only the free coordinates. -/
theorem joint_cell_free_surjective (J₀ : Mat I J) (o : E→Mat U I×Mat U I)
    (H : Space (PairedKeys E U))
    (h : Injective ((mixedFrameRowLinear J₀ o).comp H.subtype)) :
    Surjective ((jointCell H).comp (frameFreeKey J₀ o)) := by
  intro c
  obtain ⟨f,hf⟩:=LinearMap.dualMap_surjective_of_injective h c
  obtain ⟨z,hz⟩:=dotL_surj f
  refine ⟨z,?_⟩
  apply LinearMap.ext
  intro v
  change pairedDot (frameFreeKey J₀ o z) v.val=c v
  rw [paired_dot_symm,paired_free_key,dotProduct_comm]
  have hh:=LinearMap.congr_fun hf v
  rw [hz] at hh
  exact hh

variable {p : Shape} {N : ℕ}

def starKey (l : Tag p.g) :
    PairedKeys (Comp p.g) (Fin N)→ₗ[F]AtomKey (p:=p) l N where
  toFun x:=fun e b=>if b then (x e.val).1 else (x e.val).2
  map_add' x y:=by ext e b i; cases b <;> rfl
  map_smul' a x:=by ext e b i; cases b <;> rfl

/-- Every tag predictor factors through one common joint cell. The
frequency budget is the sum of the tag budgets, before sampling a frame. -/
theorem joint_predictor_coordinates (g : Augur p N) (R : ℕ)
    (hg : LinearAugur g R) :
    ∃ H : Space (PairedKeys (Comp p.g) (Fin N)),dim H≤p.g*R ∧
      ∃ φ : Tag p.g→F→Module.Dual F H→F,
        ∀ l q x,g l q (starKey l x)=φ l q (jointCell H x) := by
  classical
  choose A φ hφ using fun l=>linear_cells_exact (hg l)
  let L (l : Tag p.g) (j : Fin R) :=
    (LinearMap.proj j).comp ((A l).comp (starKey (N:=N) l))
  choose v hv using fun l j=>paired_dot_surj (L l j)
  let V : Tag p.g×Fin R→PairedKeys (Comp p.g) (Fin N):=fun i=>v i.1 i.2
  let H:=Submodule.span F (Set.range V)
  have hdim : dim H≤p.g*R := by
    have hh:=finrank_range_le_card (R:=F) V
    simpa only [Set.finrank,H,dim,Fintype.card_prod,Fintype.card_fin] using hh
  have hmem (l : Tag p.g) (j : Fin R) : v l j∈H:=
    Submodule.subset_span ⟨(l,j),rfl⟩
  refine ⟨H,hdim,fun l q c=>φ l q (fun j=>c ⟨v l j,hmem l j⟩),?_⟩
  intro l q x
  rw [hφ l q (starKey l x)]
  congr 1
  funext j
  change L l j x=pairedDot x (v l j)
  rw [hv l j]
  exact paired_dot_symm _ _

end
end Lax793645Proofs.Simplifications
