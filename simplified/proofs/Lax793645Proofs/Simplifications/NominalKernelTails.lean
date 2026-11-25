import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GroupedQueryIndependence
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J U W : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype W]
  [DecidableEq I] [DecidableEq J] [DecidableEq U] [DecidableEq W]

omit [Fintype U] [Fintype W] [DecidableEq I] [DecidableEq U] [DecidableEq W] in
/-- Projecting to independent free coordinates controls the entire kernel,
not just the event that a first dependence appears. -/
theorem projected_kernel_dimension (P : Mat W I) (V : Mat U J) (b : I→J)
    (hb : Injective b) (h : ∀ x,P*ᵥx=0→V*ᵥ((embedMat b)*ᵥx)=0) :
    Fintype.card I-P.rank≤Fintype.card J-V.rank := by
  let S := LinearMap.ker P.mulVecLin
  let T := LinearMap.ker V.mulVecLin
  let f := (embedMat b).mulVecLin
  let g : S→ₗ[F] T := (f.comp S.subtype).codRestrict T (fun x=>h x.val x.property)
  have hi : Injective g := by
    intro x y he
    apply Subtype.ext
    exact (embedMat_inj hb) (congrArg Subtype.val he)
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have hp := P.mulVecLin.finrank_range_add_finrank_ker
  have hv := V.mulVecLin.finrank_range_add_finrank_ker
  change P.rank+dim S=dim (Vec I) at hp
  change V.rank+dim T=dim (Vec J) at hv
  change dim S≤dim T at hd
  rw [dim_vec] at hp hv
  omega

variable {p : Shape} {n : ℕ}

omit [DecidableEq I] in
theorem ray_kernel_dimension {G : Type} [Fintype G] [DecidableEq G] {f : Route I G} {b : I→J}
    {A : NomQuery p n f} (e : G) (V : PlusRack J n)
    (hb : Injective (fun i : Port f e=>b i.val))
    (hm : ∀ i : Port f e,∀ j : Fin n,A e (emptySel,some (Block.Z,j)) i=V j (b i.val)) :
    Fintype.card (Port f e)-(A e).rank≤Fintype.card J-V.rank := by
  classical
  apply projected_kernel_dimension (A e) V (fun i=>b i.val) hb
  intro x hx
  funext j
  have hh := congr_fun hx (emptySel,some (Block.Z,j))
  change ∑ i:Port f e,A e (emptySel,some (Block.Z,j)) i*x i=0 at hh
  simp_rw [hm] at hh
  rw [Matrix.mulVec_mulVec,mul_embedMat]
  exact hh

/-- Arbitrarily deep nominal rank deficiencies have the full exponential
tail under the original independent input law. No batches are discarded. -/
theorem free_nominal_kernel_tail {T : Type} [Fintype T] [DecidableEq T]
    (p : Shape) (n : ℕ) (w : I→Wgt (Knobs p.g n))
    (hw : ∀ i,mapW (w i) (freePart p)=unif) (d : ℕ) :
    pr (draws T (prodW w)) (fun x=> (freeNet p x).rank+d≤Fintype.card (T×I))≤
      bp ((num T*num I-n)*d) := by
  rw [show pr _ _=pr (mapW (draws T (prodW w)) (freeNet p))
    (fun M : PlusRack (T×I) n=>M.rank+d≤Fintype.card (T×I)) from (mapW_pr ..).symm,
      law_probes p n w hw]
  simpa only [num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using
    pr_deficient (I:=Fin n) (J:=T×I) d

/-- The nominal arrays of the actual query template inherit the same
kernel-dimension bound from their constant-selector Z coordinates. -/
theorem query_kernel_dimension {T G : Type} [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] (v : Template p I)
    (x : T→Inputs p n I) (g : Route (KeySlots p v.t) G)
    (he : ∀ e : G,Injective (fun i : Port g e=>i.val.1)) (e : G) :
    Fintype.card (Port (tied g T) e)-
      (pooled (fun i=>v.queryLaw (x i) (g:=g)) e).rank≤
        Fintype.card (T×I)-(freeNet p x).rank := by
  classical
  let r : T×KeySlots p v.t→T×I := fun y=>(y.1,y.2.1)
  have hr : Injective (fun a : Port (tied g T) e=>r a.val) := by
    rintro ⟨⟨j,a⟩,ha⟩ ⟨⟨j',b⟩,hb⟩ h
    have hA : j=j' := congrArg Prod.fst h
    have hK : a=b := congrArg Subtype.val (he e (show
      (⟨a,ha⟩ : Port g e).val.1=(⟨b,hb⟩ : Port g e).val.1 from congrArg Prod.snd h))
    exact Subtype.ext (Prod.ext hA hK)
  apply ray_kernel_dimension (b:=r) e (freeNet p x) hr
  intro a j
  change point p _ _ (emptySel,some (Block.Z,j))=freeNet p x j (a.val.1,a.val.2.1)
  rw [point_base_eval]
  exact if_pos (Flavor.keepZ _ _)

/-- Large nominal deficiencies anywhere in a fixed query family have a
raw exponentially small tail, with all original batches still present. -/
theorem query_nominal_kernel_tail {T G : Type} [Fintype T] [DecidableEq T]
    [Fintype G] [DecidableEq G] (v : Template p I)
    (g : Route (KeySlots p v.t) G)
    (he : ∀ e : G,Injective (fun i : Port g e=>i.val.1))
    (w : I→Wgt (Knobs p.g n)) (hl : ∀ i,IsLaw (w i))
    (hw : ∀ i,mapW (w i) (freePart p)=unif) (d : ℕ) :
    pr (draws T (prodW w)) (fun x=>∃ e,
      (pooled (fun i=>v.queryLaw (x i) (g:=g)) e).rank+d≤
        Fintype.card (Port (tied g T) e))≤bp ((num T*num I-n)*d) := by
  have hm : ∀ x,0≤draws T (prodW w) x := (draws_law (prodW_law hl)).nz
  refine (pr_mono hm ?_).trans (free_nominal_kernel_tail p n w hw d)
  intro x hx
  obtain ⟨e,he'⟩ := hx
  have hh := query_kernel_dimension v x g he e
  have hr := (freeNet p x).rank_le_card_width
  omega

end
end Lax793645Proofs.Simplifications
