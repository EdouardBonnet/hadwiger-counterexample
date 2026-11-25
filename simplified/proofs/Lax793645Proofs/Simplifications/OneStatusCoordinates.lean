import Lax793645Proofs.Simplifications.OneStatusQuadratics
import Lax793645Proofs.Simplifications.OneStatusCharts
import Lax793645Proofs.Simplifications.OneQueryCellRecentring
import Lax793645Proofs.Simplifications.ConditionalStatusSupports

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis LinearMap Module Matrix Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem linear_map_cells {V W Q : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (L : V→ₗ[F]W) :
    HasLinearCells (fun (_ : Q) x=>L x) (dim W) := by
  let E:W≃ₗ[F]Vec (Fin (dim W)):=(Module.finBasis F W).equivFun
  exact ⟨dim W,le_rfl,E.toLinearMap.comp L,fun _ x=>E.symm x,
    fun _ x=>(E.symm_apply_apply (L x)).symm⟩

theorem linear_cells_pair {V Q A B : Type} [AddCommGroup V] [Module F V]
    {f : Q→V→A} {g : Q→V→B} {R S : ℕ}
    (hf : HasLinearCells f R) (hg : HasLinearCells g S) :
    HasLinearCells (fun q x=>(f q x,g q x)) (R+S) := by
  obtain ⟨L,φ,hφ⟩:=linear_cells_exact hf
  obtain ⟨M,ψ,hψ⟩:=linear_cells_exact hg
  have h:=linear_cells_postprocess (linear_map_cells (Q:=Q) (L.prod M))
    (fun q z=>(φ q z.1,ψ q z.2))
  simpa only [Module.finrank_prod,dim_vec,Fintype.card_fin,LinearMap.prod_apply,
    Function.prod,←hφ,←hψ] using h

variable {p : Shape} {n N d : ℕ}

def punchLinear (p : Shape) (n : ℕ) : Knobs p.g n→ₗ[F]Tickets p where
  toFun:=punchField p
  map_add' x y:=by
    ext i
    change zget (x (asBlock i.1.1)+y (asBlock i.1.1)) (gaugeAddr p i)=
      zget (x (asBlock i.1.1)) (gaugeAddr p i)+zget (y (asBlock i.1.1)) (gaugeAddr p i)
    unfold zget
    split_ifs <;> rfl
  map_smul' a x:=by
    ext i
    change zget (a • x (asBlock i.1.1)) (gaugeAddr p i)=a*zget (x (asBlock i.1.1)) (gaugeAddr p i)
    unfold zget
    split_ifs <;> simp

def scanFromPunch (p : Shape) (l : Tag p.g) (f : Flavor p.g) (z : Tickets p) :
    Digest p.g := fun i=>if f.keeps l (asBlock i) then
      ∑ j : Fin p.r,z ((i,j),true)*z ((i,j),false) else 0

theorem scan_from_punch (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :
    scan p l f x=scanFromPunch p l f (punchField p x) := by
  rfl

def testerFromScan (p : Shape) (l : Tag p.g) (a : Profile p n) (z : Digest p.g) : F :=
  role p n a*z.diagO+
    ∑ t : Tag p.g,(roleT p n t a*(z (.inr ())+(if l=t then z (.inr ()) else 0))+
      sharedT p n t a*∑ u : Tag p.g,z (.inl (u,t)))

theorem tester_from_scan (hg : Odd p.g) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (a : Profile p n) (x : Knobs p.g n) :
    T0 p n a (useAtom p l s f x)=testerFromScan p l a (scan p l f x) := by
  simp only [T0_val,role_scan,roleT_scan,sharedT_scan p hg,testerFromScan]

/-- This budget records the tester coordinates once, then two factors
for each basis quadratic and for the internal status bit. -/
def oneStatusCoordinateBound (p : Shape) (d K : ℕ) : ℕ :=
  Fintype.card (Gauge p)+d*(2*(p.J*tagDegree p.g*(2*K)))+
    2*(tagDegree p.g*(2*p.h))

theorem one_status_coordinates (hg : Odd p.g) (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : OneUnit p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (K : ℕ)
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K) :
    HasLinearCells (fun (_ : Unit) x=>oneSpecify p i v m o l s f x)
      (oneStatusCoordinateBound p d K) := by
  let P:=springLinear p l s f (n:=n)
  let k:=spring p l s f (0 : Knobs p.g n)
  have hs (x : Knobs p.g n) : P x+k=spring p l s f x:=sub_add_cancel ..
  let mix (x : Knobs p.g n) (j : Fin d):=
    evmat (qmix m (v (Pi.single j 1)) l) (spring p l s f x) (spring p l s f x)
  have hm (j : Fin d) : HasLinearCells (fun (_ : Unit) x=>mix x j)
      (2*(p.J*tagDegree p.g*(2*K))) := by
    have hr: (qmix m (v (Pi.single j 1)) l).rank≤p.J*tagDegree p.g*(2*K):=
      (qmix_rank ..).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (hv j)))
    simpa only [hs,add_zero] using affine_matrix_linear_cells
      (Q:=Unit) (qmix m (v (Pi.single j 1)) l) P k 0 _ hr
  have hmix: HasLinearCells (fun (_ : Unit) x=>mix x)
      (d*(2*(p.J*tagDegree p.g*(2*K)))) := by
    simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] using
      linear_cells_bundle (fun _ : Fin d=>2*(p.J*tagDegree p.g*(2*K)))
        (fun j (_ : Unit) x=>mix x j) hm
  have hpunch: HasLinearCells (fun (_ : Unit) (x : Knobs p.g n)=>punchField p x)
      (Fintype.card (Gauge p)) := by
    simpa only [Tickets,dim_vec,punchLinear,LinearMap.coe_mk,AddHom.coe_mk] using
      linear_map_cells (Q:=Unit) (punchLinear p n)
  obtain ⟨M,hM,he⟩:=one_inner_gem o i l
  have hp: HasLinearCells (fun (_ : Unit) x=>oneInner o i (useAtom p l s f x))
      (2*(tagDegree p.g*(2*p.h))) := by
    have hx (x : Knobs p.g n): oneInner o i (useAtom p l s f x)=
        evmat M (P x+k) (P x+k):=by
      rw [useAtom,he,mom,mpair_outer,hs]
      rfl
    simpa only [add_zero,←hx] using affine_matrix_linear_cells (Q:=Unit) M P k 0 _ hM
  have hc:=linear_cells_pair (linear_cells_pair hpunch hmix) hp
  let decode (z : (Tickets p×Cell d)×F) : Magazine p d :=
    let a:=scanFromPunch p l f z.1.1
    (a,(a.diagO,fun j=>testerFromScan p l (v (Pi.single j 1)) a+z.1.2 j),z.2)
  have hd (x : Knobs p.g n): oneSpecify p i v m o l s f x=
      decode ((punchField p x,mix x),oneInner o i (useAtom p l s f x)) := by
    dsimp only [oneSpecify,decode]
    rw [←scan_from_punch,role_scan]
    congr 3
    funext j
    unfold roll
    rw [T_swap]
    change T0 p n _ _+Tmix m _ _=_
    rw [tester_from_scan hg,useAtom,Tmix_atom,mom,mpair_outer]
    rfl
  simpa only [←hd,oneStatusCoordinateBound] using
    linear_cells_postprocess hc (fun (_ : Unit) z=>decode z)

end
end Lax793645Proofs.Simplifications
