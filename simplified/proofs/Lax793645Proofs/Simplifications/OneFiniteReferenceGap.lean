import Lax793645Proofs.Simplifications.OneFinitePredictionClasses
import Lax793645Proofs.Simplifications.BoundedCoordinateSeparation
import Lax793645Proofs.Simplifications.OneLinearPredictorCertificates
import Lax793645Proofs.Simplifications.GramReferenceBias

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {N : ℕ}

theorem one_assembly_linear (g : Bool→OneAugur p N) (R : ℕ)
    (hg : ∀ i,OneLinearAugur (g i) R) (i j : Bool) (s t : F) :
    OneLinearAugur (oneAssembly g i j s t) (2*R) := by
  intro l
  have hh:=linear_cells_bundle (fun _ : Bool=>R) (fun i=>g i l) (fun i=>hg i l)
  have ht:=linear_cells_postprocess hh (fun (_ : F) z=>s*z i+t*z j)
  change HasLinearCells (fun q x=>s*g i l q x+t*g j l q x) (2*R)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,
    Nat.cast_ofNat,oneAssembly] using ht

def oneUnaryCoordinates (l : Tag p.g) (N : ℕ) :
    KeyCoordinates (TagStar l) N≃ₗ[F]OneAtomKey l N where
  toFun x e:=Sum.elim (fun u=>x (u,false,e)) (fun u=>x (u,true,e))
  invFun x a:=x a.2.2 (if a.2.1 then Sum.inr a.1 else Sum.inl a.1)
  left_inv x:=by funext a; rcases a with ⟨u,b,e⟩; cases b <;> rfl
  right_inv x:=by funext e u; cases u <;> rfl
  map_add' x y:=by funext e u; cases u <;> rfl
  map_smul' c x:=by funext e u; cases u <;> rfl

def oneUnaryRail (l : Tag p.g) : Rail (TagStar l) := by
  classical
  exact univ.filter (fun x=>x.1=x.2)

theorem one_unary_gram (l : Tag p.g) (q : F) (x : KeyCoordinates (TagStar l) N) :
    gramKeySet (oneUnaryRail l) (fun _=>q) N x ↔
      ownOne p l q (oneAtomSplit l N (oneUnaryCoordinates l N x)) := by
  classical
  constructor
  · intro h e
    have hh:=congrFun h (⟨(e,e),by simp [oneUnaryRail]⟩)
    exact hh
  · intro h
    funext e
    have he : e.val.1=e.val.2:=(mem_filter.mp e.property).2
    change (∑ u,keyPlus x u e.val.1*keyMinus x u e.val.2)=q
    rw [←he]
    exact h e.val.1

theorem one_unary_reference_coordinates (l : Tag p.g) (q : F) :
    mapW (oneLawOmega p N l q) (oneUnaryCoordinates l N).symm=
      unifOn (gramKeySet (oneUnaryRail l) (fun _=>q) N) := by
  classical
  let C:=(oneAtomSplit l N).symm.trans (oneUnaryCoordinates l N).symm.toEquiv
  let K:=gramKeySet (oneUnaryRail l) (fun _=>q) N
  have he : ownOne p l q=(fun x=>K (C x)) := by
    funext x
    apply propext
    have hh:=one_unary_gram l q (C x)
    have hc : oneUnaryCoordinates l N (C x)=(oneAtomSplit l N).symm x := by
      change oneUnaryCoordinates l N ((oneUnaryCoordinates l N).symm
        ((oneAtomSplit l N).symm x))=_
      exact LinearEquiv.apply_symm_apply _ _
    rw [hc,Equiv.apply_symm_apply] at hh
    exact hh.symm
  rw [oneLawOmega,mapW_nested,lawOmega,he]
  exact on_equiv C K

/-- A fixed row bound gives a common positive mass to every attained
predictor value. The threshold on the dimension is uniform over the maps. -/
theorem one_attained_cell_calendar (p : Shape) (M R : ℕ) (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Type) (l : Tag p.g)
      (Y : F → OneAtomKey (p:=p) l (M*n) → A), HasLinearCells Y R →
      ∀ q x, bp (-(R:ℝ))/2 ≤ mapW (oneLawOmega p (M*n) l q) (Y q) (Y q x) := by
  classical
  have hv : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    have hpos : 0<(M:ℝ)/2:=div_pos (by exact_mod_cast (by omega : 0<M)) (by norm_num)
    convert (bp_tendsto_zero hpos).comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  have hcal (l : Tag p.g) : ∀ᶠ n : ℕ in atTop,
      bp (-((M*n:ℕ):ℝ)/2)≤bp (-num (oneUnaryRail l))/2 ∧
      2*bp (num (oneUnaryRail l))*bp (-((M*n:ℕ):ℝ)/2)≤bp (-(R:ℝ))/2 := by
    have ht : Tendsto (fun n : ℕ=>2*bp (num (oneUnaryRail l))*
        bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
      simpa using hv.const_mul (2*bp (num (oneUnaryRail l)))
    filter_upwards [hv.eventually (eventually_le_nhds (half_pos (bp_pos _))),
      ht.eventually (eventually_le_nhds (half_pos (bp_pos _)))] with n hn hm
    exact ⟨hn,hm⟩
  filter_upwards [eventually_all.mpr hcal] with n hn A l Y hY q x
  let C := oneUnaryCoordinates (p:=p) l (M*n)
  let ν := unifOn (gramKeySet (oneUnaryRail (p:=p) l) (fun _=>q) (M*n))
  obtain ⟨hν,_,hbias⟩ := gram_reference_bias (oneUnaryRail (p:=p) l) (fun _=>q) (hn l).1
  have h := attained_coordinate_mass ν hν R _
    (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) (hn l).2 hbias
    (fun q y => Y q (C y)) (linear_cells_precompose hY C.toLinearMap) q (C.symm x)
  rw [show ν = mapW (oneLawOmega p (M*n) l q) C.symm from
    (one_unary_reference_coordinates l q).symm,mapW_nested] at h
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using h

/-- The separation threshold depends only on the fixed number of
predictor coordinates. No scalar limits enter its choice. -/
theorem one_reference_separation_calendar (p : Shape) (M R : ℕ) (hM : 1≤M) :
    ∃ τ : ℝ,0<τ ∧ ∀ᶠ n : ℕ in atTop,∀ (g : OneAugur p (M*n)),
      OneLinearAugur g R→∀ r : F,
      (∀ l q,oneTabRef p l q g r≤τ)→ oneLiteral g r := by
  classical
  let τ:=bp (-(R:ℝ))/4
  have hτ : 0<τ:=div_pos (bp_pos _) (by norm_num)
  refine ⟨τ,hτ,?_⟩
  have hv : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    have hpos : 0<(M:ℝ)/2:=div_pos (by exact_mod_cast (by omega : 0<M)) (by norm_num)
    convert (bp_tendsto_zero hpos).comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  have hcal (l : Tag p.g) : ∀ᶠ n : ℕ in atTop,
      bp (-((M*n:ℕ):ℝ)/2)≤bp (-num (oneUnaryRail l))/2 ∧
      2*bp (num (oneUnaryRail l))*bp (-((M*n:ℕ):ℝ)/2)≤bp (-(R:ℝ))/2 := by
    have ht : Tendsto (fun n : ℕ=>2*bp (num (oneUnaryRail l))*
        bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
      simpa using hv.const_mul (2*bp (num (oneUnaryRail l)))
    filter_upwards [hv.eventually (eventually_le_nhds (half_pos (bp_pos _))),
      ht.eventually (eventually_le_nhds (half_pos (bp_pos _)))] with n hn hm
    exact ⟨hn,hm⟩
  filter_upwards [eventually_all.mpr hcal] with n hn g hg r he l q x
  let E:=oneUnaryRail l
  let ν:=unifOn (gramKeySet E (fun _=>q) (M*n))
  let C:=oneUnaryCoordinates l (M*n)
  obtain ⟨hν,_,hbias⟩:=gram_reference_bias E (fun _=>q) (hn l).1
  have hlin:=linear_cells_precompose (hg l) C.toLinearMap
  have hpr : pr ν (fun y=>g l q (C y)≠r*q)≤τ := by
    rw [show ν=mapW (oneLawOmega p (M*n) l q) C.symm from
      (one_unary_reference_coordinates l q).symm,mapW_pr]
    simpa only [C,LinearEquiv.apply_symm_apply,oneTabRef] using he l q
  have hval:=bounded_coordinate_separation ν hν R
    (2*bp (num E)*bp (-((M*n:ℕ):ℝ)/2)) τ
    (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) (hn l).2
    (by dsimp only [τ]; linarith only [bp_pos (-(R:ℝ))]) hbias
    (fun q y=>g l q (C y)) hlin q (r*q) hpr (C.symm x)
  simpa only [LinearEquiv.apply_symm_apply] using hval

end
end Lax793645Proofs.Simplifications
