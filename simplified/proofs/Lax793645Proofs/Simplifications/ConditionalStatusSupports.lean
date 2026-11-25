import Lax793645Proofs.Simplifications.QuadraticCoordinateBound
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C W V S : Type} [AddCommGroup C] [Module F C]
  [AddCommGroup W] [Module F W] [Fintype W]
  [AddCommGroup V] [Module F V] [Fintype V]

/-- Status probabilities after an affine change of variables making the
common coordinates independent of the remaining uniform input. -/
def conditionalStatus (A : C→ₗ[F]V) (B : W→ₗ[F]V) (d : V) (f : V→S)
    (s : S) (c : C) : ℝ:=pr unif (fun w=>f (A c+B w+d)=s)

/-- A possible status has probability at least one atom of the uniform
law on the image of B. The bound uses the status dimension, not the
number of common coordinates. -/
theorem conditional_status_gap (A : C→ₗ[F]V) (B : W→ₗ[F]V) (d : V) (f : V→S)
    (s : S) (c : C) (h : 0<conditionalStatus A B d f s c) :
    bp (-(dim V:ℝ))≤conditionalStatus A B d f s c := by
  obtain ⟨w,hw,_⟩:=exists_of_pr_pos unif_law.nz h
  have hp:=pr_unif_lin B (B w)
  rw [ind_one (show B w∈range B from ⟨w,rfl⟩),one_mul] at hp
  have hr : rk B≤dim V:=Submodule.finrank_le _
  have hr' : (rk B:ℝ)≤dim V:=by exact_mod_cast hr
  exact (bp_le (by linarith only [hr'])).trans
    (hp.symm.le.trans (pr_mono unif_law.nz (fun z hz=>by
      rw [hz]
      exact hw)))

omit [Fintype V] in
/-- Two common cells differing by a vector absorbed in the free input
have identical conditional status distributions. -/
theorem conditional_status_equal (A : C→ₗ[F]V) (B : W→ₗ[F]V) (d : V) (f : V→S)
    (s : S) (c c' : C) (h : A c'-A c∈range B) :
    conditionalStatus A B d f s c'=conditionalStatus A B d f s c := by
  obtain ⟨v,hv⟩:=h
  have hc : A c'=A c+B v:=by rw [hv]; abel
  let e : W≃W:=⟨(·+v),(·+v),add_polar v,add_polar v⟩
  unfold conditionalStatus pr
  rw [←avg_bij e unif (fun w=>ind (f (A c'+B w+d)=s))]
  apply avg_congr
  intro w _
  congr 2
  apply congrArg f
  change A c'+B (w+v)+d=A c+B w+d
  rw [hc,map_add]
  calc
    _=A c+B w+d+(B v+B v):=by abel
    _=A c+B w+d:=by rw [char_two,add_zero]

/-- The full table factors through a quotient of the status-coordinate
space. Its number of essential rows is independent of dim C. -/
theorem conditional_status_coordinates (A : C→ₗ[F]V) (B : W→ₗ[F]V)
    (d : V) (f : V→S) (s : S) :
    HasLinearCells (fun (_ : Unit) c=>conditionalStatus A B d f s c) (dim V) := by
  classical
  let Q:=V ⧸ range B
  let e:Q≃ₗ[F]Vec (Fin (Module.finrank F Q)):=(Module.finBasis F Q).equivFun
  let L:=e.toLinearMap.comp ((range B).mkQ.comp A)
  let φ (_ : Unit) (z : Vec (Fin (Module.finrank F Q))):=
    conditionalStatus (LinearMap.id : V→ₗ[F]V) B d f s (Quotient.out (e.symm z))
  refine ⟨Module.finrank F Q,?_,L,φ,?_⟩
  · exact Submodule.finrank_quotient_le _
  · intro q c
    change conditionalStatus (LinearMap.id : V→ₗ[F]V) B d f s (A c)=_
    apply conditional_status_equal
    change A c-Quotient.out (e.symm (L c))∈range B
    have he : e.symm (L c)=(range B).mkQ (A c):=by
      exact e.symm_apply_apply _
    rw [he]
    exact (Submodule.Quotient.eq _).mp (Quotient.out_eq _).symm

omit [AddCommGroup W] [Module F W] [Fintype W] [AddCommGroup V] [Module F V] [Fintype V] in
/-- The overlap gap follows from the number of essential status rows,
even when the common partition has arbitrarily many fixed rows. -/
theorem bounded_coordinate_overlap_gap [Fintype C]
    (f g ν : C→ℝ) (m : ℕ) (a : ℝ) (ha : 0≤a)
    (hf : HasLinearCells (fun (_ : Unit) c=>f c) m)
    (hg : HasLinearCells (fun (_ : Unit) c=>g c) m)
    (hf0 : ∀ c,0≤f c) (hg0 : ∀ c,0≤g c)
    (hfg : ∀ c,0<f c→a≤f c) (hgg : ∀ c,0<g c→a≤g c)
    (hν : ∀ c,unif c/2≤ν c) (c₀ : C) (hc₀ : 0<f c₀ ∧ 0<g c₀) :
    bp (-(2*m:ℕ):ℝ)*a^2/2≤avg ν (fun c=>f c*g c) := by
  classical
  let h (b : Bool) : C→ℝ:=if b then f else g
  have hh (b : Bool) : HasLinearCells (fun (_ : Unit) c=>h b c) m:=by
    cases b <;> assumption
  obtain ⟨r,hr,L,φ,hφ⟩:=linear_cells_bundle (fun _ : Bool=>m)
    (fun b (_ : Unit) c=>h b c) hh
  have hr' : r≤2*m:=by simpa using hr
  have hs c (hc : L c=L c₀) : f c=f c₀ ∧ g c=g c₀:=by
    have he := (hφ () c).trans ((congrArg (φ ()) hc).trans (hφ () c₀).symm)
    exact ⟨congrFun he true,congrFun he false⟩
  have hv0 c : 0≤ν c:=(div_nonneg (unif_law.nz c) (by norm_num)).trans (hν c)
  have hpoint c : (unif c)*(ind (L c=L c₀)*(a^2/2))≤ν c*(f c*g c) := by
    by_cases hc : L c=L c₀
    · rw [ind_one hc,one_mul]
      obtain ⟨he₁,he₂⟩:=hs c hc
      have hprod : a^2≤f c*g c:=by
        rw [he₁,he₂,pow_two]
        exact mul_le_mul (hfg c₀ hc₀.1) (hgg c₀ hc₀.2) ha (hf0 c₀)
      calc
        _=(unif c/2)*a^2:=by ring
        _≤ν c*a^2:=mul_le_mul_of_nonneg_right (hν c) (sq_nonneg a)
        _≤ν c*(f c*g c):=mul_le_mul_of_nonneg_left hprod (hv0 c)
    · rw [ind_zero hc,zero_mul,mul_zero]
      exact mul_nonneg (hv0 c) (mul_nonneg (hf0 c) (hg0 c))
  have hm : pr unif (fun c=>L c=L c₀)*(a^2/2)≤avg ν (fun c=>f c*g c):=by
    rw [pr,←avg_mul]
    exact Finset.sum_le_sum (fun c _=>hpoint c)
  have hp:=pr_unif_lin L (L c₀)
  rw [ind_one (show L c₀∈range L from ⟨c₀,rfl⟩),one_mul] at hp
  have hrL : rk L≤2*m := (Submodule.finrank_le _).trans (by simpa using hr')
  have hpr : bp (-(2*m:ℕ):ℝ)≤pr unif (fun c=>L c=L c₀):=by
    rw [hp]
    apply bp_le
    exact_mod_cast (neg_le_neg (show (rk L:ℤ)≤(2*m:ℕ) by exact_mod_cast hrL))
  exact (show bp (-(2*m:ℕ):ℝ)*a^2/2=bp (-(2*m:ℕ):ℝ)*(a^2/2) by ring).le.trans
    ((mul_le_mul_of_nonneg_right hpr (by positivity)).trans hm)

omit [AddCommGroup V] [Module F V] [Fintype V] in
/-- The proposed status-overlap dichotomy. The constant is fixed by the
status dimension, before the common-coordinate dimension is chosen. -/
theorem conditional_status_overlap_gap [Fintype C]
    {W' S' : Type} [AddCommGroup W'] [Module F W'] [Fintype W']
    (m : ℕ) (A A' : C→ₗ[F]Vec (Fin m))
    (B : W→ₗ[F]Vec (Fin m)) (B' : W'→ₗ[F]Vec (Fin m))
    (d d' : Vec (Fin m)) (f : Vec (Fin m)→S) (f' : Vec (Fin m)→S')
    (s : S) (s' : S') (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c) :
    let overlap:=avg ν (fun c=>conditionalStatus A B d f s c*conditionalStatus A' B' d' f' s' c)
    overlap=0 ∨ bp (-(4*(m:ℝ)+1))≤overlap:=by
  classical
  dsimp only
  let h:=conditionalStatus A B d f s
  let h':=conditionalStatus A' B' d' f' s'
  have hn c : 0≤h c:=pr_nonneg unif_law.nz
  have hn' c : 0≤h' c:=pr_nonneg unif_law.nz
  by_cases hex : ∃ c,0<h c ∧ 0<h' c
  · obtain ⟨c,hc⟩:=hex
    right
    have hf : HasLinearCells (fun (_ : Unit) c=>h c) m:=by
      simpa only [dim_vec,Fintype.card_fin] using conditional_status_coordinates A B d f s
    have hf' : HasLinearCells (fun (_ : Unit) c=>h' c) m:=by
      simpa only [dim_vec,Fintype.card_fin] using conditional_status_coordinates A' B' d' f' s'
    have hg c (hc : 0<h c) : bp (-(m:ℝ))≤h c:=by
      simpa only [dim_vec,Fintype.card_fin] using conditional_status_gap A B d f s c hc
    have hg' c (hc : 0<h' c) : bp (-(m:ℝ))≤h' c:=by
      simpa only [dim_vec,Fintype.card_fin] using conditional_status_gap A' B' d' f' s' c hc
    have hh:=bounded_coordinate_overlap_gap h h' ν m (bp (-(m:ℝ))) (bp_pos _).le
      hf hf' hn hn' hg hg' hν c hc
    have he : bp (-(2*m:ℕ):ℝ)*bp (-(m:ℝ))^2/2=bp (-(4*(m:ℝ)+1)):=by
      rw [pow_two,←bp_add,←bp_add,show (2:ℝ)=bp 1 from by norm_num [bp],←bp_sub]
      congr 1
      push_cast
      ring
    rwa [he] at hh
  · left
    have hz c : h c*h' c=0:=by
      by_cases hh : h c=0
      · rw [hh,zero_mul]
      have hh' : h' c=0:=le_antisymm (not_lt.mp (fun hc=>hex ⟨c,lt_of_le_of_ne (hn c) (Ne.symm hh),hc⟩)) (hn' c)
      rw [hh',mul_zero]
    change avg ν (fun c=>h c*h' c)=0
    simp only [hz,avg_zero]

end
end Lax793645Proofs.Simplifications
