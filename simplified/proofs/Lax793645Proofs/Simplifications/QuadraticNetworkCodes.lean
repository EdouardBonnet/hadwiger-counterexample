import Lax793645Proofs.Simplifications.QuadraticFullCodes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

def geoMatrix (g : Route I G) (A : GeoM g) : Mat I I:=
  fun i j=>if h:g i=g j then A (g i) ⟨i,rfl⟩ ⟨j,h.symm⟩ else 0

theorem geo_matrix_block (g : Route I G) (A : GeoM g) (c : G) (i j : Port g c) :
    geoMatrix g A i.val j.val=A c i j := by
  rcases i with ⟨i,hi⟩
  rcases j with ⟨j,hj⟩
  subst c
  simp only [geoMatrix,dif_pos hj.symm]

theorem geo_matrix_supported (g : Route I G) (A : GeoM g) :
    withinRail (geoMatrix g A) (crowded g) := by
  intro i j h
  have hn : g i≠g j:=fun he=>h (mem_filter.mpr ⟨mem_univ _,he⟩)
  exact dif_neg hn

theorem geo_matrix_symmetric (g : Route I G) (A : GeoM g) (hA : ∀ c,(A c)ᵀ=A c) :
    (geoMatrix g A)ᵀ=geoMatrix g A := by
  ext i j
  by_cases h : g i=g j
  · let a : Port g (g i):=⟨i,rfl⟩
    let b : Port g (g i):=⟨j,h.symm⟩
    change geoMatrix g A b.val a.val=geoMatrix g A a.val b.val
    rw [geo_matrix_block,geo_matrix_block]
    exact congrFun (congrFun (hA (g i)) a) b
  · change geoMatrix g A j i=geoMatrix g A i j
    simp only [geoMatrix,dif_neg h,dif_neg (Ne.symm h)]

theorem geo_matrix_reconstruct (g : Route I G) (M : Mat I I)
    (hM : withinRail M (crowded g)) :
    geoMatrix g (fun c=>M.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val))=M := by
  ext i j
  by_cases h : g i=g j
  · simp only [geoMatrix,dif_pos h,submatrix_apply]
  · rw [show M i j=0 from hM i j (fun he=>h (mem_filter.mp he).2)]
    exact dif_neg h

def symmetricNetworkEquiv (g : Route I G) :
    (∀ c,symmetricRail (univ : Rail (Port g c)))≃ₗ[F]symmetricRail (crowded g) where
  toFun A:=⟨geoMatrix g (fun c=>(A c).val),geo_matrix_symmetric g _ (fun c=>(A c).property.1),
    geo_matrix_supported g _⟩
  invFun M c:=⟨M.val.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val),
    by ext i j; exact congrFun (congrFun M.property.1 i.val) j.val,
    fun _ _ hn=>(hn (mem_univ _)).elim⟩
  left_inv A:=by
    funext c
    apply Subtype.ext
    ext i j
    exact geo_matrix_block g (fun c=>(A c).val) c i j
  right_inv M:=Subtype.ext (geo_matrix_reconstruct g M.val M.property.2)
  map_add' A B:=by
    apply Subtype.ext
    ext i j
    change geoMatrix g (fun c=>(A c).val+(B c).val) i j=
      geoMatrix g (fun c=>(A c).val) i j+geoMatrix g (fun c=>(B c).val) i j
    by_cases h:g i=g j <;> simp [geoMatrix,h]
  map_smul' a A:=by
    apply Subtype.ext
    ext i j
    change geoMatrix g (fun c=>a•(A c).val) i j=a*geoMatrix g (fun c=>(A c).val) i j
    by_cases h:g i=g j <;> simp [geoMatrix,h]

/-- The exact number of quadratic Gram equations is additive over the
independent endpoint/component ports. -/
theorem quadratic_network_dimension (g : Route I G) :
    dim (symmetricRail (crowded g))=∑ c,dim (QuadraticGramCode (Port g c)) := by
  have he:=(symmetricNetworkEquiv g).finrank_eq
  rw [Module.finrank_pi_fintype] at he
  change (∑ c,dim (symmetricRail (univ : Rail (Port g c))))=dim (symmetricRail (crowded g)) at he
  rw [←he]
  exact Finset.sum_congr rfl (fun c _=>quadratic_full_dimension (I:=Port g c))

end
end Lax793645Proofs.Simplifications
