import Lax793645Proofs.Simplifications.QuadraticNetworkCodes
import Lax793645Proofs.Simplifications.QuadraticPairGramLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] {N : ℕ}

theorem network_matrix_pairing (g : Route I G) (M H : Mat I I)
    (hM : withinRail M (crowded g)) :
    mpair M H=∑ c,mpair (M.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val))
      (H.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)) := by
  change (∑ i,∑ j,M i j*H i j)=∑ c,∑ i : Port g c,∑ j : Port g c,M i.val j.val*H i.val j.val
  rw [←Fintype.sum_fiberwise g (fun i=>∑ j,M i j*H i j)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  rw [←Fintype.sum_fiberwise g (fun j=>M i.val j*H i.val j)]
  rw [Finset.sum_eq_single c]
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro j _
    have hn : (i.val,j.val)∉crowded g:=by
      intro he
      exact hd (j.property.symm.trans ((mem_filter.mp he).2.symm.trans i.property))
    rw [hM _ _ hn,zero_mul]
  · simp

theorem geo_matrix_pairing (g : Route I G) (A : GeoM g) (H : Mat I I) :
    mpair (geoMatrix g A) H=∑ c,mpair (A c)
      (H.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)) := by
  rw [network_matrix_pairing g _ _ (geo_matrix_supported g A)]
  apply Finset.sum_congr rfl
  intro c _
  have he : (geoMatrix g A).submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)=A c := by
    ext i j
    exact geo_matrix_block g A c i j
  rw [he]

theorem quadratic_network_traced (g : Route I G) (A : GeoM g) (x : Rack I N) :
    quadraticTraced (crowded g) (geoMatrix g A) ((rackCoordinates I N).symm x) ↔
      ∀ c,quadraticPairCode (rackEquiv g N x c)=quadraticGramCode (A c) := by
  have hg c : ((x.1ᵀ*x.2).submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val))=
      (rackEquiv g N x c).1ᵀ*(rackEquiv g N x c).2 := by ext i j; rfl
  have hread : quadraticTraced (crowded g) (geoMatrix g A) ((rackCoordinates I N).symm x) ↔
      ∀ M : symmetricRail (crowded g),mpair M.val (x.1ᵀ*x.2)=mpair M.val (geoMatrix g A) := by
    have hp : keyPlus ((rackCoordinates I N).symm x)=x.1 := rfl
    have hminus : keyMinus ((rackCoordinates I N).symm x)=x.2 := rfl
    constructor
    · intro h M
      have hh:=h M.val M.property.1 M.property.2
      simpa only [gramPrimitive,layer_form,hp,hminus] using hh
    · intro h M hs hm
      simpa only [gramPrimitive,layer_form,hp,hminus] using h ⟨M,hs,hm⟩
  rw [hread]
  constructor
  · intro h c
    apply (quadratic_full_code_eq _ _).mp
    apply LinearMap.ext
    intro M
    let V : ∀ d,symmetricRail (univ : Rail (Port g d)):=Function.update (fun _=>0) c M
    have hh:=h (symmetricNetworkEquiv g V)
    change mpair (geoMatrix g (fun d=>(V d).val)) (x.1ᵀ*x.2)=
      mpair (geoMatrix g (fun d=>(V d).val)) (geoMatrix g A) at hh
    rw [geo_matrix_pairing,geo_matrix_pairing] at hh
    have hs (H : Mat I I) :
        (∑ d,mpair (V d).val (H.submatrix (fun i : Port g d=>i.val) (fun i : Port g d=>i.val)))=
        mpair M.val (H.submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)) := by
      rw [Finset.sum_eq_single c]
      · simp [V]
      · intro d _ hd
        simp [V,hd,mpair]
      · simp
    rw [hs,hs,hg] at hh
    have hb : (geoMatrix g A).submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)=A c := by
      ext i j
      exact geo_matrix_block g A c i j
    rw [hb] at hh
    simpa only [quadratic_rail_read_value] using hh
  · intro h M
    rw [network_matrix_pairing g _ _ M.property.2,network_matrix_pairing g _ _ M.property.2]
    apply Finset.sum_congr rfl
    intro c _
    rw [hg]
    have hb : (geoMatrix g A).submatrix (fun i : Port g c=>i.val) (fun i : Port g c=>i.val)=A c := by
      ext i j
      exact geo_matrix_block g A c i j
    rw [hb]
    apply symmetric_pairing_quadratic_code _ _ _ _ (h c)
    ext i j
    exact congrFun (congrFun M.property.1 i.val) j.val

end
end Lax793645Proofs.Simplifications
