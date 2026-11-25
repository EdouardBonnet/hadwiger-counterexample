import Lax793645Proofs.Simplifications.OneSupportedPhaseLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N r : ℕ}

def oneImageProfile (o : OneOrient p n N) : Profile p n→ₗ[F]Ambient p (2*N) where
  toFun z e:=liftM (onePrimalMatrix (o e)) (onePrimalMatrix (o e)) (z e)
  map_add' z w:=by ext e a b; simp only [Pi.add_apply,map_add,Matrix.add_apply]
  map_smul' c z:=by ext e a b; simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Matrix.smul_apply]

theorem one_image_profile_readout (o : OneOrient p n N) (z : Profile p n) :
    oneImageProfile o z=oneAmbientReadout (oneMomentEmbed o z) := by
  classical
  funext e
  change liftM (onePrimalMatrix (o e)) (onePrimalMatrix (o e)) (z e)=
    quadraticMomentMap (oneAmbientCoordinates N).toLinearMap
      (quadraticMomentMap (onePrimal (o e)) (z e))
  rw [quadraticMomentMap,quadraticMomentMap,liftM_comp]
  simp only [onePrimalMatrix,LinearMap.toMatrix'_comp]
  congr!

theorem one_image_profile_box (x : OneUnit p n N) (i : Bool) (z : Profile p n) (e : Comp p.g) :
    oneImageProfile (x i) z e∈box (onePrimalImages x i e) (onePrimalImages x i e) := by
  change liftM _ _ _∈box _ _
  rw [box_mem,liftM_transpose]
  exact ⟨colSp_lift_le ..,colSp_lift_le ..⟩

theorem one_image_profile_symmetric (o : OneOrient p n N) (z : Profile p n)
    (hz : z∈Xspace p n) (e : Comp p.g) : (oneImageProfile o z e)ᵀ=oneImageProfile o z e := by
  have hs : (z e)ᵀ=z e := by
    obtain ⟨w,hw,rfl⟩:=mem_X.mp hz
    exact Wspace_sym ((Wspace p n).add_mem (Wtag_le _ (hw _)) (Wtag_le _ (hw _)))
  change (liftM _ _ _)ᵀ=liftM _ _ _
  rw [liftM_transpose,hs]

theorem one_image_profile_rank (o : OneOrient p n N) (z : Profile p n) :
    epoch p (oneImageProfile o z)≤totalRank z := by
  apply Finset.sum_le_sum
  intro e _
  change (liftM (onePrimalMatrix (o e)) (onePrimalMatrix (o e)) (z e)).rank≤(z e).rank
  rw [liftM_def]
  exact (Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)

def oneMarkedDelta (x : OneUnit p n N) (marks : Bool→Profile p n) : Ambient p (2*N):=
  oneImageProfile (x true) (marks true)+oneImageProfile (x false) (marks false)

/-- Concrete one-frame marked profiles produce the symmetric records
used by the phase estimate; their total companion count is bounded by
the original marked-profile rank. -/
theorem one_marked_offsets (x : OneUnit p n N) (marks : Bool→Profile p n)
    (hmarks : ∀ i,marks i∈Xspace p n) (S : SymCover p (2*N))
    (hdisj : ∀ i e,Disjoint (S e) (onePrimalImages x i e))
    (hcover : ∀ e,vanish (S e) (S e) (oneMarkedDelta x marks e))
    (hne : oneMarkedDelta x marks≠0) (hr : totalRank (marks true)≤r) :
    ∃ X : SymAtlas p r S,symStandard X ∧
      ∀ i,∃ Z,symCompFor X Z (onePrimalImages x i) (oneMarkedDelta x marks) := by
  exact symmetric_profile_offsets (fun i=>oneImageProfile (x i) (marks i)) (onePrimalImages x)
    (fun i e=>one_image_profile_symmetric _ _ (hmarks i) e)
    (fun i e=>one_image_profile_box x i (marks i) e) hdisj hcover hne
    ((one_image_profile_rank _ _).trans hr)

end
end Lax793645Proofs.Simplifications
