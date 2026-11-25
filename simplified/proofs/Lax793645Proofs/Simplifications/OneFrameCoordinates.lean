import Lax793645Proofs.Simplifications.OneUnitCollisions
import Lax793645Proofs.Simplifications.CoordinatePinClosure

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneBlock := Bool⊕(Bool⊕Bool)

def oneBlockSlots (p : Shape) (n : ℕ) : OneBlock→Type
  | Sum.inl _=>Row p n
  | Sum.inr _=>Fin p.h

instance oneBlockSlotsFintype (p : Shape) (n : ℕ) (b : OneBlock) : Fintype (oneBlockSlots p n b) := by
  cases b <;> dsimp only [oneBlockSlots] <;> infer_instance

instance oneBlockSlotsDecidable (p : Shape) (n : ℕ) (b : OneBlock) : DecidableEq (oneBlockSlots p n b) := by
  cases b <;> dsimp only [oneBlockSlots] <;> infer_instance

abbrev OneColumn (p : Shape) (n : ℕ) := Σ b : OneBlock,oneBlockSlots p n b

def oneBlockCoordinates (p : Shape) (n : ℕ) :
    Vec (OneColumn p n)≃ₗ[F](∀ b : OneBlock,Vec (oneBlockSlots p n b)) where
  toFun v b i:=v ⟨b,i⟩
  invFun v i:=v i.1 i.2
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def oneNominalCoordinates (p : Shape) (n : ℕ) : Vec (OneColumn p n)≃ₗ[F]OneUnitFull p n where
  toFun v:=(fun ri=>v ⟨Sum.inl ri.2,ri.1⟩,
    fun i=>(fun j=>v ⟨Sum.inr (Sum.inl i),j⟩,fun j=>v ⟨Sum.inr (Sum.inr i),j⟩))
  invFun v k:=match k with
    | ⟨Sum.inl i,r⟩=>v.1 (r,i)
    | ⟨Sum.inr (Sum.inl i),j⟩=>((v.2 i).1) j
    | ⟨Sum.inr (Sum.inr i),j⟩=>((v.2 i).2) j
  left_inv v:=by
    funext k
    rcases k with ⟨i,k⟩
    rcases i with i|i
    · rfl
    · cases i <;> rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def oneAmbientCoordinates (N : ℕ) : Vec (HyperbolicIdx N)≃ₗ[F]Vec (Fin (2*N)) :=
  LinearEquiv.funCongrLeft F F
    (finSumFinEquiv.trans (finCongr (Nat.two_mul N).symm)).symm

def oneCoordinateImages {p : Shape} {n N : ℕ} (x : OneUnit p n N) (e : Comp p.g) :
    Mat (Fin (2*N)) (OneColumn p n) :=
  LinearMap.toMatrix' ((oneAmbientCoordinates N).toLinearMap.comp
    ((oneUnitMap x e).comp (oneNominalCoordinates p n).toLinearMap))

theorem one_coordinate_images_apply {p : Shape} {n N : ℕ}
    (x : OneUnit p n N) (e : Comp p.g) (v : Vec (OneColumn p n)) :
    oneCoordinateImages x e*ᵥv=oneAmbientCoordinates N (oneUnitMap x e (oneNominalCoordinates p n v)) := by
  rw [oneCoordinateImages,LinearMap.toMatrix'_mulVec]
  rfl

/-- The actual one-frame nominal columns split into P1, P2, X1, X2, Y1,
Y2. The resulting closure factor is exactly six. -/
def onePinClosure (p : Shape) (n : ℕ) : ImageClosure (Comp p.g) (OneColumn p n) 6 := by
  have hc : Fintype.card OneBlock=6:=by simp [OneBlock]
  exact hc ▸ coordinateImageClosure (oneBlockCoordinates p n)

end
end Lax793645Proofs.Simplifications
