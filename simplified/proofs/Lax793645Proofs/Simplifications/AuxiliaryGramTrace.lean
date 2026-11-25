import Lax793645Proofs.Simplifications.AuxiliaryGramRails
import Lax793645Proofs.Simplifications.AuxiliaryKernelNetworks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {J : Type} [Fintype J] [DecidableEq J] {N : ℕ}

def auxiliaryTarget (Z V : Mat J J) : Mat (Bool×J) (Bool×J):=
  fun i j=>if i.1 then 0 else if j.1 then V i.2 j.2 else Z i.2 j.2

theorem auxiliary_target_pairing (A C Z V : Mat J J) :
    mpair (auxiliaryMatrix A C) (auxiliaryTarget Z V)=mpair A Z+mpair C V:=by
  simp only [mpair,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type,Fintype.sum_bool,
    Finset.sum_add_distrib]
  simp [auxiliaryMatrix,auxiliaryTarget]
  ac_rfl

theorem auxiliary_cross_pairing (C : Mat J J) (x y : KeyCoordinates J N) :
    crossGram C Cᵀ N x y=mpair C (auxiliaryPairing (keyPlus x,keyMinus x) (keyPlus y,keyMinus y)):=by
  rw [cross_gram_apply,layer_form,layer_form]
  change _=mpair C ((keyPlus x)ᵀ*keyMinus y+(keyMinus x)ᵀ*keyPlus y)
  rw [map_add]
  congr 1
  change (∑ i,∑ j,C j i*∑ u,keyPlus y u i*keyMinus x u j)=
    ∑ i,∑ j,C i j*∑ u,keyMinus x u i*keyPlus y u j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact mul_comm _ _

theorem ledger_matrix_pairing (E : Rail J) (v : Vec E) (A : Mat J J) :
    mpair (ledgerM E v) A=dotProduct v (railsM E A):=by
  let r (i : J×J):=ledgerM E v i.1 i.2*A i.1 i.2
  change (∑ i,∑ j,r (i,j))=∑ i:E,v i*A i.val.1 i.val.2
  rw [←Fintype.sum_prod_type]
  symm
  calc
    _=∑ i:E,r i.val:=by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [r]
      rw [show ledgerM E v i.val.1 i.val.2=v i from congr_fun (inLedger E v) i]
    _=∑ i∈E,r i:=Finset.sum_coe_sort ..
    _=_:=Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=>by
      rcases i with ⟨i,j⟩
      simp only [r,ledgerM,Matrix.of_apply,dif_neg hi,zero_mul])

/-- The enlarged Gram condition says exactly the old quadratic Gram
condition together with the auxiliary polar pairing equations. -/
theorem auxiliary_trace_iff (E : Rail J) (hE : ∀ i j,(i,j)∈E→(j,i)∈E)
    (Z V : Mat J J) (x y : KeyCoordinates J N) :
    quadraticTraced (auxiliaryRail E) (auxiliaryTarget Z V) (auxiliaryCoordinates J N (x,y)) ↔
      quadraticTraced E Z x ∧
      railsM E (auxiliaryPairing (keyPlus x,keyMinus x) (keyPlus y,keyMinus y))=railsM E V:=by
  have hc (A : symmetricRail E) (v : Vec E) :
      gramPrimitive (auxiliaryMatrix A.val (ledgerM E v)) (auxiliaryCoordinates J N (x,y))=
        gramPrimitive A.val x+dotProduct v
          (railsM E (auxiliaryPairing (keyPlus x,keyMinus x) (keyPlus y,keyMinus y))):=by
    rw [auxiliary_gram_decomposition]
    change gramPrimitive A.val x+crossGram (ledgerM E v) (ledgerM E v)ᵀ N x y+
      gramPrimitive (0 : Mat J J) y=_
    have hz : gramPrimitive (0 : Mat J J) y=0:=by simp [gramPrimitive,layer_form,mpair]
    rw [hz,add_zero,auxiliary_cross_pairing,ledger_matrix_pairing]
  constructor
  · intro hh
    have hm (A : symmetricRail E) (v : Vec E) :
        gramPrimitive A.val x+dotProduct v
          (railsM E (auxiliaryPairing (keyPlus x,keyMinus x) (keyPlus y,keyMinus y)))=
        mpair A.val Z+dotProduct v (railsM E V):=by
      have h:=hh (auxiliaryRailEquiv E hE (A,v)).val
        (auxiliaryRailEquiv E hE (A,v)).property.1 (auxiliaryRailEquiv E hE (A,v)).property.2
      change gramPrimitive (auxiliaryMatrix A.val (ledgerM E v)) _=
        mpair (auxiliaryMatrix A.val (ledgerM E v)) _ at h
      rwa [hc,auxiliary_target_pairing,ledger_matrix_pairing] at h
    refine ⟨?_,?_⟩
    · intro A hA hAE
      simpa only [zero_dotProduct,add_zero] using hm ⟨A,hA,hAE⟩ 0
    · funext i
      have hh:=hm 0 (Pi.single i 1)
      simpa [gramPrimitive,layer_form,mpair] using hh
  · rintro ⟨hx,hy⟩ M hM hm
    obtain ⟨⟨A,v⟩,h⟩:=(auxiliaryRailEquiv E hE).surjective ⟨M,hM,hm⟩
    have he:=congrArg Subtype.val h
    change auxiliaryMatrix A.val (ledgerM E v)=M at he
    rw [←he,hc,auxiliary_target_pairing,ledger_matrix_pairing,
      hx A.val A.property.1 A.property.2,hy]

end
end Lax793645Proofs.Simplifications
