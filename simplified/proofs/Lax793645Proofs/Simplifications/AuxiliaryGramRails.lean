import Lax793645Proofs.Simplifications.AuxiliaryGramBatches

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {J : Type} [Fintype J] [DecidableEq J]

def auxiliaryRail (E : Rail J) : Rail (Bool×J):=
  univ.filter (fun z=>(z.1.2,z.2.2)∈E ∧ (z.1.1=false ∨ z.2.1=false))

def auxiliaryMatrix (A C : Mat J J) : Mat (Bool×J) (Bool×J):=
  fun i j=>if i.1 then (if j.1 then 0 else C j.2 i.2)
    else (if j.1 then C i.2 j.2 else A i.2 j.2)

theorem auxiliary_matrix_blocks (A C : Mat J J) :
    auxiliaryBlock (auxiliaryMatrix A C) false false=A ∧
    auxiliaryBlock (auxiliaryMatrix A C) false true=C ∧
    auxiliaryBlock (auxiliaryMatrix A C) true false=Cᵀ ∧
    auxiliaryBlock (auxiliaryMatrix A C) true true=0:=⟨rfl,rfl,rfl,rfl⟩

theorem auxiliary_matrix_symmetric (A C : Mat J J) (hA : Aᵀ=A) :
    (auxiliaryMatrix A C)ᵀ=auxiliaryMatrix A C:=by
  ext ⟨a,i⟩ ⟨b,j⟩
  cases a <;> cases b
  · exact congrFun (congrFun hA i) j
  · rfl
  · rfl
  · rfl

theorem auxiliary_matrix_supported (E : Rail J)
    (hE : ∀ i j,(i,j)∈E→(j,i)∈E)
    (A C : Mat J J) (hA : withinRail A E) (hC : withinRail C E) :
    withinRail (auxiliaryMatrix A C) (auxiliaryRail E):=by
  intro ⟨a,i⟩ ⟨b,j⟩ hn
  have hh : ¬((i,j)∈E ∧ (a=false ∨ b=false)):=by
    simpa only [auxiliaryRail,mem_filter,mem_univ,true_and] using hn
  cases a <;> cases b
  · exact hA i j (fun h=>hh ⟨h,Or.inl rfl⟩)
  · exact hC i j (fun h=>hh ⟨h,Or.inl rfl⟩)
  · exact hC j i (fun h=>hh ⟨hE j i h,Or.inr rfl⟩)
  · rfl

def auxiliaryRailEquiv (E : Rail J) (hE : ∀ i j,(i,j)∈E→(j,i)∈E) :
    (symmetricRail E × Vec E) ≃ₗ[F] symmetricRail (auxiliaryRail E) where
  toFun z:=⟨auxiliaryMatrix z.1.val (ledgerM E z.2),
    auxiliary_matrix_symmetric _ _ z.1.property.1,
    auxiliary_matrix_supported E hE _ _ z.1.property.2 (within_recorded E z.2)⟩
  invFun M:=
    (⟨auxiliaryBlock M.val false false,
       by ext i j; exact congrFun (congrFun M.property.1 (false,i)) (false,j),
       by intro i j hn; exact M.property.2 (false,i) (false,j)
            (by simpa [auxiliaryRail,hn])⟩,
     railsM E (auxiliaryBlock M.val false true))
  left_inv z:=by
    apply Prod.ext
    · rfl
    · exact inLedger E z.2
  right_inv M:=by
    apply Subtype.ext
    change auxiliaryMatrix (auxiliaryBlock M.val false false)
      (ledgerM E (railsM E (auxiliaryBlock M.val false true)))=M.val
    have hc : withinRail (auxiliaryBlock M.val false true) E:=by
      intro i j hn
      exact M.property.2 (false,i) (true,j) (by simp [auxiliaryRail,hn])
    rw [ledger_recovers E _ hc]
    ext ⟨a,i⟩ ⟨b,j⟩
    cases a <;> cases b
    · rfl
    · rfl
    · exact congrFun (congrFun M.property.1 (true,i)) (false,j)
    · exact (M.property.2 (true,i) (true,j) (by simp [auxiliaryRail])).symm
  map_add' x y:=by
    apply Subtype.ext
    ext ⟨a,i⟩ ⟨b,j⟩
    cases a <;> cases b <;>
      simp [auxiliaryMatrix,ledgerM,Matrix.add_apply] <;> split_ifs <;> simp_all
  map_smul' a x:=by
    apply Subtype.ext
    ext ⟨b,i⟩ ⟨c,j⟩
    cases b <;> cases c <;>
      simp [auxiliaryMatrix,ledgerM]

/-- Auxiliary vectors add exactly one pairing equation per permitted
ordered pair of original slots. They introduce no auxiliary--auxiliary
Gram conditions. -/
theorem auxiliary_rail_dimension (E : Rail J)
    (hE : ∀ i j,(i,j)∈E→(j,i)∈E) :
    dim (symmetricRail (auxiliaryRail E))=dim (symmetricRail E)+Fintype.card E:=by
  have hh:=(auxiliaryRailEquiv E hE).finrank_eq
  rw [Module.finrank_prod] at hh
  change dim (symmetricRail E)+dim (Vec E)=dim (symmetricRail (auxiliaryRail E)) at hh
  rw [dim_vec] at hh
  exact hh.symm

end
end Lax793645Proofs.Simplifications
