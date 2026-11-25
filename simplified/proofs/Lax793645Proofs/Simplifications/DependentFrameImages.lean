import Lax793645Proofs.Simplifications.PrescribedKernelGram
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.IndependentColumnBatches

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J R S U : Type}
  [Fintype I] [Fintype J] [Fintype R] [Fintype S] [Fintype U]
  [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S] [DecidableEq U]

theorem quotient_exact_gram_law (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S) :
    mapW (unifOn (gramGood (U:=U) G)) (fun z=>(z.1*L,z.2*M))=
      unifOn (prescribedKernelGram L M G) := by
  let T (z : Mat U R×Mat U S) := (z.1*L,z.2*M)
  let ok (z : Mat U I×Mat U J) :=
    LinearMap.ker z.1.mulVecLin=LinearMap.ker L.mulVecLin ∧
      LinearMap.ker z.2.mulVecLin=LinearMap.ker M.mulVecLin
  have he : (gramGood (U:=U) G)=
      (fun z=>(z.1ᵀ*z.2=G) ∧ ok (T z)) := by
    funext z
    simp only [gramGood,ok,T,exact_kernel_mul_iff L hL,exact_kernel_mul_iff M hM]
  rw [he,←unifOn_and]
  change mapW (onW (unifOn (fun z : Mat U R×Mat U S=>z.1ᵀ*z.2=G)) (ok ∘ T)) T=_
  rw [map_condition]
  have hh := quotient_gram_law (U:=U) L M hL hM G
  rw [←pair_unif,on_unif] at hh
  rw [show mapW (unifOn (fun z : Mat U R×Mat U S=>z.1ᵀ*z.2=G)) T=
    unifOn (relationGram L M G) from hh,unifOn_and]
  congr 1
  funext z
  apply propext
  change (((_≤_) ∧ (_≤_)) ∧ z.1ᵀ*z.2=Lᵀ*G*M) ∧ ok z ↔ _
  constructor
  · rintro ⟨⟨_,hG⟩,hK⟩
    exact ⟨hK.1,hK.2,hG⟩
  · rintro ⟨hP,hQ,hG⟩
    exact ⟨⟨⟨hP.ge,hQ.ge⟩,hG⟩,hP,hQ⟩

omit [Fintype U] [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq U] in
theorem left_injective_kernel (A : Mat U R) (hA : Injective A.mulVec) (L : Mat R I) :
    LinearMap.ker (A*L).mulVecLin=LinearMap.ker L.mulVecLin := by
  ext x
  change (A*L)*ᵥx=0 ↔ L*ᵥx=0
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_zero A,hA.eq_iff]

/-- Exact dependent image law for one actual endpoint/component frame.
No columns are removed from the observed rack. -/
theorem peer_dependent {p : Shape} {n N : ℕ} (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (A : Mat (Row p n) I) :
    mapW (rawC m N) (peer p A A)=unifOn (fun z : Rack I N=>
      LinearMap.ker z.1.mulVecLin=LinearMap.ker A.mulVecLin ∧
      LinearMap.ker z.2.mulVecLin=LinearMap.ker A.mulVecLin ∧
      z.1ᵀ*z.2=pullM A A (selfM p n m.mixM)) := by
  classical
  obtain ⟨C,L,hC,hL,hCL⟩ := rank_product A
  let T (z : Rack (Fin A.rank) N) : Rack I N := (z.1*L,z.2*L)
  have he : peer p A A=T ∘ peer p C C := by
    funext x
    dsimp only [peer,T,Function.comp_apply]
    simp only [Matrix.mul_assoc,hCL]
  rw [he,←mapW_nested,peer_cap m N hN hC hC]
  dsimp only [T]
  rw [quotient_exact_gram_law L L hL hL]
  have hk : LinearMap.ker A.mulVecLin=LinearMap.ker L.mulVecLin := by
    simpa only [hCL] using left_injective_kernel C hC L
  have hg : Lᵀ*pullM C C (selfM p n m.mixM)*L=pullM A A (selfM p n m.mixM) := by
    simp only [pullM_def]
    calc
      _=(C*L)ᵀ*selfM p n m.mixM*(C*L) := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=_ := by simp only [hCL]
  congr 1
  funext z
  simp only [prescribedKernelGram,hk,hg]

/-- Uniform finite product events split without a positivity assumption. -/
theorem uniform_pi_event {G : Type} [Fintype G] [DecidableEq G]
    {A : G→Type} [∀ i,Fintype (A i)] (p : ∀ i,A i→Prop) :
    unifOn (fun x=>∀ i,p i (x i))=prodW (fun i=>unifOn (p i)) := by
  classical
  funext x
  rw [unifOn_val]
  have he : nbr (fun x : ∀ i,A i=>∀ i,p i (x i))=∏ i,nbr (p i) := by
    unfold nbr
    simp_rw [ind_all]
    exact prodW_tot (fun i x=>ind (p i x))
  simp only [prodW,he,unifOn_val,ind_all,Finset.prod_div_distrib]

def dependentGramPart {p : Shape} {n N : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    (g : Route I G) (m : Mixer p n) (A : NomQuery p n g) (x : Rack I N) : Prop :=
  ∀ i, let z:=rackEquiv g N x i
       LinearMap.ker z.1.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
       LinearMap.ker z.2.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
       z.1ᵀ*z.2=pullM (A i) (A i) (selfM p n m.mixM)

/-- Simultaneous dependent image law at every endpoint and component. -/
theorem law_peek_dependent {p : Shape} {n N : ℕ} {G : Type}
    [Fintype G] [DecidableEq G] (g : Route I G) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (A : NomQuery p n g) :
    mapW (forumLaw m N) (peekR p g A A)=unifOn (dependentGramPart g m A) := by
  classical
  let E:=rackEquiv g N
  let f (x : Forum p n N G) := fun i=>peer p (A i) (A i) (x i)
  have h : mapW (forumLaw m N) f=mapW (unifOn (dependentGramPart g m A)) E := by
    unfold forumLaw f
    rw [joint_map]
    have he : mapW (unifOn (dependentGramPart g m A)) E=
      prodW (fun i=>unifOn (fun z : Rack (Port g i) N=>
        LinearMap.ker z.1.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
        LinearMap.ker z.2.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
        z.1ᵀ*z.2=pullM (A i) (A i) (selfM p n m.mixM))) := by
      exact (on_equiv E (fun y : Network g N=>∀ i,
        LinearMap.ker (y i).1.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
        LinearMap.ker (y i).2.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
        (y i).1ᵀ*(y i).2=pullM (A i) (A i) (selfM p n m.mixM))).trans (uniform_pi_event (fun i (z : Rack (Port g i) N)=>
          LinearMap.ker z.1.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
          LinearMap.ker z.2.mulVecLin=LinearMap.ker (A i).mulVecLin ∧
          z.1ᵀ*z.2=pullM (A i) (A i) (selfM p n m.mixM)))
    rw [he]
    apply congrArg (prodW (ι:=G))
    funext i
    exact peer_dependent m hN (A i)
  change mapW (forumLaw m N) (E.symm ∘ f)=_
  rw [←mapW_nested,h]
  funext x
  rw [mapW_equiv_val,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply]

/-- The query's original key columns have exactly this law even when the
nominal inputs are dependent. The previous raw_keys needed independence. -/
theorem raw_keys_dependent {p : Shape} {n N : ℕ}
    (t : Tagging p I) (v : Volley p n I) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) :
    mapW (pairW (raw m N) (raw m N)) ((scatter t N) ∘ v.keys t)=
      unifOn (dependentGramPart (globPort p t v.obj) m (nomAsk t v)) := by
  classical
  have hh:=law_peek_dependent (globPort p t v.obj) m hN (nomAsk t v)
  rw [←law_mergeR m N,mapW_nested] at hh
  refine Eq.trans ?_ hh
  congr 1

end
end Lax793645Proofs.Simplifications
