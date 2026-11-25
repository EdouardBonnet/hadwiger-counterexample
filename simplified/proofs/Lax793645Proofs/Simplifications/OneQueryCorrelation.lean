import Lax793645Proofs.Simplifications.OneQueryHighMoment

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I T J : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [DecidableEq J] {p : Shape} {n N : ℕ}

/-- On the reference key variety every permitted within-query quadratic
character is constant. A single query therefore supplies its small Fourier
coefficient directly. -/
theorem quadratic_supported_fourier (E : Rail J) (Z : Mat J J)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ)
    (hs : ∀ x,D x≠0→quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (M : Mat J J) (hM : Mᵀ=M) (hm : withinRail M E)
    (ξ : KeyCoordinates J N) :
    |linearFourier (fun x=>phasedBy M (rackCoordinates J N x)*D x) ξ|≤δ := by
  have he x : phasedBy M (rackCoordinates J N x)*D x=wsign (mpair M Z)*D x:=by
    by_cases hx : D x=0
    · simp only [hx,mul_zero]
    · have hh:=hs x hx M hM hm
      change wsign (gramPrimitive M x)*D x=_
      rw [hh]
  simp_rw [he]
  unfold linearFourier
  have he x : vectorPhase ξ x*(wsign (mpair M Z)*D x)=
      wsign (mpair M Z)*(vectorPhase ξ x*D x):=by ring
  simp_rw [he]
  rw [avg_mul',abs_mul,wsign_abs,one_mul]
  exact hF ξ

def oneQueryCorrelation (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (o : OneUnit p n N) : ℝ:=
  avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x)

abbrev directQueryRoute (v : Template p I) (T : Type) : Route (T×KeySlots p v.t) (Ports p):=
  tied (globPort p v.t v.aim) T

def directQueryNominal (v : Template p I) (y : T→Inputs p n I) :
    NomQuery p n (directQueryRoute v T):=
  pooled (fun t=>v.queryLaw (y t))

omit [DecidableEq I] in
theorem one_direct_nominal_key (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (y : T→Inputs p n I) (o : OneUnit p n N) (t : T) :
    (rackCoordinates (KeySlots p v.t) N).symm
      (led t (onePeek (directQueryRoute v T) (directQueryNominal v y) (oneMerge o)))=
      oneTemplateCoordinates v o (y t) := by
  funext c
  rcases c with ⟨u,b,i⟩
  cases b
  · change onePrimal (o (v.aim i.1) i.2.val)
      ((directQueryNominal v y (v.aim i.1,i.2.val))*ᵥPi.single ⟨(t,i),rfl⟩ 1) (Sum.inl u)=_
    rw [Matrix.mulVec_single_one]
    rfl
  · change onePrimal (o (v.aim i.1) i.2.val)
      ((directQueryNominal v y (v.aim i.1,i.2.val))*ᵥPi.single ⟨(t,i),rfl⟩ 1) (Sum.inr u)=_
    rw [Matrix.mulVec_single_one]
    rfl

theorem one_direct_moment_expansion (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (ρ : Wgt (OneUnit p n N)) :
    avg ρ (fun o=>(oneQueryCorrelation v D ψ o)^Fintype.card T)=
      avg unif (fun y : T→Inputs p n I=>(∏ t,ψ (y t))*
        avg ρ (fun o=>∏ t,D ((rackCoordinates (KeySlots p v.t) N).symm
          (led t (onePeek (directQueryRoute v T) (directQueryNominal v y) (oneMerge o)))))) := by
  have he (o : OneUnit p n N) : (oneQueryCorrelation v D ψ o)^Fintype.card T=
      avg unif (fun y : T→Inputs p n I=>∏ t,D (oneTemplateCoordinates v o (y t))*ψ (y t)):=by
    have hh:=prodW_avg (fun _ : T=>(unif : Wgt (Inputs p n I)))
      (fun _ x=>D (oneTemplateCoordinates v o x)*ψ x)
    rw [←uniform_product_law] at hh
    simp only [Finset.prod_const,Finset.card_univ] at hh
    exact hh.symm
  simp_rw [he,Finset.prod_mul_distrib,one_direct_nominal_key]
  rw [avg_avg]
  simp_rw [avg_mul]
  congr 1
  funext y
  ring

end
end Lax793645Proofs.Simplifications
