import Lax793645Proofs.Simplifications.QuadraticTransvections

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type} [AddCommGroup V] [Module QField V] [FiniteDimensional QField V]

/-- Move one new frame column while fixing the previously chosen columns.
Two quadratic reflections suffice in the case of zero mutual pairing. -/
theorem quadratic_move_fixing (q : QuadraticForm QField V)
    (hnd : q.polarBilin.Nondegenerate) (D : Submodule QField V)
    (u w : V) (hu : u∉D) (hw : w∉D) (hq : q u=q w)
    (hpolar : ∀ d : D,q.polarBilin d u=q.polarBilin d w)
    (hroom : 2*Module.finrank QField D+8≤Module.finrank QField V) :
    ∃ e : q.IsometryEquiv q,e u=w ∧ ∀ d : D,e d=d := by
  classical
  by_cases he : q.polarBilin u w=1
  · obtain ⟨e,he,hfix⟩:=quadratic_move_pair q u w hq he
    refine ⟨e,he,fun d=>hfix d ?_⟩
    simpa only [binary_polar_symm q u,binary_polar_symm q w] using hpolar d
  have he0 : q.polarBilin u w=0 := by
    rcases (by decide : ∀ a : QField,a=0∨a=1) (q.polarBilin u w) with h|h
    · exact h
    exact (he h).elim
  let S:=D⊔Submodule.span QField {u}
  let bD : D→ₗ[QField]QField:=(q.polarBilin u).comp D.subtype
  obtain ⟨b₁,hb₁,hb₁u⟩:=bD.exists_extend_of_notMem hu 1
  have hb₁D (d : D) : b₁ d=q.polarBilin u d:=LinearMap.congr_fun hb₁ d
  have huS : u∈S:=Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
  obtain ⟨b,hbu,hbw,hbD⟩ : ∃ b : V→ₗ[QField]QField,
      b u=1 ∧ b w=1 ∧ ∀ d : D,b d=q.polarBilin u d := by
    by_cases hwS : w∈S
    · refine ⟨b₁,hb₁u,?_,hb₁D⟩
      obtain ⟨d,hd|hd⟩:=binary_span_decompose D u w hwS
      · exact (hw (hd ▸ d.property)).elim
      have hd0 : q.polarBilin u d=0 := by
        have hh:=he0
        rw [hd,map_add,binary_polar_self,add_zero] at hh
        exact hh
      rw [hd,map_add,hb₁D,hd0,hb₁u,zero_add]
    · obtain ⟨b₂,hb₂,hb₂w⟩:=(b₁.comp S.subtype).exists_extend_of_notMem hwS 1
      have hb₂S (s : S) : b₂ s=b₁ s:=LinearMap.congr_fun hb₂ s
      exact ⟨b₂,(hb₂S ⟨u,huS⟩).trans hb₁u,hb₂w,
        fun d=>(hb₂S ⟨d,Submodule.mem_sup_left d.property⟩).trans (hb₁D d)⟩
  let T:=S⊔Submodule.span QField {w}
  have huT : u∈T:=Submodule.mem_sup_left huS
  have hwT : w∈T:=Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
  have hDdim : Module.finrank QField S=Module.finrank QField D+1 :=
    Submodule.finrank_sup_span_singleton hu
  have hTdim : Module.finrank QField T≤Module.finrank QField D+2 := by
    by_cases hwS : w∈S
    · have hTS : T=S:=sup_eq_left.mpr (Submodule.span_le.mpr (by
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact hwS))
      rw [hTS,hDdim]
      omega
    · have hh : Module.finrank QField T=Module.finrank QField S+1:=
        Submodule.finrank_sup_span_singleton hwS
      omega
  obtain ⟨z,_,hqz,hz⟩:=quadratic_one_vector q hnd T (b.comp T.subtype) (q u) (by omega)
  have huz : q.polarBilin u z=1:=(hz ⟨u,huT⟩).trans hbu
  have hwz : q.polarBilin w z=1:=(hz ⟨w,hwT⟩).trans hbw
  have hDz (d : D) : q.polarBilin u d=q.polarBilin z d := by
    have hh:=(hz ⟨d,Submodule.mem_sup_left (Submodule.mem_sup_left d.property)⟩).trans (hbD d)
    exact hh.symm.trans (binary_polar_symm q d z)
  obtain ⟨e₁,he₁,hfix₁⟩:=quadratic_move_pair q u z hqz.symm huz
  obtain ⟨e₂,he₂,hfix₂⟩:=quadratic_move_pair q z w (hqz.trans hq)
    ((binary_polar_symm q z w).trans hwz)
  refine ⟨e₁.trans e₂,?_,?_⟩
  · change e₂ (e₁ u)=w
    rw [he₁,he₂]
  · intro d
    change e₂ (e₁ d)=d
    rw [hfix₁ d (hDz d)]
    apply hfix₂
    exact (hDz d).symm.trans (by
      simpa only [binary_polar_symm q u,binary_polar_symm q w] using hpolar d)

omit [FiniteDimensional QField V] in
theorem quadratic_isometry_polar (q : QuadraticForm QField V) (e : q.IsometryEquiv q)
    (u w : V) : q.polarBilin (e u) (e w)=q.polarBilin u w := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,e.map_app]

variable {B : Type} [AddCommGroup B] [Module QField B] [FiniteDimensional QField B]

/-- Small isometric frames lie in one orbit of the ambient quadratic group.
The proof uses reflections and a dimension bound, without invoking Witt's theorem. -/
theorem quadratic_frame_move (q : QuadraticForm QField V)
    (hnd : q.polarBilin.Nondegenerate) (P Q : B→ₗ[QField] V)
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hq : ∀ x,q (P x)=q (Q x))
    (hroom : 2*Module.finrank QField B+6≤Module.finrank QField V) :
    ∃ e : q.IsometryEquiv q,∀ x,e (P x)=Q x := by
  classical
  have hp (x y : B) : q.polarBilin (P x) (P y)=q.polarBilin (Q x) (Q y) := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,hq]
  have extend : ∀ k : ℕ,∀ (S : Submodule QField B),
      Module.finrank QField B-Module.finrank QField S=k →
      ∀ (e : q.IsometryEquiv q),(∀ s : S,e (P s)=Q s) →
      ∃ e' : q.IsometryEquiv q,∀ x,e' (P x)=Q x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hk e he
      by_cases hS : S=⊤
      · exact ⟨e,fun x=>he ⟨x,hS ▸ Submodule.mem_top⟩⟩
      have hx : ∃ x : B,x∉S := by
        by_contra hh
        push Not at hh
        exact hS (Submodule.eq_top_iff'.mpr hh)
      obtain ⟨x,hx⟩:=hx
      let D:=S.map Q
      have hdimD : Module.finrank QField D=Module.finrank QField S :=
        (Submodule.equivMapOfInjective Q hQ S).finrank_eq.symm
      have hdimS : Module.finrank QField S<Module.finrank QField B:=Submodule.finrank_lt hS
      have hu : e (P x)∉D := by
        rintro ⟨s,hs,hsx⟩
        have hpx : P s=P x:=e.injective ((he ⟨s,hs⟩).trans hsx)
        exact hx (hP hpx ▸ hs)
      have hw : Q x∉D := by
        rintro ⟨s,hs,hsx⟩
        exact hx (hQ hsx ▸ hs)
      have hpolar (d : D) : q.polarBilin d (e (P x))=q.polarBilin d (Q x) := by
        obtain ⟨s,hs,hsd⟩:=d.property
        have hd : (d:V)=e (P s):=hsd.symm.trans (he ⟨s,hs⟩).symm
        rw [hd,quadratic_isometry_polar,hp,he ⟨s,hs⟩]
      obtain ⟨a,ha,hfix⟩:=quadratic_move_fixing q hnd D (e (P x)) (Q x) hu hw
        ((e.map_app (P x)).trans (hq x)) hpolar (by omega)
      let T:=S⊔Submodule.span QField {x}
      have hT : ∀ t : T,(e.trans a) (P t)=Q t := by
        intro t
        obtain ⟨s,hs|hs⟩:=binary_span_decompose S x t t.property
        · change a (e (P (t:B)))=Q t
          rw [hs,he s]
          exact hfix ⟨Q s,⟨s,s.property,rfl⟩⟩
        · change a (e (P (t:B)))=Q t
          rw [hs,map_add,map_add,map_add,ha,he s,hfix ⟨Q s,⟨s,s.property,rfl⟩⟩]
          exact (map_add Q (s:B) x).symm
      have hdimT : Module.finrank QField T=Module.finrank QField S+1:=
        Submodule.finrank_sup_span_singleton hx
      have hdimB := Submodule.finrank_le T
      exact ih _ (by omega) T rfl (e.trans a) hT
  apply extend _ ⊥ rfl (QuadraticMap.IsometryEquiv.refl q)
  intro s
  have hs : (s:B)=0:=s.property
  simp only [hs,map_zero]

end
end Lax793645Proofs.Simplifications
