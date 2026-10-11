import Lax342547.TableInjection
import Lax342547Proofs.RawContractions
import Lax342547Proofs.TableSpaces

namespace Lax342547Proofs.TableInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.RawContractions Lax342547.FiniteInjection Lax342547.TableInjection

set_option backward.isDefEq.respectTransparency false

theorem failure_iff_not_injective {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    (D : Submodule Binary (B → Binary)) (P : Matrix N B Binary) (Y : Matrix N H Binary)
    (S : Submodule Binary (H → Binary)) (hP : Function.Injective P.mulVec) :
    pinFailure (D.map P.mulVecLin) Y S ↔
      ¬ Function.Injective (S.mkQ.comp (Y.transpose.mulVecLin.comp (P.mulVecLin.comp D.subtype))) := by
  classical
  let f := S.mkQ.comp (Y.transpose.mulVecLin.comp (P.mulVecLin.comp D.subtype))
  have hz (v : D) : f v = 0 ↔ Y.transpose.mulVec (P.mulVec v.val) ∈ S := by
    exact Submodule.Quotient.mk_eq_zero S
  constructor
  · rintro ⟨v,hv,hY⟩ hinj
    obtain ⟨d,hd,he⟩ := v.property
    have he' : P.mulVec d = v.val := he
    have hf : f ⟨d,hd⟩ = 0 := (hz ⟨d,hd⟩).mpr (by rw [he']; exact hY)
    have hd0 : (⟨d,hd⟩ : D) = 0 := hinj (hf.trans f.map_zero.symm)
    apply hv
    rw [← he]
    change P.mulVec d = 0
    have hdval : d = 0 := congrArg Subtype.val hd0
    rw [hdval,Matrix.mulVec_zero]
  · intro h
    have hn : ∃ d : D,d ≠ 0 ∧ f d = 0 := by
      by_contra! hc
      apply h
      exact LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun d hd => by
        by_contra hn
        exact hc d hn hd))
    obtain ⟨d,hd,hf⟩ := hn
    refine ⟨⟨P.mulVec d.val,⟨d.val,d.property,rfl⟩⟩,?_,(hz d).mp hf⟩
    intro he
    apply hd
    apply Subtype.ext
    exact hP (by simpa using he)

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
  {E : Matrix B B Binary}

theorem primalMatrix_injective (A : Fin 2 → Comp → Frame B H N E)
    (e : Comp) (i : Fin 2) (s : Bool) : Function.Injective (primalMatrix A e i s).mulVec := by
  cases s
  · intro v w h
    exact congrArg Prod.fst ((A i e).minus_injective (a₁ := (v,0)) (a₂ := (w,0)) (by simpa [primalMatrix] using h))
  · intro v w h
    exact congrArg Prod.fst ((A i e).plus_injective (a₁ := (v,0)) (a₂ := (w,0)) (by simpa [primalMatrix] using h))

theorem rawTable_extends (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) : Extends (rawForms A Bmap) (rawTable P Q A Bmap) :=
  ⟨fun _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem raw_row (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) :
    rowChannels P Q (e,true) (e,false) ((rawTable P Q A Bmap).forward e) i z =
      (Bmap z e).Y.transpose.mulVecLin.comp ((A i e).P.mulVecLin.comp (pinnedPrimal P i (e,true)).subtype) := by
  ext d h
  change fullPlus (rawForms A Bmap) e i z d.val h = _
  rw [Lax342547Proofs.RawContractions.raw_plus]
  simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,Submodule.subtype_apply]

theorem raw_column (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) :
    columnChannels Q P (e,true) (e,false) ((rawTable P Q A Bmap).reverse e) z i =
      (Bmap z e).X.transpose.mulVecLin.comp ((A i e).Q.mulVecLin.comp (pinnedPrimal P i (e,false)).subtype) := by
  ext d h
  change fullMinus (rawForms A Bmap) e i z d.val h = _
  rw [Lax342547Proofs.RawContractions.raw_minus]
  simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,Submodule.subtype_apply]

/--
---
conclusion: Lax342547.TableInjection.actual_table_injecting_iff
---
-/
theorem actual_table_injecting_iff (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) :
    Injecting (rawTable P Q A Bmap) ↔ ∀ e i z s role,¬ Failed P Q A Bmap e i z s role := by
  classical
  have ht (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
      (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) (s : Bool) :
      ¬ pinFailure (primalImage P A e i s) (oppositeChannel Bmap e z s) (protectedChannel Q z (e,s)) ↔
      Function.Injective ((protectedChannel Q z (e,s)).mkQ.comp
        ((oppositeChannel Bmap e z s).transpose.mulVecLin.comp
          ((primalMatrix A e i s).mulVecLin.comp (pinnedPrimal P i (e,s)).subtype))) := by
    unfold primalImage
    rw [failure_iff_not_injective _ _ _ _ (primalMatrix_injective A e i s)]
    exact not_not
  have hplus (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
      (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) := ht P Q A Bmap e i z true
  have hminus (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
      (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) := ht P Q A Bmap e i z false
  simp only [primalMatrix,oppositeChannel,if_true, Bool.false_eq_true,if_false,
     ] at hplus hminus
  simp only [Injecting,Failed]
  constructor
  · intro h e i z s role
    cases role <;> cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
    · apply (hminus P Q A Bmap e i z).mpr
      simpa only [raw_column] using (h e i z).2.1
    · apply (hplus P Q A Bmap e i z).mpr
      simpa only [raw_row] using (h e i z).1
    · apply (hminus Q P Bmap A e i z).mpr
      have hh := (h e i z).2.2.2
      change Function.Injective ((protectedChannel P z (e,false)).mkQ.comp
        (columnChannels P Q (e,true) (e,false) ((rawTable Q P Bmap A).reverse e) z i)) at hh
      simpa only [raw_column] using hh
    · apply (hplus Q P Bmap A e i z).mpr
      have hh := (h e i z).2.2.1
      change Function.Injective ((protectedChannel P z (e,true)).mkQ.comp
        (rowChannels Q P (e,true) (e,false) ((rawTable Q P Bmap A).forward e) i z)) at hh
      simpa only [raw_row] using hh
  · intro h e i z
    refine ⟨?_,?_,?_,?_⟩
    · rw [raw_row]
      exact (hplus P Q A Bmap e i z).mp (h e i z true false)
    · rw [raw_column]
      exact (hminus P Q A Bmap e i z).mp (h e i z false false)
    · change Function.Injective ((protectedChannel P z (e,true)).mkQ.comp
        (rowChannels Q P (e,true) (e,false) ((rawTable Q P Bmap A).forward e) i z))
      rw [raw_row]
      exact (hplus Q P Bmap A e i z).mp (h e i z true true)
    · change Function.Injective ((protectedChannel P z (e,false)).mkQ.comp
        (columnChannels P Q (e,true) (e,false) ((rawTable Q P Bmap A).reverse e) z i))
      rw [raw_column]
      exact (hminus Q P Bmap A e i z).mp (h e i z false true)

/--
---
conclusion: Lax342547.TableInjection.admissible_injection_iff
---
Admissibility already fixes every pinned-primal versus channel entry;
no agreement on the unpinned channel-by-channel block is needed.
-/
theorem admissible_injection_iff (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (T : Table P Q)
    (hT : Admissible T Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation A Bmap) :
    Injecting T ↔ Injecting (rawTable P Q A Bmap) := by
  classical
  have hr (e : Comp) (i z : Fin 2) :
      rowChannels P Q (e,true) (e,false) (T.forward e) i z =
      rowChannels P Q (e,true) (e,false) ((rawTable P Q A Bmap).forward e) i z := by
    ext d h
    exact hT.1 e (tablePinnedPrimal P (e,true) i d)
      (tableChannel Q (e,false) z (Pi.single h 1)) (Or.inl d.property)
  have hc (e : Comp) (i z : Fin 2) :
      columnChannels Q P (e,true) (e,false) (T.reverse e) z i =
      columnChannels Q P (e,true) (e,false) ((rawTable P Q A Bmap).reverse e) z i := by
    ext d h
    exact hT.2 e (tableChannel Q (e,true) z (Pi.single h 1))
      (tablePinnedPrimal P (e,false) i d) (Or.inr d.property)
  have hr' (e : Comp) (i z : Fin 2) :
      rowChannels Q P (e,true) (e,false) (T.reverse e) i z =
      rowChannels Q P (e,true) (e,false) ((rawTable P Q A Bmap).reverse e) i z := by
    ext d h
    exact hT.2 e (tablePinnedPrimal Q (e,true) i d)
      (tableChannel P (e,false) z (Pi.single h 1)) (Or.inl d.property)
  have hc' (e : Comp) (i z : Fin 2) :
      columnChannels P Q (e,true) (e,false) (T.forward e) z i =
      columnChannels P Q (e,true) (e,false) ((rawTable P Q A Bmap).forward e) z i := by
    ext d h
    exact hT.1 e (tableChannel P (e,true) z (Pi.single h 1))
      (tablePinnedPrimal Q (e,false) i d) (Or.inr d.property)
  simp only [Injecting,hr,hc,hr',hc']

end Lax342547Proofs.TableInjection
