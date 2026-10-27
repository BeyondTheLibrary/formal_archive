import Workspace.Algo.AggNodeGuideEquiv

/-! # The finite tuple domain of the local-guide construction

Enumerate ordered tuples on the supplied fixed-point list and retain the
injective ones. The arity guard is measured in the original string domain,
as in the certificate phase, so this computation has a uniform
quasipolynomial RAM bound even when the giant domain is much smaller.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Inputs are the arity witness, original domain, and tuple vertex list. -/
def aggnGuideRows (c : ℕ) (p : RawAggTestInput) : List (List ℕ) :=
  ((aggTable c p).2.map Prod.fst).filter wftNodup

theorem aggnQuasiFun_guideRows (c : ℕ) : QuasiFun (aggnGuideRows c) :=
  ((aggQuasiFun_table c).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))).comp_poly
    (PolyFun.filter wftPolyFun_nodup)

theorem aggnGuideRows_mem {c : ℕ} {ks dom D row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    row ∈ aggnGuideRows c (ks,dom,D) ↔
      row.length = ks.length ∧ (∀ a ∈ row,a ∈ D) ∧ row.Nodup := by
  rw [aggnGuideRows,aggTable_of_guard (a := (ks,dom,D)) hg,keys_tupleTable,
    List.mem_filter,mem_tuplesOf,wftNodup_eq_true_iff]
  exact and_assoc

theorem aggnGuideRows_nodup {c : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hD : D.Nodup) :
    (aggnGuideRows c (ks,dom,D)).Nodup := by
  rw [aggnGuideRows,aggTable_of_guard (a := (ks,dom,D)) hg,keys_tupleTable]
  exact (nodup_tuplesOf hD _).filter _

theorem aggnGuideRows_length {c : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    (aggnGuideRows c (ks,dom,D)).length ≤ D.length ^ ks.length := by
  rw [aggnGuideRows,aggTable_of_guard (a := (ks,dom,D)) hg,keys_tupleTable]
  simpa only [length_tuplesOf] using List.length_filter_le wftNodup (tuplesOf D ks.length)

theorem aggnGuideRows_name {c m : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (u : Fin ks.length ↪ ↥(winSet m D)) :
    aggnTupleName (fun i => (u i).val) ∈ aggnGuideRows c (ks,dom,D) := by
  apply (aggnGuideRows_mem hg).mpr
  refine ⟨aggnTupleName_length _,?_,aggnTupleName_nodup (Subtype.val_injective.comp u.injective)⟩
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact (u i).property

/-- Every enumerated raw row is the name of an injective tuple on the supplied set. -/
theorem aggnGuideRows_complete {c m : ℕ} {ks dom D row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hlt : ∀ a ∈ D,a < m)
    (hr : row ∈ aggnGuideRows c (ks,dom,D)) :
    ∃ u : Fin ks.length ↪ ↥(winSet m D),aggnTupleName (fun i => (u i).val) = row := by
  obtain ⟨hlen,hsub,hnd⟩ := (aggnGuideRows_mem hg).mp hr
  let u : Fin ks.length ↪ ↥(winSet m D) :=
    { toFun := fun i =>
        ⟨⟨row[i.val]'(by omega),hlt _ (hsub _ (List.getElem_mem (by omega)))⟩,
          hsub _ (List.getElem_mem (by omega))⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact (List.Nodup.getElem_inj_iff hnd).mp (congrArg (fun a => a.val.val) hij) }
  refine ⟨u,?_⟩
  apply List.ext_getElem
  · exact (aggnTupleName_length _).trans hlen.symm
  · intro i hi hi'
    simp only [aggnTupleName,List.getElem_ofFn]
    rfl

end Algo
