import Workspace.Algo.SplitDesignCase3

/-! The Case 3 selector acts on old block names. Its test is exactly the
absolute symmetry-defect test of Reduce-Part2-by-Color. -/
namespace Algo
open Babai RAM

theorem splitMapNames_mem {l L : List ℕ} (hnd : l.Nodup)
    (hL : ∀ i ∈ L, i < l.length) (i : Fin l.length) :
    l[i.val] ∈ L.map (fun j => labAt l j) ↔ i.val ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨j,hj,hji⟩
    have hji' : j = i.val := (List.Nodup.getElem_inj_iff hnd).1 (by
      simpa only [labAt,List.getD_eq_getElem _ _ (hL j hj)] using hji)
    rwa [hji'] at hj
  · intro hi
    exact ⟨i.val,hi,by simp [labAt,i.isLt]⟩

theorem splitMapNames_nodup {l L : List ℕ} (hnd : l.Nodup) (hLn : L.Nodup)
    (hL : ∀ i ∈ L, i < l.length) : (L.map (fun i => labAt l i)).Nodup := by
  apply List.Nodup.map_on ?_ hLn
  intro i hi j hj he
  exact (List.Nodup.getElem_inj_iff hnd).1 (by
    simpa only [labAt,List.getD_eq_getElem _ _ (hL i hi),
      List.getD_eq_getElem _ _ (hL j hj)] using he)

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)

def designReadFirstSet (o : RawDesignReadOut) : Set (Set ↥s) :=
  Subtype.val '' {B : ↥X.blocks | (e₂ B).val ∈ designReadFirst o}

theorem designReadFirstSet_sub (o : RawDesignReadOut) :
    designReadFirstSet e₂ o ⊆ X.blocks := by
  rintro B ⟨C,hC,rfl⟩
  exact C.property

theorem designReadFirstSet_mem (o : RawDesignReadOut) (B : ↥X.blocks) :
    B.val ∈ designReadFirstSet e₂ o ↔ (e₂ B).val ∈ designReadFirst o := by
  simp only [designReadFirstSet,Set.mem_image,Set.mem_setOf_eq]
  exact ⟨fun ⟨C,hC,hCB⟩ => (Subtype.ext hCB : C = B) ▸ hC,fun hB => ⟨B,hB,rfl⟩⟩

include hw he₂ in
theorem designReadNamedFirst_mem (o : RawDesignReadOut)
    (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) (B : ↥X.blocks) :
    name₂ B ∈ designReadNamedFirst (r,o) ↔ B.val ∈ designReadFirstSet e₂ o := by
  rw [designReadFirstSet_mem,← he₂ B]
  exact splitMapNames_mem hw.right_nodup hL (e₂ B)

include hw in
theorem designReadNamedFirst_nodup (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    (designReadNamedFirst (r,o)).Nodup := splitMapNames_nodup hw.right_nodup hnd hL

theorem designReadNamedFirst_sub (o : RawDesignReadOut)
    (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    ∀ a ∈ designReadNamedFirst (r,o), a ∈ r.2.2 := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.1 ha
  rw [labAt,List.getD_eq_getElem _ _ (hL i hi)]
  exact List.getElem_mem (hL i hi)

include h hw he₂ in
theorem designReadNamedHint_spec (o : RawDesignReadOut) (B C : ↥X.blocks) :
    binColor (designReadNamedHint (r,o),(name₂ B,name₂ C)) =
      designReadHintAt (o,(e₂ B,e₂ C)) := by
  rw [designReadNamedHint_get _ ((h.right _).2 ⟨B,rfl⟩) ((h.right _).2 ⟨C,rfl⟩)]
  simp only [designReadNamedHintAt,designBlockIndex_spec h e₂ he₂ hw.right_nodup]

include h hw he₂ in
theorem designReadFirstEquiv_exists (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    ∃ eG : ↥(designReadFirstSet e₂ o) ≃ Fin (designReadNamedFirst (r,o)).length,
      ∀ B, (designReadNamedFirst (r,o))[(eG B).val] =
        name₂ ⟨B.val,designReadFirstSet_sub e₂ o B.property⟩ := by
  apply splitNameEquiv_exists
    (fun B : ↥(designReadFirstSet e₂ o) => name₂ ⟨B.val,designReadFirstSet_sub e₂ o B.property⟩)
    (fun B C hh => Subtype.ext (congrArg (fun D : ↥X.blocks => D.val) (h.inj₂ hh)))
    _ (designReadNamedFirst_nodup hw o hnd hL)
  intro a
  constructor
  · intro ha
    obtain ⟨B,rfl⟩ := (h.right a).1 (designReadNamedFirst_sub o hL a ha)
    exact ⟨⟨B.val,(designReadNamedFirst_mem hw e₂ he₂ o hL B).1 ha⟩,rfl⟩
  · rintro ⟨B,rfl⟩
    exact (designReadNamedFirst_mem hw e₂ he₂ o hL _).2 B.property

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadSelectFirst_spec (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    designReadSelectFirst (r,o) = true ↔ ((X.n₁ : ℚ) - 1) / 2 ≤
      (X.linkGraph.restrictBlk (designReadFirstSet e₂ o)).symDefect₁ := by
  obtain ⟨eG,heG⟩ := designReadFirstEquiv_exists h hw e₂ he₂ o hnd hL
  exact designRestricted_test h e₁ he₁ (designReadFirstSet_sub e₂ o)
    (designReadNamedFirst (r,o)) eG heG

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadSelected_mem (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length)
    (B : ↥X.blocks) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    name₂ B ∈ designReadSelected (r,o) ↔
      B.val ∈ reducePart2ByColorBlk X.linkGraph (designReadFirstSet e₂ o)
        (X.blocks \ designReadFirstSet e₂ o) := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  have ht := designReadSelectFirst_spec h hw e₁ he₁ e₂ he₂ o hnd hL
  unfold designReadSelected reducePart2ByColorBlk
  change (name₂ B ∈ if designReadSelectFirst (r,o) = true then _ else _) ↔
    B.val ∈ if ((X.n₁ : ℚ) - 1) / 2 ≤ _ then _ else _
  by_cases hb : designReadSelectFirst (r,o) = true
  · rw [if_pos hb,if_pos (ht.mp hb)]
    exact designReadNamedFirst_mem hw e₂ he₂ o hL B
  · rw [if_neg hb,if_neg (fun hh => hb (ht.mpr hh))]
    simp only [List.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,
      designReadNamedFirst_mem hw e₂ he₂ o hL B,Set.mem_diff]
    exact and_congr (iff_of_true ((h.right _).2 ⟨B,rfl⟩) B.property) Iff.rfl

end
end Algo
