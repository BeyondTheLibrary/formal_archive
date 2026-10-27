import Workspace.Algo.SplitBipGraphRead
import Workspace.Algo.SplitBipStep9Input

/-! The second refinement numbers blocks first and points second. These
positions give the version indices used by all three cases of step 9.
The original names remain in the graph that supplied this table. -/
namespace Algo
open Babai RAM

def sbipGraphCaseVertices (r : RawSbipGraph) : List ℕ := r.1.2.1 ++ r.1.1

def sbipGraphCaseTable (r : RawSbipGraph) : RawConfig :=
  sbipStep3 (sbipIndexed (sbipGraphInitial r,sbipGraphCaseVertices r))

def sbipGraphNumbered (r : RawSbipGraph) : RawUpccCase :=
  (sbipGraphCaseTable r,
    (List.range r.1.1.length).map (fun i => r.1.2.1.length + i),List.range r.1.2.1.length)

theorem polyFun_sbipGraphCaseVertices : PolyFun sbipGraphCaseVertices :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
    (polyFun_fst.comp polyFun_fst)).comp polyFun_append)

theorem polyFun_sbipGraphCaseTable : PolyFun sbipGraphCaseTable :=
  (polyFun_sbipGraphInitial.pair polyFun_sbipGraphCaseVertices).comp
    (sbipPoly_indexed.comp sbipPoly_step3)

theorem polyFun_sbipGraphNumbered : PolyFun sbipGraphNumbered := by
  have hl : PolyFun (fun r : RawSbipGraph => r.1.1) := polyFun_fst.comp polyFun_fst
  have hr : PolyFun (fun r : RawSbipGraph => r.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  exact polyFun_sbipGraphCaseTable.pair
    ((((hr.comp polyFun_length).pair (hl.comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_add)).pair (hr.comp polyFun_rangeLength))

@[simp] theorem sbipGraphCaseTable_length (r : RawSbipGraph) :
    (sbipGraphCaseTable r).1.length = (sbipGraphCaseVertices r).length := by
  simp [sbipGraphCaseTable,sbipStep3,fst_rawWLStable,sbipIndexed]

theorem sbipGraphNumbered_left (r : RawSbipGraph) (a : ℕ) :
    a ∈ (sbipGraphNumbered r).2.1 ↔ r.1.2.1.length ≤ a ∧ a < (sbipGraphCaseVertices r).length := by
  simp only [sbipGraphNumbered,List.mem_map,List.mem_range,sbipGraphCaseVertices,List.length_append]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hlo,hhi⟩
    exact ⟨a - r.1.2.1.length,by omega,by omega⟩

@[simp] theorem sbipGraphNumbered_right (r : RawSbipGraph) (a : ℕ) :
    a ∈ (sbipGraphNumbered r).2.2 ↔ a < r.1.2.1.length := List.mem_range

theorem sbipGraphNumbered_wf (r : RawSbipGraph) : (sbipGraphNumbered r).WF := by
  have ht := sbipStep3_wf (sbipIndexed_wf (sbipGraphInitial r) (sbipGraphCaseVertices r))
  refine ⟨?_,?_,List.nodup_range,?_,?_,?_⟩
  · simpa only [sbipGraphNumbered,sbipGraphCaseTable_length] using ht
  · exact List.nodup_range.map (fun a b h => Nat.add_left_cancel h)
  · intro a ha hb
    have ha' := (sbipGraphNumbered_left r a).1 ha
    have hb' := (sbipGraphNumbered_right r a).1 hb
    omega
  · intro a
    rw [List.mem_append,sbipGraphNumbered_left,sbipGraphNumbered_right]
    change _ ↔ a ∈ (sbipStep3 (sbipIndexed (sbipGraphInitial r,sbipGraphCaseVertices r))).1
    rw [ht.domMem]
    simp only [sbipGraphCaseVertices,List.length_append]
    omega
  · intro a
    simp [sbipGraphNumbered]

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) (r : RawSbipGraph) (name : G.Vtx → ℕ)
    (h : SbipGraphColorNames G r name)
    (e : G.Vtx ≃ Fin (sbipGraphCaseVertices r).length)
    (he : ∀ A, (sbipGraphCaseVertices r)[(e A).val]'(e A).isLt = name A)

include h he in
theorem sbipGraphCaseTable_spec (A B : G.Vtx) :
    binColor (sbipGraphCaseTable r,(e A,e B)) = G.wlNamed A B := by
  have hi : ∀ C D : G.Vtx,
      namedBin (sbipGraphCaseVertices r).length
        (sbipIndexed (sbipGraphInitial r,sbipGraphCaseVertices r)) (e C) (e D) =
          G.vtxInitColor C D := by
    intro C D
    have hm (A : G.Vtx) : name A ∈ sbipGraphVertices r := by
      have ha := he A ▸ List.getElem_mem (e A).isLt
      simpa only [sbipGraphCaseVertices,sbipGraphVertices,List.mem_append,or_comm] using ha
    rw [namedBin,sbipIndexed_get,he,he,sbipGraphInitial_get r (hm C) (hm D)]
    exact sbipGraphPair_spec G r name h C D
  exact sbipStep3_named G e (sbipIndexed_wf _ _) hi A B

def sbipGraphNumberedPoint (x : ↥G.V₁) : ℕ :=
  (e ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩).val

def sbipGraphNumberedBlock (B : ↥G.blocks) : ℕ := (e ⟨B.val,Or.inr B.property⟩).val

theorem sbipGraphNumberedPoint_injective : Function.Injective (sbipGraphNumberedPoint G r e) := by
  intro x y hh
  have hs := congrArg (fun A : G.Vtx => A.val) (e.injective (Fin.ext hh))
  exact Subtype.ext (Set.singleton_injective hs)

theorem sbipGraphNumberedBlock_injective : Function.Injective (sbipGraphNumberedBlock G r e) := by
  intro B C hh
  exact Subtype.ext (congrArg (fun A : G.Vtx => A.val) (e.injective (Fin.ext hh)))

include he in
theorem sbipGraphNumbered_left_names
    (hnd : (sbipGraphCaseVertices r).Nodup)
    (hleft : ∀ A, name A ∈ r.1.1 ↔ ∃ x, G.part₁ x ∧ A.val = {x}) :
    sbipGraphNumberedPoint G r e '' Set.univ = {a | a ∈ (sbipGraphNumbered r).2.1} := by
  have hpos (A : G.Vtx) : r.1.2.1.length ≤ (e A).val ↔ ∃ x, G.part₁ x ∧ A.val = {x} := by
    rw [← sbipSuffix_mem _ _ hnd (e A)]
    change (sbipGraphCaseVertices r)[(e A).val]'(e A).isLt ∈ r.1.1 ↔ _
    rw [he A]
    exact hleft A
  ext a
  constructor
  · rintro ⟨x,_,rfl⟩
    exact (sbipGraphNumbered_left r _).2
      ⟨(hpos _).2 ⟨x.val,x.property,rfl⟩,(e _).isLt⟩
  · intro ha
    obtain ⟨hlo,hhi⟩ := (sbipGraphNumbered_left r a).1 ha
    let A := e.symm ⟨a,hhi⟩
    have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
    obtain ⟨x,hx,hAx⟩ := (hpos A).1 (hA.symm ▸ hlo)
    refine ⟨⟨x,hx⟩,Set.mem_univ _,?_⟩
    have hv : (⟨{x},Or.inl ⟨x,hx,rfl⟩⟩ : G.Vtx) = A := Subtype.ext hAx.symm
    change (e ⟨{x},Or.inl ⟨x,hx,rfl⟩⟩).val = a
    rw [hv,hA]

include he in
theorem sbipGraphNumbered_right_names
    (hnd : (sbipGraphCaseVertices r).Nodup)
    (hright : ∀ A, name A ∈ r.1.2.1 ↔ A.val ∈ G.blocks) :
    sbipGraphNumberedBlock G r e '' Set.univ = {a | a ∈ (sbipGraphNumbered r).2.2} := by
  have hpos (A : G.Vtx) : (e A).val < r.1.2.1.length ↔ A.val ∈ G.blocks := by
    rw [← sbipPrefix_mem _ _ hnd (e A)]
    change (sbipGraphCaseVertices r)[(e A).val]'(e A).isLt ∈ r.1.2.1 ↔ _
    rw [he A]
    exact hright A
  ext a
  constructor
  · rintro ⟨B,_,rfl⟩
    exact (sbipGraphNumbered_right r _).2 ((hpos _).2 B.property)
  · intro ha
    have hlo := (sbipGraphNumbered_right r _).1 ha
    have hhi : a < (sbipGraphCaseVertices r).length := by
      simp only [sbipGraphCaseVertices,List.length_append]
      omega
    let A := e.symm ⟨a,hhi⟩
    have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
    have hb := (hpos A).1 (hA.symm ▸ hlo)
    refine ⟨⟨A.val,hb⟩,Set.mem_univ _,?_⟩
    have hv : (⟨A.val,Or.inr hb⟩ : G.Vtx) = A := Subtype.ext rfl
    change (e ⟨A.val,Or.inr hb⟩).val = a
    rw [hv,hA]

end
end Algo
