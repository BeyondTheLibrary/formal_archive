import Workspace.Algo.SplitImprimitiveStoredNames

/-! A selected graph's column positions biject its actual mathematical
blocks. Under this bijection the stored dictionary gives the entire block,
and the unchanged matrix reads exactly the mathematical edge relation.
Point colors are specified on the whole ambient carrier.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} {q : RawImpGraph} {Y : VColBipBlk ↥s ℕ}
    (hr : ImpGraphRep X name₁ name₂ r q Y)

/-- Each output position names the union of its stored old columns. -/
def impStoredBlockAt (i : Fin q.2.1.length) : ↥Y.blocks :=
  ⟨impColumnSet X name₂ q.2.1[i.val],by
    rw [← hr.blocks]
    exact ⟨q.2.1[i.val],List.getElem_mem i.isLt,rfl⟩⟩

theorem impStoredBlockAt_bijective : Function.Bijective (impStoredBlockAt hr) := by
  constructor
  · intro i j he
    have hh := hr.columns_inj (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (congrArg Subtype.val he)
    exact Fin.ext ((List.Nodup.getElem_inj_iff hr.columns_nodup).mp hh)
  · intro B
    obtain ⟨g,hg,hB⟩ := (show B.val ∈ impColumnSet X name₂ '' {g | g ∈ q.2.1} from
      hr.blocks.symm ▸ B.property)
    obtain ⟨i,hi,hig⟩ := List.getElem_of_mem hg
    exact ⟨⟨i,hi⟩,Subtype.ext (by change impColumnSet X name₂ q.2.1[i] = B.val; rw [hig,hB])⟩

noncomputable def impStoredBlockEquiv : Fin q.2.1.length ≃ ↥Y.blocks :=
  Equiv.ofBijective (impStoredBlockAt hr) (impStoredBlockAt_bijective hr)

@[simp] theorem impStoredBlockEquiv_apply (i : Fin q.2.1.length) :
    (impStoredBlockEquiv hr i).val = impColumnSet X name₂ q.2.1[i.val] := rfl

variable {point : ↥s → ℕ} {d : List (List ℕ)}
    (hn : ImpNames X name₁ name₂ r) (hd : ImpStoredNames X name₁ name₂ point d)
    (hq : q ∈ impStep2Graphs r) (dom : List ℕ)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)

include hn hd hq in
theorem impStoredGraph_block_members (i : Fin q.2.1.length) (u : ℕ) :
    u ∈ sbipDictGet ((impStoredGraph ((dom,d),q)).2,dom.length+i) ↔
      ∃ x ∈ (impStoredBlockEquiv hr i).val, point x = u :=
  impStoredGraph_column hn hd hq dom i u

include hr hd he₁ in
theorem impStoredGraph_point_get (x : ↥X.Pt₁) :
    rawGet ((impStoredGraph ((dom,d),q)).1.1.1,e₁ x) = point x.val := by
  rw [impStoredGraph_left,hr.left]
  simp only [sbipDictPoints,rawGet]
  rw [List.getD_eq_getElem _ _ (by simpa using (e₁ x).isLt),List.getElem_map,he₁]
  exact impStored_point hd x

include hr hn he₁ in
theorem impStoredGraph_matrix_spec (x : ↥X.Pt₁) (i : Fin q.2.1.length) :
    sbipMatrixEntry ((impStoredGraph ((dom,d),q)).1.1,(e₁ x,i)) =
      if (x.val,(impStoredBlockEquiv hr i).val) ∈ Y.E then 1 else 0 := by
  change (q.2.2.getD (e₁ x) []).getD i 0 = _
  rw [hr.matrix,hr.left]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem (e₁ x).isLt,Option.map_some,Option.getD_some,he₁,
    List.getElem?_eq_getElem i.isLt]
  have he : (∃ y : ↥X.Pt₁, name₁ y = name₁ x ∧
      (y.val,impColumnSet X name₂ q.2.1[i.val]) ∈ Y.E) ↔
        (x.val,(impStoredBlockEquiv hr i).val) ∈ Y.E := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hh : y = x := hn.inj₁ hy
      subst y
      exact he
    · intro hx
      exact ⟨x,rfl,hx⟩
  simp only [he]

include hr in
/-- Section 9.6 resets the point colors on every ambient point, not only
on points in the retained first part. -/
theorem impStoredGraph_full_point_colors (x : ↥s) :
    labAt (impStoredGraph ((dom,d),q)).1.2.1 (point x) = Y.f x := by
  rw [impStoredGraph_pointColor,hr.point_colors]

theorem impStoredGraph_block_colors (i : Fin q.2.1.length) :
    labAt (impStoredGraph ((dom,d),q)).1.2.2.1 (dom.length+i) =
      Y.g (impStoredBlockEquiv hr i).val := by
  rw [impStoredGraph_blockColor,hr.block_colors]

end
end Algo
