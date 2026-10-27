import Workspace.Algo.SplitBipPackSpec
import Workspace.Algo.SplitBipStoredDictionary
import Workspace.Algo.SplitUpccSpec
import Workspace.Algo.SplitNamedLists

/-! Section 9.2.2 treats each vertex of the second part as a singleton
block. This RAM adapter keeps its original point name in the member row,
copies its color, and starts with the zero hint required by the paper. -/
namespace Algo
open Babai RAM
open scoped Classical

abbrev RawSbipSingleton := List ℕ × (RawLab × RawUpccBip)

def sbipSingletonPack (z : RawSbipSingleton) : RawSbipPack :=
  ((z.1,z.2.2.1),(z.2.2.2.1.map (fun v => [v]),
    (z.2.2.2.2,(z.2.1,z.2.2.2.1.map (labAt z.2.1),([],[])))))

def sbipSingletonStored (z : RawSbipSingleton) : RawSbipStored :=
  sbipPack (sbipSingletonPack z)

theorem polyFun_sbipSingletonPack : PolyFun sbipSingletonPack := by
  have hg : PolyFun (fun z : RawSbipSingleton => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hc : PolyFun (fun z : RawSbipSingleton => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hr := (hg.comp polyFun_snd).comp polyFun_fst
  have hcolors := (hc.pair hr).comp (PolyFun.mapParam polyFun_labAt)
  exact (polyFun_fst.pair (hg.comp polyFun_fst)).pair
    ((hr.comp (PolyFun.map polyFun_singleton)).pair
      (((hg.comp polyFun_snd).comp polyFun_snd).pair
        (hc.pair (hcolors.pair (polyFun_const ([],[]))))))

theorem polyFun_sbipSingletonStored : PolyFun sbipSingletonStored :=
  polyFun_sbipSingletonPack.comp polyFun_sbipPack

section
variable {α : Type} (Y : VColBip α ℕ)

noncomputable def bipSingletonEquiv : ↥Y.V₂ ≃ ↥Y.toBlk.blocks :=
  Equiv.ofBijective (fun y => ⟨{y.val},y.val,y.property,rfl⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (Set.singleton_injective (congrArg Subtype.val h))
    · rintro ⟨B,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩)

@[simp] theorem bipSingletonEquiv_apply (y : ↥Y.V₂) :
    (bipSingletonEquiv Y y).val = {y.val} := rfl

theorem bipSingletonEquiv_symm (B : ↥Y.toBlk.blocks) :
    B.val = {(bipSingletonEquiv Y).symm B |>.val} := by
  exact (congrArg Subtype.val ((bipSingletonEquiv Y).apply_symm_apply B)).symm

end

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω} {n : ℕ}
    (e : ↥s ≃ Fin n) (ht : t ⊆ s) (Y : VColBip ↥t ℕ)
    (lab : RawLab) (g : RawUpccBip) (hr : UpccBipRep e lab g ht Y)
    (w : List ℕ) (hw : n ≤ w.length)

theorem upccSubName_injective : Function.Injective (upccSubName e ht) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun a : ↥s => a.val) (e.injective (Fin.ext h))

include hr hw in
/-- The singleton constructor satisfies the complete persistent-storage
contract, including all original point colors and exact block members. -/
theorem sbipSingletonStored_complete :
    SbipStoredRep Y.toBlk (upccSubName e ht) (sbipSingletonStored (w,(lab,g))) := by
  let point := upccSubName e ht
  have hp : Function.Injective point := upccSubName_injective e ht
  have hbound (x : ↥t) : point x < w.length :=
    lt_of_lt_of_le (e ⟨x.val,ht x.property⟩).isLt hw
  obtain ⟨hl,hright,hleft,hsecond,hcolor,hmat⟩ := hr
  have cover (S : Set ↥t) (l : List ℕ) (he : point '' S = {a | a ∈ l}) :
      ∀ a,a ∈ l ↔ ∃ x : ↥S,point x.val = a := by
    intro a
    rw [← show a ∈ point '' S ↔ a ∈ l from by rw [he]; rfl]
    constructor
    · rintro ⟨x,hx,hname⟩; exact ⟨⟨x,hx⟩,hname⟩
    · rintro ⟨x,hname⟩; exact ⟨x.val,x.property,hname⟩
  obtain ⟨ep,hep⟩ := splitNameEquiv_exists (fun x : ↥Y.V₁ => point x.val)
    (fun _ _ h => Subtype.ext (hp h)) g.1 hl (cover _ _ hleft)
  obtain ⟨er,her⟩ := splitNameEquiv_exists (fun x : ↥Y.V₂ => point x.val)
    (fun _ _ h => Subtype.ext (hp h)) g.2.1 hright (cover _ _ hsecond)
  let z := sbipSingletonPack (w,(lab,g))
  let eb : ↥Y.toBlk.blocks ≃ Fin z.2.1.length :=
    ((bipSingletonEquiv Y).symm.trans er).trans (finCongr (by simp [z,sbipSingletonPack]))
  have heb (B : ↥Y.toBlk.blocks) :
      g.2.1[(eb B).val]'(by simpa [z,sbipSingletonPack] using (eb B).isLt) =
        point ((bipSingletonEquiv Y).symm B).val := her _
  have hb (B : ↥Y.toBlk.blocks) := bipSingletonEquiv_symm Y B
  have hrows (B : ↥Y.toBlk.blocks) : (z.2.1[(eb B).val]).Nodup := by
    simp [z,sbipSingletonPack]
  have hmembers (B : ↥Y.toBlk.blocks) (a : ℕ) :
      a ∈ z.2.1[(eb B).val] ↔ ∃ x ∈ B.val,point x = a := by
    simp only [z,sbipSingletonPack,List.getElem_map,List.mem_singleton]
    rw [hb B]
    simp only [Set.mem_singleton_iff,exists_eq_left]
    exact (congrArg (fun v => a = v) (heb B)).to_iff.trans eq_comm
  have hbound' : ∀ x,Y.toBlk.part₁ x → point x < z.1.1.length :=
    fun x _ => hbound x
  have hcolors : ∀ x,labAt z.2.2.2.1 (point x) = Y.toBlk.f x := hcolor
  refine ⟨sbipPackName Y.toBlk point w.length eb,?_,?_,hcolors,?_,?_,?_,?_⟩
  · apply sbipPack_colorNames Y.toBlk point z ep eb hp hbound' hl hep hcolors
    · intro B
      change labAt (g.2.1.map (labAt lab)) (eb B) = Y.toBlk.g B.val
      rw [VColBip.toBlk_g_of_mem Y B.property,hb B]
      simp only [Set.image_singleton,csSup_singleton]
      simpa only [labAt,List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_eq_getElem (show (eb B).val < g.2.1.length by
          simpa [z,sbipSingletonPack] using (eb B).isLt),
        Option.map_some,Option.getD_some,heb] using hcolor ((bipSingletonEquiv Y).symm B).val
    · intro x B
      change (g.2.2.getD (ep x) []).getD (eb B) 0 = _
      rw [hmat]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_eq_getElem (ep x).isLt,Option.map_some,Option.getD_some,hep,
        List.getElem?_eq_getElem (show (eb B).val < g.2.1.length by
          simpa [z,sbipSingletonPack] using (eb B).isLt),heb]
      rw [hb B,VColBip.mem_toBlk_E_singleton]
      have he : (∃ u v : ↥t,point u = point x.val ∧
          point v = point ((bipSingletonEquiv Y).symm B).val ∧ (u,v) ∈ Y.E) ↔
          (x.val,((bipSingletonEquiv Y).symm B).val) ∈ Y.E := by
        constructor
        · rintro ⟨u,v,hu,hv,hE⟩
          rwa [hp hu,hp hv] at hE
        · intro hE; exact ⟨_,_,rfl,rfl,hE⟩
      simp only [point] at he
      rw [he]
    · intro A B
      rfl
  · exact sbipPack_storedDictionary Y.toBlk point z eb hrows hmembers
  · exact sbipPackVertices_nodup z hl
      (sbipPack_left_bound Y.toBlk point z ep hbound' hep)
  · exact sbipPackNames_left Y.toBlk point z ep eb hbound' hep
  · exact sbipPackNames_right Y.toBlk point z eb hbound'
  · exact sbipPackNames_cover Y.toBlk point z ep eb hbound' hep

end
end Algo
