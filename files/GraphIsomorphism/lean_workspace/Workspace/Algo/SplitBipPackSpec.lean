import Workspace.Algo.SplitBipPackNames

/-! Read a packed graph through its point and block enumerations. The
constructor below keeps all point colors, block colors, adjacency entries,
and hint values of the mathematical child graph.
-/
set_option quotPrecheck false
namespace Algo
open Babai RAM
open scoped Classical

theorem sbipRestore_mem (p : RawConfig) (l : List ℕ) (hnd : l.Nodup)
    {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) :
    binColor (sbipRestore (p,l),(a,b)) =
      binColor (p,(rawLetterIndex (l,a),rawLetterIndex (l,b))) := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hb
  rw [sbipLetterIndex_get hnd ⟨i,hi⟩,sbipLetterIndex_get hnd ⟨j,hj⟩]
  exact sbipRestore_get p l hnd ⟨i,hi⟩ ⟨j,hj⟩

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) (point : ↥s → ℕ) (z : RawSbipPack)
    (eP : ↥G.V₁ ≃ Fin z.1.2.length) (eB : ↥G.blocks ≃ Fin z.2.1.length)
    (hp : Function.Injective point) (hlt : ∀ x, G.part₁ x → point x < z.1.1.length)
    (hl : z.1.2.Nodup) (heP : ∀ x, z.1.2[(eP x).val] = point x.val)

local notation "name" => sbipPackName G point z.1.1.length eB

include heP in
theorem sbipPack_point_mem (x : ↥G.V₁) : point x.val ∈ z.1.2 :=
  heP x ▸ List.getElem_mem (eP x).isLt

include heP in
theorem sbipPack_point_mem_iff (a : ℕ) : a ∈ z.1.2 ↔ ∃ x : ↥G.V₁,point x.val = a := by
  constructor
  · intro ha
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
    obtain ⟨x,hx⟩ := eP.surjective ⟨i,hi⟩
    exact ⟨x,by simpa only [hx] using (heP x).symm⟩
  · rintro ⟨x,rfl⟩
    exact sbipPack_point_mem G point z eP heP x

include hlt heP in
theorem sbipPack_left_bound : ∀ a ∈ z.1.2,a < z.1.1.length := by
  intro a ha
  obtain ⟨x,rfl⟩ := (sbipPack_point_mem_iff G point z eP heP a).mp ha
  exact hlt x.val x.property

include hlt heP in
theorem sbipPackName_mem_vertices (A : G.Vtx) : name A ∈ sbipPackVertices z := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point z.1.1.length eB x hx]
    exact List.mem_append_left _ (sbipPack_point_mem G point z eP heP ⟨x,hx⟩)
  · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩]
    apply List.mem_append_right
    apply (sbipPackBlocks_mem z _).mpr
    have hh := (eB ⟨A,hA⟩).isLt
    omega

include hlt heP in
theorem sbipPack_block_not_point (B : ↥G.blocks) :
    z.1.1.length + (eB B).val ∉ z.1.2 := by
  intro hm
  have hh := sbipPack_left_bound G point z eP hlt heP _ hm
  omega

include hlt in
theorem sbipPack_point_not_block (x : ↥G.V₁) : point x.val ∉ sbipPackBlocks z := by
  intro hm
  have hh := (sbipPackBlocks_mem z _).mp hm
  have hp := hlt x.val x.property
  omega

include hlt heP in
theorem sbipPackNames_left (A : G.Vtx) :
    name A ∈ (sbipPack z).1.1.1 ↔ ∃ x,G.part₁ x ∧ A.val = {x} := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point z.1.1.length eB x hx]
    exact iff_of_true (sbipPack_point_mem G point z eP heP ⟨x,hx⟩) ⟨x,hx,rfl⟩
  · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩]
    apply iff_of_false (sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩)
    rintro ⟨x,hx,rfl⟩
    exact G.blocks_off₁ _ hA x rfl hx

include hlt in
theorem sbipPackNames_right (A : G.Vtx) :
    name A ∈ (sbipPack z).1.1.2.1 ↔ A.val ∈ G.blocks := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point z.1.1.length eB x hx]
    apply iff_of_false (sbipPack_point_not_block G point z hlt ⟨x,hx⟩)
    intro hB
    exact G.blocks_off₁ _ hB x rfl hx
  · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩]
    apply iff_of_true _ hA
    exact (sbipPackBlocks_mem z _).2 ⟨by omega,by have hh := (eB ⟨A,hA⟩).isLt; omega⟩

include hp hlt hl heP in
/-- Exact graph fields suffice for the common refinement's complete naming predicate. -/
theorem sbipPack_colorNames
    (hf : ∀ x,labAt z.2.2.2.1 (point x) = G.f x)
    (hg : ∀ B : ↥G.blocks,labAt z.2.2.2.2.1 (eB B) = G.g B.val)
    (hE : ∀ x : ↥G.V₁, ∀ B : ↥G.blocks,
      sbipMatrixEntry ((z.1.2,sbipPackBlocks z,z.2.2.1),(eP x,eB B)) =
        if (x.val,B.val) ∈ G.E then 1 else 0)
    (hh : ∀ A B : G.Vtx,binColor (z.2.2.2.2.2,
      (rawLetterIndex (sbipPackVertices z,name A),rawLetterIndex (sbipPackVertices z,name B))) =
        G.h A.val B.val) : SbipGraphColorNames G (sbipPack z).1 name := by
  have hnd := sbipPackVertices_nodup z hl (sbipPack_left_bound G point z eP hlt heP)
  refine ⟨sbipPackName_injective G point z.1.1.length eB hp hlt,?_,?_,?_⟩
  · rintro ⟨A,hA⟩
    rcases hA with ⟨x,hx,rfl⟩ | hA
    · rw [sbipPackName_point G point z.1.1.length eB x hx]
      have hm := sbipPack_point_mem G point z eP heP ⟨x,hx⟩
      simp only [sbipGraphVertexColor,sbipPack,decide_eq_true_eq,if_pos hm]
      rw [hf,VColBipBlk.initVtxColor,if_pos ⟨x,hx,rfl⟩]
      simp
    · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩]
      have hn := sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩
      have hm : z.1.1.length + (eB ⟨A,hA⟩).val ∈ sbipPackBlocks z :=
        (sbipPackBlocks_mem z _).mpr ⟨by omega,by have hh := (eB ⟨A,hA⟩).isLt; omega⟩
      have hns : ¬ ∃ x,G.part₁ x ∧ A = {x} := by
        rintro ⟨x,hx,rfl⟩
        exact G.blocks_off₁ _ hA x rfl hx
      change (if decide (_ ∈ z.1.2) then _ else if decide (_ ∈ sbipPackBlocks z) then _ else _) = _
      rw [if_neg (by simpa using hn),if_pos (by simpa using hm),sbipPack_blockColor,hg,
        VColBipBlk.initVtxColor,if_neg hns,if_pos hA]
  · rintro ⟨A,hA⟩ ⟨B,hB⟩
    rcases hA with ⟨x,hx,rfl⟩ | hA <;> rcases hB with ⟨y,hy,rfl⟩ | hB
    · rw [sbipPackName_point G point z.1.1.length eB x hx,
        sbipPackName_point G point z.1.1.length eB y hy]
      rw [sbipGraphEdge_off _ _ _ (Or.inr (sbipPack_point_not_block G point z hlt ⟨y,hy⟩))]
      symm
      apply if_neg
      rintro ⟨v,hv,hvx,hE⟩
      exact G.blocks_off₁ _ (G.E_sub _ hE).2 y rfl hy
    · rw [sbipPackName_point G point z.1.1.length eB x hx,
        sbipPackName_block G point z.1.1.length eB ⟨B,hB⟩]
      have hli : (sbipPack z).1.1.1[(eP ⟨x,hx⟩).val] = point x := heP ⟨x,hx⟩
      have hri := sbipPackBlocks_get z (eB ⟨B,hB⟩)
      have hedge := sbipGraphEdge_get (sbipPack z).1 hl (sbipPackBlocks_nodup z)
        (eP ⟨x,hx⟩) ⟨(eB ⟨B,hB⟩).val,by simpa using (eB ⟨B,hB⟩).isLt⟩
      rw [hli] at hedge
      simp only [sbipPack_blocks] at hedge
      rw [hri] at hedge
      rw [hedge]
      change (if sbipMatrixEntry ((z.1.2,sbipPackBlocks z,z.2.2.1),
        (eP ⟨x,hx⟩,eB ⟨B,hB⟩)) = 0 then 0 else 1) = _
      rw [hE]
      have he : (∃ v,G.part₁ v ∧ ({x} : Set ↥s) = {v} ∧ (v,B) ∈ G.E) ↔ (x,B) ∈ G.E := by
        constructor
        · rintro ⟨v,_,hv,he⟩
          rwa [← Set.singleton_injective hv] at he
        · intro he; exact ⟨x,hx,rfl,he⟩
      simp only [VColBipBlk.initEdge,he]
      by_cases hexy : (x,B) ∈ G.E <;> simp [hexy]
    · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩,
        sbipPackName_point G point z.1.1.length eB y hy]
      rw [sbipGraphEdge_off _ _ _ (Or.inl (sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩))]
      symm
      apply if_neg
      rintro ⟨x,hx,rfl,_⟩
      exact G.blocks_off₁ _ hA x rfl hx
    · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩,
        sbipPackName_block G point z.1.1.length eB ⟨B,hB⟩]
      rw [sbipGraphEdge_off _ _ _ (Or.inl (sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩))]
      symm
      apply if_neg
      rintro ⟨x,hx,rfl,_⟩
      exact G.blocks_off₁ _ hA x rfl hx
  · intro A B
    change binColor (sbipRestore (z.2.2.2.2.2,sbipPackVertices z),(name A,name B)) = _
    rw [sbipRestore_mem _ _ hnd (sbipPackName_mem_vertices G point z eP eB hlt heP A)
      (sbipPackName_mem_vertices G point z eP eB hlt heP B)]
    exact hh A B

include hlt heP in
theorem sbipPack_vertex_members
    (hd : ∀ B : ↥G.blocks,∀ a,a ∈ z.2.1[(eB B).val] ↔ ∃ x ∈ B.val,point x = a)
    (A : G.Vtx) (a : ℕ) :
    a ∈ sbipVertexMembers (sbipPack z,name A) ↔ ∃ x ∈ A.val,point x = a := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point z.1.1.length eB x hx,
      sbipVertexMembers_point _ (sbipPack_point_mem G point z eP heP ⟨x,hx⟩)]
    simp only [List.mem_singleton,Set.mem_singleton_iff,exists_eq_left]
    exact eq_comm
  · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩,
      sbipVertexMembers_block _ (sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩),
      sbipPack_dict,sbipDictGet_get]
    exact hd ⟨A,hA⟩ a

include hlt heP in
theorem sbipPack_vertex_members_nodup
    (hd : ∀ B : ↥G.blocks,z.2.1[(eB B).val].Nodup) (A : G.Vtx) :
    (sbipVertexMembers (sbipPack z,name A)).Nodup := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rw [sbipPackName_point G point z.1.1.length eB x hx,
      sbipVertexMembers_point _ (sbipPack_point_mem G point z eP heP ⟨x,hx⟩)]
    exact List.nodup_singleton _
  · rw [sbipPackName_block G point z.1.1.length eB ⟨A,hA⟩,
      sbipVertexMembers_block _ (sbipPack_block_not_point G point z eP eB hlt heP ⟨A,hA⟩),
      sbipPack_dict,sbipDictGet_get]
    exact hd ⟨A,hA⟩

include hlt heP in
theorem sbipPackNames_cover (a : ℕ) : a ∈ sbipPackVertices z ↔ ∃ A : G.Vtx,name A = a := by
  constructor
  · intro ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨x,hx⟩ := (sbipPack_point_mem_iff G point z eP heP a).mp ha
      exact ⟨⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩,
        (sbipPackName_point G point z.1.1.length eB x.val x.property).trans hx⟩
    · obtain ⟨lo,hi⟩ := (sbipPackBlocks_mem z a).mp ha
      let i : Fin z.2.1.length := ⟨a-z.1.1.length,by omega⟩
      let B := eB.symm i
      refine ⟨⟨B.val,Or.inr B.property⟩,?_⟩
      rw [sbipPackName_block G point z.1.1.length eB B]
      simp only [B,Equiv.apply_symm_apply,i]
      omega
  · rintro ⟨A,rfl⟩
    exact sbipPackName_mem_vertices G point z eP eB hlt heP A

end
end Algo
