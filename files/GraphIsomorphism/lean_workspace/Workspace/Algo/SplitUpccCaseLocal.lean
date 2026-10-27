import Workspace.Algo.SplitUpccCaseTransport

/-!
# Section 3.4.3: the local constituent used in Section 9.8

The first part of the paper's graph consists only of the dominant local
cell. The mathematical local constituent has the opposite order of parts.
The maps below send a point to its singleton and a block to itself.
-/

namespace Algo
open Babai RAM

section Local
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω} (X : UPCCObj s)

/-- Section 9.8, step 3: the paper's smaller graph, with the original point
and block types. Its reverse is the local constituent of Definition 3.4.18. -/
def upccCaseLocalMath (B : ↥X.blocks) :
    BipGraph ↥(X.linkClass B (X.mColor B)) ↥(X.blkClass B (X.lColor B)) :=
  ⟨{p | X.c p.2.val {p.1.val} = X.mColor B}⟩

/-- Section 3.4.3, Definition 3.4.18: the point and block readings are
isomorphic to the two neighborhood types of the local constituent.
The displayed maps fix the underlying singleton or block. -/
theorem upccCaseLocalMath_spec (B : ↥X.blocks) (hbig : ∃ k, X.IsBigColor₂ B k) :
    ∃ P : PartitionStructure ↥X.vtxSet, P.IsCoherent ∧ P.natColor = X.vc ∧
      ∃ m l : Fin P.rank,
        (m : ℕ) = X.mColor B ∧ (l : ℕ) = X.lColor B ∧ m ≠ l ∧
        ∃ f : ↥(X.linkClass B (X.mColor B)) ≃ ↥(P.nbr m (X.vtxOfBlk B)),
        ∃ g : ↥(X.blkClass B (X.lColor B)) ≃ ↥(P.nbr l (X.vtxOfBlk B)),
          (∀ x, (f x).val = X.vtxOfPt ⟨x.val,x.2.1⟩) ∧
          (∀ C, (g C).val = X.vtxOfBlk ⟨C.val,C.2.1⟩) ∧
          (∀ x C, (g C,f x) ∈ (P.localConstituentBip m l m (X.vtxOfBlk B)).E ↔
            (x,C) ∈ (upccCaseLocalMath X B).E) := by
  classical
  let D := X.upccCase'.toIsBipartiteCase.data
  have hm := X.isBigColor₂_mColor hbig
  have hp : 0 < (X.linkClass B (X.mColor B)).ncard := by
    change X.Pt₁.ncard < 2 * (X.linkClass B (X.mColor B)).ncard at hm
    omega
  obtain ⟨x₀,hx₀⟩ := (Set.ncard_pos (Set.toFinite _)).1 hp
  obtain ⟨C₀,hC₀,hne,hcol⟩ := (X.isSmallColor₂_lColor B.2).1
  let u₀ := X.vtxOfPt ⟨x₀,hx₀.1⟩
  let v₀ := X.vtxOfBlk ⟨C₀,hC₀⟩
  let m := D.P.color (X.vtxOfBlk B) u₀
  let l := D.P.color (X.vtxOfBlk B) v₀
  have hmval : (m : ℕ) = X.mColor B := (D.color_val _ _).symm.trans hx₀.2
  have hlval : (l : ℕ) = X.lColor B := (D.color_val _ _).symm.trans hcol
  have hmc (v : ↥X.vtxSet) :
      D.P.color (X.vtxOfBlk B) v = m ↔ X.c B v = X.mColor B := by
    change D.P.color (X.vtxOfBlk B) v = m ↔ X.vc (X.vtxOfBlk B) v = X.mColor B
    rw [D.color_val,← hmval]
    exact ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩
  have hlc (v : ↥X.vtxSet) :
      D.P.color (X.vtxOfBlk B) v = l ↔ X.c B v = X.lColor B := by
    change D.P.color (X.vtxOfBlk B) v = l ↔ X.vc (X.vtxOfBlk B) v = X.lColor B
    rw [D.color_val,← hlval]
    exact ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩
  have hml : m ≠ l := by
    intro h
    have hc : X.vc (X.vtxOfBlk B) v₀ = X.vc (X.vtxOfBlk B) u₀ :=
      (D.color_val _ _).trans ((congrArg Fin.val h.symm).trans (D.color_val _ _).symm)
    have hv : v₀.val ∈ X.sglSet :=
      (D.head_mem_part₁_iff hc).2 ⟨x₀,hx₀.1,rfl⟩
    exact D.notMem_part₂_of_mem_part₁ hv hC₀
  let f₀ : ↥(X.linkClass B (X.mColor B)) → ↥(D.P.nbr m (X.vtxOfBlk B)) :=
    fun x => ⟨X.vtxOfPt ⟨x.val,x.2.1⟩,(hmc _).2 x.2.2⟩
  let g₀ : ↥(X.blkClass B (X.lColor B)) → ↥(D.P.nbr l (X.vtxOfBlk B)) :=
    fun C => ⟨X.vtxOfBlk ⟨C.val,C.2.1⟩,(hlc _).2 C.2.2⟩
  have hf : Function.Bijective f₀ := by
    constructor
    · intro x y h
      have hv := congrArg (fun v => v.val.val) h
      exact Subtype.ext (Set.singleton_injective hv)
    · intro v
      have hc := (hmc v.val).1 v.2
      have hv : v.val.val ∈ X.sglSet :=
        (D.head_mem_part₁_iff (show X.vc (X.vtxOfBlk B) v.val =
          X.vc (X.vtxOfBlk B) u₀ from hc.trans hx₀.2.symm)).2 ⟨x₀,hx₀.1,rfl⟩
      obtain ⟨x,hx,he⟩ := hv
      have hcx : X.c B {x} = X.mColor B := by rw [← he]; exact hc
      refine ⟨⟨x,hx,hcx⟩,?_⟩
      exact Subtype.ext (Subtype.ext he.symm)
  have hg : Function.Bijective g₀ := by
    constructor
    · intro C E h
      have hv := congrArg (fun v => v.val.val) h
      exact Subtype.ext hv
    · intro v
      have hc := (hlc v.val).1 v.2
      have hv : v.val.val ∈ X.blocks :=
        (D.head_mem_part₂_iff (show X.vc (X.vtxOfBlk B) v.val =
          X.vc (X.vtxOfBlk B) v₀ from hc.trans hcol.symm)).2 hC₀
      exact ⟨⟨v.val.val,hv,hc⟩,Subtype.ext (Subtype.ext rfl)⟩
  refine ⟨D.P,D.isCoherent,D.natColor_eq,m,l,hmval,hlval,hml,Equiv.ofBijective f₀ hf,
    Equiv.ofBijective g₀ hg,fun _ => rfl,fun _ => rfl,?_⟩
  intro x C
  change D.P.color (X.vtxOfBlk ⟨C.val,C.2.1⟩) (X.vtxOfPt ⟨x.val,x.2.1⟩) = m ↔
    X.c C.val {x.val} = X.mColor B
  have hc := D.color_val (X.vtxOfBlk ⟨C.val,C.2.1⟩) (X.vtxOfPt ⟨x.val,x.2.1⟩)
  change X.c C.val {x.val} = _ at hc
  constructor
  · intro h
    exact hc.trans ((congrArg Fin.val h).trans hmval)
  · intro h
    exact Fin.ext (hc.symm.trans (h.trans hmval.symm))

variable {n : ℕ} (e : ↥X.vtxSet ≃ Fin n) {r : RawUpccCase}
    (hw : r.WF) (hn : UpccCaseNames X e r)
include hw hn

/-- Section 9.8: the smaller raw graph lists exactly the two local cells. -/
theorem upccCaseLocal_parts (B : ↥X.blocks) :
    (upccCaseLocal (r,upccCaseName₂ X e B)).1.Nodup ∧
    (upccCaseLocal (r,upccCaseName₂ X e B)).2.1.Nodup ∧
    (upccCaseLocal (r,upccCaseName₂ X e B)).1 ⊆ r.2.1 ∧
    (upccCaseLocal (r,upccCaseName₂ X e B)).2.1 ⊆ r.2.2 ∧
    (∀ x : ↥X.Pt₁, upccCaseName₁ X e x ∈ (upccCaseLocal (r,upccCaseName₂ X e B)).1 ↔
      x.val ∈ X.linkClass B (X.mColor B)) ∧
    (∀ C : ↥X.blocks, upccCaseName₂ X e C ∈ (upccCaseLocal (r,upccCaseName₂ X e B)).2.1 ↔
      C.val ∈ X.blkClass B (X.lColor B)) := by
  refine ⟨hw.left_nodup.filter _,hw.right_nodup.filter _,
    fun _ ha => List.mem_of_mem_filter ha,fun _ ha => List.mem_of_mem_filter ha,?_,?_⟩
  · intro x
    change upccCaseName₁ X e x ∈ upccCaseLink ((r,upccCaseName₂ X e B),
      upccCaseM (r,upccCaseName₂ X e B)) ↔ _
    rw [upccCaseM_spec X e hw hn,upccCaseLink_mem X e hn]
    exact ⟨fun h => ⟨x.2,h⟩,And.right⟩
  · intro C
    change upccCaseName₂ X e C ∈ upccCaseBlock ((r,upccCaseName₂ X e B),
      upccCaseL (r,upccCaseName₂ X e B)) ↔ _
    rw [upccCaseL_spec X e hw hn,upccCaseBlock_mem X e hn]
    exact ⟨fun h => ⟨C.2,h⟩,And.right⟩

open scoped Classical in
/-- Section 9.8: the full matrix of the smaller raw graph is the matrix of
the local constituent, through the named point and block maps. -/
theorem upccCaseLocal_matrix (B : ↥X.blocks) :
    let g := upccCaseLocal (r,upccCaseName₂ X e B)
    g.2.2 = g.1.map (fun a => g.2.1.map (fun b =>
      if ∃ x : ↥(X.linkClass B (X.mColor B)), ∃ C : ↥(X.blkClass B (X.lColor B)),
        upccCaseName₁ X e ⟨x.val,x.2.1⟩ = a ∧ upccCaseName₂ X e ⟨C.val,C.2.1⟩ = b ∧
          (x,C) ∈ (upccCaseLocalMath X B).E then 1 else 0)) := by
  classical
  dsimp only
  change (upccCaseLink _).map _ = (upccCaseLink _).map _
  apply List.map_congr_left
  intro a ha
  obtain ⟨x,rfl⟩ := upccCaseName₁_surj hn (List.mem_of_mem_filter ha)
  have hx : x.val ∈ X.linkClass B (X.mColor B) :=
    ((upccCaseLocal_parts X e hw hn B).2.2.2.2.1 x).1 ha
  rw [upccCaseRow_spec X e hw hn]
  apply List.map_congr_left
  intro b hb
  obtain ⟨C,rfl⟩ := upccCaseName₂_surj hn (List.mem_of_mem_filter hb)
  have hC : C.val ∈ X.blkClass B (X.lColor B) :=
    ((upccCaseLocal_parts X e hw hn B).2.2.2.2.2 C).1 hb
  have hleft : (∃ D : ↥X.blocks, upccCaseName₂ X e D = upccCaseName₂ X e C ∧
      (x.val,D.val) ∈ (X.upccBip B).E) ↔ X.c C.val {x.val} = X.mColor B := by
    constructor
    · rintro ⟨D,hD,hE⟩
      have : D = C := upccCaseName₂_injective X e hD
      subst D
      exact hE.2.2.2
    · intro h; exact ⟨C,rfl,hx.1,hx.2,hC,h⟩
  have hright : (∃ y : ↥(X.linkClass B (X.mColor B)), ∃ D : ↥(X.blkClass B (X.lColor B)),
      upccCaseName₁ X e ⟨y.val,y.2.1⟩ = upccCaseName₁ X e x ∧
      upccCaseName₂ X e ⟨D.val,D.2.1⟩ = upccCaseName₂ X e C ∧
      (y,D) ∈ (upccCaseLocalMath X B).E) ↔ X.c C.val {x.val} = X.mColor B := by
    constructor
    · rintro ⟨y,D,hy,hD,hE⟩
      have hy' := congrArg Subtype.val (upccCaseName₁_injective X e hy)
      have hD' := congrArg Subtype.val (upccCaseName₂_injective X e hD)
      change X.c D.val {y.val} = X.mColor B at hE
      rwa [hy',hD'] at hE
    · intro h; exact ⟨⟨x.val,hx⟩,⟨C.val,hC⟩,rfl,rfl,h⟩
  simp only [hleft,hright]

end Local
end Algo
