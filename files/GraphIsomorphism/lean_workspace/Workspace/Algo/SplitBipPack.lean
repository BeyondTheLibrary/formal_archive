import Workspace.Algo.SplitBipDictionary

/-! Recursive outputs retain their original point names. New block names
start at the ambient degree, so they are disjoint from all point names.
The witness list supplies this degree without iterating a binary integer.
The hint supplied to this routine uses compact positions in point-first
order. Packing restores it to the names of the new graph. -/
namespace Algo
open Babai RAM

/-- Ambient witness, first part, block member rows, matrix, and decorations.
Block colors use column positions and the hint uses point-first positions. -/
abbrev RawSbipPack := (List ℕ × List ℕ) ×
  (List (List ℕ) × (List (List ℕ) × RawSbipDecor))

def sbipPackBlocks (z : RawSbipPack) : List ℕ :=
  (List.range z.2.1.length).map (fun i => z.1.1.length + i)

def sbipPackVertices (z : RawSbipPack) : List ℕ := z.1.2 ++ sbipPackBlocks z

def sbipPack (z : RawSbipPack) : RawSbipStored :=
  (((z.1.2,sbipPackBlocks z,z.2.2.1),
    (z.2.2.2.1,z.1.1.map (fun _ => 0) ++ z.2.2.2.2.1,
      sbipRestore (z.2.2.2.2.2,sbipPackVertices z))),
    z.1.1.map (fun _ => []) ++ z.2.1)

theorem polyFun_sbipPackBlocks : PolyFun sbipPackBlocks :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_length).pair
    ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_add))

theorem polyFun_sbipPackVertices : PolyFun sbipPackVertices :=
  (((polyFun_fst.comp polyFun_snd).pair polyFun_sbipPackBlocks).comp polyFun_append)

theorem polyFun_sbipPack : PolyFun sbipPack := by
  have hw : PolyFun (fun z : RawSbipPack => z.1.1) := polyFun_fst.comp polyFun_fst
  have hl : PolyFun (fun z : RawSbipPack => z.1.2) := polyFun_fst.comp polyFun_snd
  have hd : PolyFun (fun z : RawSbipPack => z.2.1) := polyFun_snd.comp polyFun_fst
  have hm : PolyFun (fun z : RawSbipPack => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hc : PolyFun (fun z : RawSbipPack => z.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hp := hw.comp (PolyFun.map (polyFun_const (0 : ℕ)))
  have he := hw.comp (PolyFun.map (polyFun_const ([] : List ℕ)))
  exact ((hl.pair (polyFun_sbipPackBlocks.pair hm)).pair
    ((hc.comp polyFun_fst).pair
      (((hp.pair ((hc.comp polyFun_snd).comp polyFun_fst)).comp polyFun_append).pair
        ((((hc.comp polyFun_snd).comp polyFun_snd).pair polyFun_sbipPackVertices).comp
          polyFun_sbipRestore)))).pair ((he.pair hd).comp polyFun_append)

@[simp] theorem sbipPackBlocks_length (z : RawSbipPack) :
    (sbipPackBlocks z).length = z.2.1.length := by simp [sbipPackBlocks]

theorem sbipPackBlocks_get (z : RawSbipPack) (i : Fin z.2.1.length) :
    (sbipPackBlocks z)[i.val]'(by simpa using i.isLt) = z.1.1.length + i := by
  simp [sbipPackBlocks]

theorem sbipPackBlocks_mem (z : RawSbipPack) (a : ℕ) :
    a ∈ sbipPackBlocks z ↔ z.1.1.length ≤ a ∧ a < z.1.1.length + z.2.1.length := by
  simp only [sbipPackBlocks,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hl,hu⟩
    exact ⟨a-z.1.1.length,by omega,by omega⟩

theorem sbipPackBlocks_nodup (z : RawSbipPack) : (sbipPackBlocks z).Nodup :=
  List.nodup_range.map (fun _ _ h => Nat.add_left_cancel h)

theorem sbipPackVertices_nodup (z : RawSbipPack) (hnd : z.1.2.Nodup)
    (hb : ∀ a ∈ z.1.2, a < z.1.1.length) : (sbipPackVertices z).Nodup := by
  rw [sbipPackVertices,List.nodup_append]
  refine ⟨hnd,sbipPackBlocks_nodup z,?_⟩
  intro a ha b hb' hab
  subst b
  have h := (sbipPackBlocks_mem z a).1 hb'
  have := hb a ha
  omega

@[simp] theorem sbipPack_points (z : RawSbipPack) : (sbipPack z).1.1.1 = z.1.2 := rfl

@[simp] theorem sbipPack_blocks (z : RawSbipPack) :
    (sbipPack z).1.1.2.1 = sbipPackBlocks z := rfl

@[simp] theorem sbipPack_matrix (z : RawSbipPack) : (sbipPack z).1.1.2.2 = z.2.2.1 := rfl

@[simp] theorem sbipPack_pointColors (z : RawSbipPack) : (sbipPack z).1.2.1 = z.2.2.2.1 := rfl

theorem sbipPack_blockColor (z : RawSbipPack) (i : ℕ) :
    labAt (sbipPack z).1.2.2.1 (z.1.1.length + i) = labAt z.2.2.2.2.1 i := by
  change (z.1.1.map (fun _ => 0) ++ z.2.2.2.2.1).getD (z.1.1.length+i) 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left,labAt]

theorem sbipPack_dict (z : RawSbipPack) (i : ℕ) :
    sbipDictGet ((sbipPack z).2,z.1.1.length+i) = sbipDictGet (z.2.1,i) := by
  change (z.1.1.map (fun _ => []) ++ z.2.1).getD (z.1.1.length+i) [] = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left,sbipDictGet]

theorem sbipPack_hint (z : RawSbipPack) (hnd : (sbipPackVertices z).Nodup)
    (i j : Fin (sbipPackVertices z).length) :
    binColor ((sbipPack z).1.2.2.2,
      ((sbipPackVertices z)[i.val],(sbipPackVertices z)[j.val])) =
        binColor (z.2.2.2.2.2,(i,j)) := sbipRestore_get _ _ hnd i j

@[simp] theorem sbipPack_dict_length (z : RawSbipPack) :
    (sbipPack z).2.length = z.1.1.length + z.2.1.length := by
  simp [sbipPack]

end Algo
