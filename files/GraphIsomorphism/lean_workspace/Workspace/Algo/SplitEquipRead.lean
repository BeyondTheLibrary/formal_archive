import Workspace.Algo.SplitColorSelect
import Workspace.Algo.AlignStruct

/-! Proposition 7.1.3 and Section 9.7 refine each vertex color by its block
size before selecting a union of color classes. All counts scan the domain. -/
namespace Algo
open Babai RAM

def rawEquipColor (z : RawColPart × ℕ) : ℕ :=
  Nat.pair (labAt z.1.1 z.2) (cellSize z)

def rawEquipColors (P : RawColPart) : RawLab :=
  (List.range P.1.length).map (fun i => rawEquipColor (P,i))

def rawEquipFirst (P : RawColPart) : List ℕ := rawColorSplit (rawEquipColors P)

def rawEquipHintAt (z : RawColPart × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 ∈ rawEquipFirst z.1) && decide (z.2.2 ∈ rawEquipFirst z.1) then
    if z.2.1 = z.2.2 then 0 else if cellOf z.1 z.2.1 = cellOf z.1 z.2.2 then 1 else 2
  else 0

theorem polyFun_rawEquipColor : PolyFun rawEquipColor :=
  polyFun_cpKey.comp polyFun_upccNatPair

theorem polyFun_rawEquipColors : PolyFun rawEquipColors :=
  (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp (PolyFun.mapParam polyFun_rawEquipColor)

theorem polyFun_rawEquipFirst : PolyFun rawEquipFirst := polyFun_rawEquipColors.comp polyFun_rawColorSplit

theorem polyFun_rawEquipHintAt : PolyFun rawEquipHintAt := by
  have hi : PolyFun (fun z : RawColPart × (ℕ × ℕ) => z.2.1) := polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun z : RawColPart × (ℕ × ℕ) => z.2.2) := polyFun_snd.comp polyFun_snd
  have hf : PolyFun (fun z : RawColPart × (ℕ × ℕ) => rawEquipFirst z.1) :=
    polyFun_fst.comp polyFun_rawEquipFirst
  have hm := polyFun_rawJAnd ((hi.pair hf).comp polyFun_natListMem)
    ((hj.pair hf).comp polyFun_natListMem)
  have hcell := polyFun_cellOfPair
  have hci := (polyFun_fst.pair hi).comp hcell
  have hcj := (polyFun_fst.pair hj).comp hcell
  have he := polyFun_rawJAnd ((hci.comp polyFun_fst).natEq (hcj.comp polyFun_fst))
    ((hci.comp polyFun_snd).natEq (hcj.comp polyFun_snd))
  refine (PolyFun.ite hm (PolyFun.ite (hi.natEq hj) (polyFun_const 0)
      (PolyFun.ite he (polyFun_const 1) (polyFun_const 2))) (polyFun_const 0)).of_eq ?_
  intro z
  simp only [rawEquipHintAt,decide_eq_true_eq,Bool.and_eq_true,cellOf,Prod.mk.injEq]

@[simp] theorem rawEquipColors_length (P : RawColPart) : (rawEquipColors P).length = P.1.length := by
  simp [rawEquipColors]

theorem cellSize_ncard_block (P : RawColPart) (i : Fin P.1.length) :
    cellSize (P,i) = ((decColPartition P.1.length P).block i).ncard := by
  have hc := splitNamedCount (fun j : Fin P.1.length => j.val) Fin.val_injective
    (List.range P.1.length) List.nodup_range
    (fun a => by simp only [List.mem_range]; exact
      ⟨fun ha => ⟨⟨a,ha⟩,rfl⟩,fun ⟨j,hj⟩ => hj ▸ j.isLt⟩)
    (fun j => decide (cellOf P j = cellOf P i))
  change cellSize (P,i) = _ at hc
  rw [hc]
  congr 1
  ext j
  simp only [Set.mem_setOf_eq,decide_eq_true_eq]
  rfl

theorem rawEquipColors_spec (P : RawColPart) (i : Fin P.1.length) :
    labAt (rawEquipColors P) i = Nat.pair ((decColPartition P.1.length P).color i)
      (((decColPartition P.1.length P).block i).ncard) := by
  simp only [rawEquipColors,labAt]
  rw [show ((List.range P.1.length).map (fun j => rawEquipColor (P,j))).getD i 0 =
      rawEquipColor (P,i) by simp [i.isLt]]
  rw [rawEquipColor,cellSize_ncard_block]
  rfl

open scoped Classical in
theorem rawColorSplit_named {V : Type} [Fintype V] {l : RawLab} (hn : 0 < l.length)
    (col : V → ℕ) (e : V ≃ Fin l.length) (hc : ∀ x, labAt l (e x) = col x) (x : V) :
    (e x).val ∈ rawColorSplit l ↔ x ∈ colorSplit col := by
  rw [rawColorSplit_spec hn]
  have he := colorSplit_image (col := col) (col' := fun j : Fin l.length => labAt l j) e hc
  rw [← he,mem_image_equiv]
  simp

open scoped Classical in
theorem rawEquipFirst_spec (P : RawColPart) (hn : 0 < P.1.length) (i : Fin P.1.length) :
    i.val ∈ rawEquipFirst P ↔ i ∈ colorSplit (fun j : Fin P.1.length =>
      Nat.pair ((decColPartition P.1.length P).color j)
        (((decColPartition P.1.length P).block j).ncard)) := by
  exact rawColorSplit_named (by simpa using hn) _
    (finCongr (rawEquipColors_length P).symm) (rawEquipColors_spec P) i

theorem rawEquipFirst_lt {P : RawColPart} {i : ℕ} (hi : i ∈ rawEquipFirst P) : i < P.1.length := by
  unfold rawEquipFirst rawColorSplit at hi
  split at hi
  · simpa using (rawColorBelow_mem _ _ _).1 hi |>.1
  · simpa using (rawColorClass_mem _ _ _).1 hi |>.1

theorem rawEquipFirst_nodup (P : RawColPart) : (rawEquipFirst P).Nodup := by
  unfold rawEquipFirst rawColorSplit
  split <;> exact List.nodup_range.filter _

open scoped Classical in
theorem rawEquipHintAt_spec (P : RawColPart) (i j : Fin P.1.length)
    (hi : i.val ∈ rawEquipFirst P) (hj : j.val ∈ rawEquipFirst P) :
    rawEquipHintAt (P,(i,j)) =
      if i = j then 0 else if (decColPartition P.1.length P).part i j then 1 else 2 := by
  simp only [rawEquipHintAt,hi,hj,decide_true,Bool.and_self,if_true]
  have he : i.val = j.val ↔ i = j := Fin.val_inj
  simp only [he]
  by_cases hij : i = j
  · simp only [if_pos hij]
  · by_cases hc : cellOf P i = cellOf P j
    · simp only [if_neg hij,if_pos hc,
        if_pos (show (decColPartition P.1.length P).part i j from hc)]
    · simp only [if_neg hij,if_neg hc,
        if_neg (show ¬ (decColPartition P.1.length P).part i j from hc)]

end Algo
