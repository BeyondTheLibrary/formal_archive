import Workspace.Algo.SplitDesignGraph
import Workspace.SplitOrJohnson.ColorSplit

/-! # The two parts used in Section 9.7

The scan follows `colorSplit`: take the least color with at least a quarter
of the vertices, if there is one. Otherwise take all colors through the
least threshold that reaches a quarter. Only colors in the input are scanned.
-/
namespace Algo
open Babai RAM

def rawColorClass (z : RawLab × ℕ) : List ℕ :=
  (List.range z.1.length).filter (fun i => decide (labAt z.1 i = z.2))

def rawColorBelow (z : RawLab × ℕ) : List ℕ :=
  (List.range z.1.length).filter (fun i => decide (labAt z.1 i ≤ z.2))

def rawQuarterClass (z : RawLab × ℕ) : Bool := decide (z.1.length ≤ 4 * (rawColorClass z).length)
def rawQuarterBelow (z : RawLab × ℕ) : Bool := decide (z.1.length ≤ 4 * (rawColorBelow z).length)

def rawQuarterColors (l : RawLab) : List ℕ := l.filter (fun k => rawQuarterClass (l,k))
def rawQuarterCuts (l : RawLab) : List ℕ := l.filter (fun k => rawQuarterBelow (l,k))

def rawColorSplit (l : RawLab) : List ℕ :=
  if (rawQuarterColors l).isEmpty then rawColorBelow (l,upccCaseLeast (rawQuarterCuts l))
  else rawColorClass (l,upccCaseLeast (rawQuarterColors l))

theorem polyFun_rawColorClass : PolyFun rawColorClass := by
  have hp : PolyFun (fun z : (RawLab × ℕ) × ℕ => decide (labAt z.1.1 z.2 = z.1.2)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_labAt).natEq
      (polyFun_fst.comp polyFun_snd)
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp (PolyFun.filterParam hp)

theorem polyFun_rawColorBelow : PolyFun rawColorBelow := by
  have hp : PolyFun (fun z : (RawLab × ℕ) × ℕ => decide (labAt z.1.1 z.2 ≤ z.1.2)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_labAt).le
      (polyFun_fst.comp polyFun_snd)
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp (PolyFun.filterParam hp)

theorem polyFun_rawQuarterClass : PolyFun rawQuarterClass :=
  (polyFun_fst.comp polyFun_length).le ((polyFun_const 4).mul (polyFun_rawColorClass.comp polyFun_length))
theorem polyFun_rawQuarterBelow : PolyFun rawQuarterBelow :=
  (polyFun_fst.comp polyFun_length).le ((polyFun_const 4).mul (polyFun_rawColorBelow.comp polyFun_length))
theorem polyFun_rawQuarterColors : PolyFun rawQuarterColors :=
  (polyFun_id.pair polyFun_id).comp (PolyFun.filterParam polyFun_rawQuarterClass)
theorem polyFun_rawQuarterCuts : PolyFun rawQuarterCuts :=
  (polyFun_id.pair polyFun_id).comp (PolyFun.filterParam polyFun_rawQuarterBelow)
theorem polyFun_rawColorSplit : PolyFun rawColorSplit :=
  PolyFun.ite (polyFun_rawQuarterColors.comp polyFun_isEmpty)
    ((polyFun_id.pair (polyFun_rawQuarterCuts.comp upccCasePoly_least)).comp polyFun_rawColorBelow)
    ((polyFun_id.pair (polyFun_rawQuarterColors.comp upccCasePoly_least)).comp polyFun_rawColorClass)

theorem rawColorClass_mem (l : RawLab) (k i : ℕ) :
    i ∈ rawColorClass (l,k) ↔ i < l.length ∧ labAt l i = k := by
  simp [rawColorClass]
theorem rawColorBelow_mem (l : RawLab) (k i : ℕ) :
    i ∈ rawColorBelow (l,k) ↔ i < l.length ∧ labAt l i ≤ k := by
  simp [rawColorBelow]

private theorem colorScan_count (l : RawLab) (p : ℕ → Bool) :
    ((List.range l.length).filter p).length = {i : Fin l.length | p i = true}.ncard := by
  exact splitNamedCount (fun i : Fin l.length => i.val) Fin.val_injective
    (List.range l.length) List.nodup_range
    (fun a => by simp only [List.mem_range]; exact ⟨fun h => ⟨⟨a,h⟩,rfl⟩,fun ⟨i,hi⟩ => hi ▸ i.isLt⟩) p

theorem rawColorClass_length (l : RawLab) (k : ℕ) :
    (rawColorClass (l,k)).length = (colorClassOf (fun i : Fin l.length => labAt l i) k).ncard := by
  rw [rawColorClass,colorScan_count]
  congr 1
  ext i
  simp [colorClassOf]

theorem rawColorBelow_length (l : RawLab) (k : ℕ) :
    (rawColorBelow (l,k)).length = (colorBelow (fun i : Fin l.length => labAt l i) k).ncard := by
  rw [rawColorBelow,colorScan_count]
  congr 1
  ext i
  simp [colorBelow]

theorem rawQuarterColors_mem {l : RawLab} (hn : 0 < l.length) (k : ℕ) :
    k ∈ rawQuarterColors l ↔ l.length ≤ 4 * (colorClassOf (fun i : Fin l.length => labAt l i) k).ncard := by
  simp only [rawQuarterColors,List.mem_filter,rawQuarterClass,decide_eq_true_eq,rawColorClass_length]
  apply and_iff_right_of_imp
  intro hk
  have hc : 0 < (colorClassOf (fun i : Fin l.length => labAt l i) k).ncard := by omega
  obtain ⟨i,hi⟩ := (Set.ncard_pos).1 hc
  change labAt l i = k at hi
  rw [← hi,labAt,List.getD_eq_getElem _ _ i.isLt]
  exact List.getElem_mem i.isLt

private theorem leastCut_present {l : RawLab} (hn : 0 < l.length) :
    Nat.find (exists_colorBelow (fun i : Fin l.length => labAt l i)) ∈ l := by
  classical
  let col := fun i : Fin l.length => labAt l i
  let k := Nat.find (exists_colorBelow col)
  have hk : l.length ≤ 4 * (colorBelow col k).ncard := by
    have hh := Nat.find_spec (exists_colorBelow col)
    change Fintype.card (Fin l.length) ≤ 4 * (colorBelow col k).ncard at hh
    rwa [Fintype.card_fin] at hh
  change k ∈ l
  by_contra hnot
  have hno : ∀ i : Fin l.length, col i ≠ k := by
    intro i he
    apply hnot
    rw [← he]
    change labAt l i ∈ l
    rw [labAt,List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem i.isLt
  rcases Nat.eq_zero_or_pos k with h0 | hp
  · have he : colorBelow col k = ∅ := by
      ext i
      simp only [colorBelow,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      intro hh
      exact hno i (by omega)
    rw [he,Set.ncard_empty] at hk
    omega
  · have he : colorBelow col k = colorBelow col (k-1) := by
      ext i
      simp only [colorBelow,Set.mem_setOf_eq]
      have := hno i
      omega
    have hmin := Nat.find_min (exists_colorBelow col) (show k-1<k by omega)
    rw [he] at hk
    exact hmin (by simpa only [Fintype.card_fin] using hk)

open scoped Classical in
theorem rawQuarterCuts_least {l : RawLab} (hn : 0 < l.length) :
    upccCaseLeast (rawQuarterCuts l) = Nat.find (exists_colorBelow (fun i : Fin l.length => labAt l i)) := by
  let col := fun i : Fin l.length => labAt l i
  let k := Nat.find (exists_colorBelow col)
  have hk : k ∈ rawQuarterCuts l := by
    simp only [rawQuarterCuts,List.mem_filter,rawQuarterBelow,decide_eq_true_eq,rawColorBelow_length]
    refine ⟨leastCut_present hn,?_⟩
    have hh := Nat.find_spec (exists_colorBelow col)
    change Fintype.card (Fin l.length) ≤ 4 * (colorBelow col k).ncard at hh
    rwa [Fintype.card_fin] at hh
  obtain ⟨hm,hmin⟩ := upccCaseLeast_spec _ (List.ne_nil_of_mem hk)
  apply le_antisymm (hmin k hk)
  apply Nat.find_min' (exists_colorBelow col)
  have hh := (List.mem_filter.1 hm).2
  simpa only [rawQuarterBelow,decide_eq_true_eq,rawColorBelow_length,Fintype.card_fin] using hh

open scoped Classical in
theorem rawColorSplit_spec {l : RawLab} (hn : 0 < l.length) (i : Fin l.length) :
    i.val ∈ rawColorSplit l ↔ i ∈ colorSplit (fun j : Fin l.length => labAt l j) := by
  classical
  let col := fun j : Fin l.length => labAt l j
  change i.val ∈ rawColorSplit l ↔ i ∈ colorSplit col
  have he : (rawQuarterColors l).isEmpty = true ↔ ¬ ∃ k, l.length ≤ 4 * (colorClassOf col k).ncard := by
    simp only [List.isEmpty_iff,List.eq_nil_iff_forall_not_mem,not_exists]
    exact forall_congr' (fun k => not_congr (rawQuarterColors_mem hn k))
  have hm := upccCaseLeast_find _ _ (rawQuarterColors_mem hn)
  by_cases h : ∃ k, l.length ≤ 4 * (colorClassOf col k).ncard
  · have hb : (rawQuarterColors l).isEmpty = false := Bool.eq_false_iff.2 (fun hh => (he.1 hh) h)
    simp only [rawColorSplit,hb,Bool.false_eq_true,if_false,rawColorClass_mem,i.isLt,true_and]
    rw [hm,dif_pos h]
    have h' : ∃ k, Fintype.card (Fin l.length) ≤ 4 * (colorClassOf col k).ncard := by simpa only [Fintype.card_fin] using h
    rw [colorSplit,dif_pos h']
    apply Iff.of_eq
    congr 1
    exact @Nat.find_congr' _ _ (fun _ => Classical.propDecidable _)
      (fun _ => inferInstance) h h' (by intro k; simp only [Fintype.card_fin])
  · have hb := he.2 h
    simp only [rawColorSplit,hb,if_true,rawColorBelow_mem,i.isLt,true_and,rawQuarterCuts_least hn]
    have h' : ¬ ∃ k, Fintype.card (Fin l.length) ≤ 4 * (colorClassOf col k).ncard := by simpa only [Fintype.card_fin] using h
    rw [colorSplit,dif_neg h']
    rfl

end Algo
