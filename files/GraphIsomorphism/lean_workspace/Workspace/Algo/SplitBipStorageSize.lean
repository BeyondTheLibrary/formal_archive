import Workspace.Algo.SplitBipTurnInput
import Workspace.Algo.DesignOut

/-! A fresh binary table is small in its vertex count, regardless of
the size of the coloring from which it was refined. This is the size
reset used between recursive turns. The table lists every ordered pair
once and its colors are ranks below the number of rows. -/
namespace Algo
open RAM Babai

def sbipBinaryRowBound (n : ℕ) : ℕ :=
  2 * (1 + 2 * (2 * (n+2) + 1)) + 2 * (n^2+2)

def sbipBinaryBound (n : ℕ) : ℕ :=
  2 * strBound n + 2 * (1 + n^2 * (2 * sbipBinaryRowBound n + 1))

theorem sbipBinary_size {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p) :
    Enc.size p ≤ sbipBinaryBound n := by
  have hdom := size_natList_le (length_le_of_nodup_lt h.domNodup
    (fun a ha => (h.domMem a).1 ha)) (fun a ha => (h.domMem a).1 ha)
  have hlen := length_table h
  have hrow : ∀ q ∈ p.2, Enc.size q ≤ sbipBinaryRowBound n := by
    intro q hq
    have hk := (h.keyMem q.1).1 (List.mem_map_of_mem hq)
    have hkey := size_natList_le hk.1.le hk.2
    have hc := h.colLt q hq
    rw [hlen] at hc
    have hcolor : Enc.size q.2 ≤ n^2+2 := by
      rw [Small.size_nat]
      have hs := size_le_self q.2
      omega
    exact (Combine.size_pair_le q.1 q.2).trans
      (by unfold sbipBinaryRowBound; omega)
  have htable := size_list_le_of_entries p.2 (sbipBinaryRowBound n) hrow
  rw [hlen] at htable
  exact (Combine.size_pair_le p.1 p.2).trans
    (by unfold sbipBinaryBound strBound; omega)

theorem polyBound_sbipBinaryRowBound : PolyBound sbipBinaryRowBound := by
  have hk := (polyBound_const 1).add ((polyBound_const 2).mul
    (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))
  have hn : PolyBound (fun n : ℕ => n^2) := by simpa only [pow_two] using polyBound_id.mul polyBound_id
  exact ((polyBound_const 2).mul hk).add
    ((polyBound_const 2).mul (hn.add (polyBound_const 2)))

theorem polyBound_sbipBinaryBound : PolyBound sbipBinaryBound := by
  have hs : PolyBound strBound := (polyBound_const 1).add
    (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
      (polyBound_const 1)))
  have hn : PolyBound (fun n : ℕ => n^2) := by simpa only [pow_two] using polyBound_id.mul polyBound_id
  exact ((polyBound_const 2).mul hs).add ((polyBound_const 2).mul
    ((polyBound_const 1).add (hn.mul (((polyBound_const 2).mul
      polyBound_sbipBinaryRowBound).add (polyBound_const 1)))))

def sbipCaseSizeBound (n : ℕ) : ℕ := 2 * sbipBinaryBound n + 8 * strBound n

theorem sbipCase_size {r : RawUpccCase} (h : r.WF) :
    Enc.size r ≤ sbipCaseSizeBound r.1.1.length := by
  have hleft : ∀ a ∈ r.2.1, a < r.1.1.length := by
    intro a ha
    exact (h.table.domMem a).1 ((h.cover a).1 (List.mem_append_left _ ha))
  have hright : ∀ a ∈ r.2.2, a < r.1.1.length := by
    intro a ha
    exact (h.table.domMem a).1 ((h.cover a).1 (List.mem_append_right _ ha))
  have hl := size_natList_le (length_le_of_nodup_lt h.left_nodup hleft) hleft
  have hr := size_natList_le (length_le_of_nodup_lt h.right_nodup hright) hright
  have hp := sbipBinary_size h.table
  have hparts := Combine.size_pair_le r.2.1 r.2.2
  have hall := Combine.size_pair_le r.1 r.2
  change Enc.size r.2 ≤ 2 * Enc.size r.2.1 + 2 * Enc.size r.2.2 at hparts
  change Enc.size r ≤ 2 * Enc.size r.1 + 2 * Enc.size r.2 at hall
  unfold sbipCaseSizeBound strBound
  omega

theorem polyBound_sbipCaseSizeBound : PolyBound sbipCaseSizeBound := by
  have hs : PolyBound strBound := (polyBound_const 1).add
    (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
      (polyBound_const 1)))
  exact ((polyBound_const 2).mul polyBound_sbipBinaryBound).add ((polyBound_const 8).mul hs)

theorem mono_sbipCaseSizeBound : Monotone sbipCaseSizeBound := by
  intro a b h
  unfold sbipCaseSizeBound sbipBinaryBound sbipBinaryRowBound strBound
  gcongr

def sbipDictionaryBound (n : ℕ) : ℕ := 1 + 2*n*(2*strBound n+1)

theorem sbipDictionary_size (n : ℕ) (d : List (List ℕ)) (hlen : d.length ≤ 2*n)
    (hnd : ∀ row ∈ d,row.Nodup) (hmem : ∀ row ∈ d,∀ a ∈ row,a<n) :
    Enc.size d ≤ sbipDictionaryBound n := by
  have hr : ∀ row ∈ d,Enc.size row ≤ strBound n := by
    intro row hrow
    exact size_natList_le (length_le_of_nodup_lt (hnd row hrow) (hmem row hrow)) (hmem row hrow)
  have hs := size_list_le_of_entries d (strBound n) hr
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) 1)

theorem polyBound_sbipDictionaryBound : PolyBound sbipDictionaryBound := by
  have hs : PolyBound strBound := (polyBound_const 1).add
    (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
      (polyBound_const 1)))
  exact (polyBound_const 1).add (((polyBound_const 2).mul polyBound_id).mul
      (((polyBound_const 2).mul hs).add (polyBound_const 1)))

theorem SbipVertexDictionary.rows_bounded {α : Type*} {V : Set (Set α)}
    {point : α → ℕ} {d : List (List ℕ)} {e : ↥V ≃ Fin d.length}
    (h : SbipVertexDictionary V point d e) {m : ℕ} (hm : ∀ x,point x < m) :
    (∀ row ∈ d,row.Nodup) ∧ (∀ row ∈ d,∀ a ∈ row,a < m) := by
  have hrow (row : List ℕ) (hr : row ∈ d) :
      ∃ A : ↥V,d[(e A).val] = row := by
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hr
    exact ⟨e.symm ⟨i,hi⟩,by simpa using he⟩
  constructor
  · intro row hr
    obtain ⟨A,rfl⟩ := hrow row hr
    exact h.row_nodup A
  · intro row hr a ha
    obtain ⟨A,rfl⟩ := hrow row hr
    obtain ⟨x,_,rfl⟩ := (h.row_mem A a).1 ha
    exact hm x

theorem sbipBinary_color_le {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p) (a b : ℕ) :
    binColor (p,(a,b)) ≤ n^2 := by
  apply tblGet_le
  intro q hq
  exact (h.colLt q hq).le.trans_eq (length_table h)

end Algo
