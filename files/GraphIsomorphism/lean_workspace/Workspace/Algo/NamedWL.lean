import Workspace.Algo.SplitRaw
import Workspace.Algo.WLPoly
import Workspace.Refinement.NamedWL

/-!
# Exact integer names for binary WL tables

The input table may use arbitrary natural names. Only its keys and vertex list
need to be well formed. One round produces names below the row count, so subsequent
rounds also satisfy `RawWL.WF`. The tags and ranks agree with `WL.namedIter`, not
only with its color classes.
-/

namespace Algo

open Babai

/-- A binary table lists every pair and vertex once. Initial names need no bound. -/
structure NamedBinaryWF (n : ℕ) (p : RawWL) : Prop where
  domNodup : p.1.Nodup
  domMem : ∀ a, a ∈ p.1 ↔ a < n
  keyNodup : (p.2.map Prod.fst).Nodup
  keyMem : ∀ t : List ℕ, t ∈ p.2.map Prod.fst ↔ (t.length = 2 ∧ ∀ a ∈ t, a < n)

/-- Every well-formed raw binary table satisfies the structural conditions. -/
theorem namedBinaryWF_of_wf {n : ℕ} {p : RawWL} (h : RawWL.WF n 2 p) : NamedBinaryWF n p :=
  ⟨h.domNodup, h.domMem, h.keyNodup, h.keyMem⟩

/-- The coloring read from a binary table. -/
def namedBin (n : ℕ) (p : RawWL) (u v : Fin n) : ℕ := binColor (p, (u.val, v.val))

variable {n : ℕ} {p : RawWL}

theorem namedBinary_row (h : NamedBinaryWF n p) (u v : Fin n) :
    ∃ q ∈ p.2, q.1 = [u.val, v.val] := by
  have hm : [u.val, v.val] ∈ p.2.map Prod.fst :=
    (h.keyMem _).2 ⟨rfl, by simp [u.isLt, v.isLt]⟩
  exact List.mem_map.1 hm

theorem namedBinary_row_cases (h : NamedBinaryWF n p) {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    ∃ u v : Fin n, q.1 = [u.val, v.val] := by
  have hk := (h.keyMem _).1 (List.mem_map_of_mem hq)
  obtain ⟨x, hx⟩ := exists_tupleOf hk.1 hk.2
  have he : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he, tupleOf_pair] at hx
  exact ⟨x 0, x 1, hx.symm⟩

/-- The first round bounds its output names even when the input names are large. -/
theorem namedBinary_step_wf (h : NamedBinaryWF n p) : RawWL.WF n 2 (rawWLStep p) where
  domNodup := h.domNodup
  domMem := h.domMem
  keyNodup := by rw [rawWLStep_keys]; exact h.keyNodup
  keyMem := by rw [rawWLStep_keys]; exact h.keyMem
  colLt := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [rawWLStep_length]
    exact wlNewCol_lt hq'

theorem namedBinary_iter_wf (h : NamedBinaryWF n p) :
    ∀ r, NamedBinaryWF n (rawWLStep^[r] p)
  | 0 => h
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    exact namedBinaryWF_of_wf (namedBinary_step_wf (namedBinary_iter_wf h r))

theorem namedBinary_length_table (h : NamedBinaryWF n p) : p.2.length = n ^ 2 := by
  simpa only [rawWLStep_length] using length_table (namedBinary_step_wf h)

/-- The list rank is the same finite-set rank used by the named refinement. -/
theorem namedRank_raw {D : List (List ℕ)} (hD : D.Nodup) (t : List ℕ) :
    rankIn (D, t) = WL.namedRank D.toFinset t := by
  classical
  rw [WL.namedRank_eq_rankIn]
  exact rankIn_congr_mem hD (Finset.nodup_toList _) (fun s => by simp) t

theorem namedBinary_innerVec (u v w : Fin n) :
    innerVec p.2 [u.val, v.val] w.val = WL.namedVec (namedBin n p) u v w := by
  simp [innerVec, substAt_eq_set, WL.namedVec, namedBin, binColor, List.range_succ]

theorem namedBinary_vecSet (h : NamedBinaryWF n p) :
    (vecSet p).toFinset = WL.namedVecs (namedBin n p) := by
  ext t
  rw [List.mem_toFinset, mem_vecSet]
  constructor
  · intro ht
    obtain ⟨q, hq, w, hw, rfl⟩ := exists_of_mem_allVecs ht
    obtain ⟨u, v, he⟩ := namedBinary_row_cases h hq
    rw [he]
    have hh := WL.namedVec_mem (namedBin n p) u v ⟨w, (h.domMem w).1 hw⟩
    rwa [← namedBinary_innerVec] at hh
  · intro ht
    obtain ⟨⟨u, v, w⟩, _, he⟩ := Finset.mem_image.1 ht
    obtain ⟨q, hq, hqv⟩ := namedBinary_row h u v
    rw [← he, ← namedBinary_innerVec, ← hqv]
    exact mem_allVecs hq ((h.domMem _).2 w.isLt)

theorem namedBinary_count (h : NamedBinaryWF n p) (u v : Fin n) (i : ℕ) :
    wlCount p [u.val, v.val] i = WL.namedCount (namedBin n p) u v i := by
  rw [wlCount, ← ncard_eq_length_filter p.1 h.domNodup (fun a ha => (h.domMem a).1 ha)]
  have hs : {z : Fin n | z.val ∈ p.1 ∧
      decide (rankIn (vecSet p, innerVec p.2 [u.val, v.val] z.val) = i) = true} =
      {z : Fin n | WL.namedRank (WL.namedVecs (namedBin n p))
        (WL.namedVec (namedBin n p) u v z) = i} := by
    ext z
    simp only [Set.mem_setOf_eq, (h.domMem _).2 z.isLt, true_and, decide_eq_true_eq,
      namedRank_raw (nodup_vecSet p), namedBinary_vecSet h, namedBinary_innerVec]
  rw [hs, ncard_setOf]
  unfold WL.namedCount
  congr 1
  ext z
  simp

/-- The raw and mathematical tags agree entry for entry. -/
theorem namedBinary_tag (h : NamedBinaryWF n p) (u v : Fin n) :
    wlTagAt p [u.val, v.val] = WL.namedTag (namedBin n p) u v := by
  have hl : (vecSet p).length = (WL.namedVecs (namedBin n p)).card := by
    rw [← namedBinary_vecSet h, List.toFinset_card_of_nodup (nodup_vecSet p)]
  unfold wlTagAt WL.namedTag
  rw [hl]
  congr 1
  exact List.map_congr_left fun i _ => namedBinary_count h u v i

theorem namedBinary_tagSet (h : NamedBinaryWF n p) :
    (wlTagSet p).toFinset = WL.namedTags (namedBin n p) := by
  ext t
  simp only [List.mem_toFinset, mem_wlTagSet, wlTags, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨u, v, he⟩ := namedBinary_row_cases h hq
    rw [he, namedBinary_tag h]
    exact WL.namedTag_mem _ u v
  · intro ht
    obtain ⟨⟨u, v⟩, _, he⟩ := Finset.mem_image.1 ht
    obtain ⟨q, hq, hqv⟩ := namedBinary_row h u v
    exact ⟨q, hq, by rw [hqv, namedBinary_tag h]; exact he⟩

/-- One raw binary round computes exactly the new integer name. -/
theorem namedBinary_step (h : NamedBinaryWF n p) (u v : Fin n) :
    namedBin n (rawWLStep p) u v = WL.namedStep (namedBin n p) u v := by
  obtain ⟨q, hq, he⟩ := namedBinary_row h u v
  rw [namedBin, binColor, ← he, tblGet_rawWLStep hq, wlNewCol, he,
    namedRank_raw (nodup_wlTagSet p), namedBinary_tagSet h, namedBinary_tag h]
  rfl

/-- Exact names, round by round, with no bound on the input color names. -/
theorem namedBinary_iter (h : NamedBinaryWF n p) (r : ℕ) (u v : Fin n) :
    namedBin n (rawWLStep^[r] p) u v = WL.namedIter (namedBin n p) r u v := by
  induction r generalizing u v with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', namedBinary_step (namedBinary_iter_wf h r)]
    have he : namedBin n (rawWLStep^[r] p) = WL.namedIter (namedBin n p) r :=
      funext fun a => funext fun b => ih a b
    rw [he]
    rfl

/-- The stable raw routine computes the exact named refinement at its own round count. -/
theorem namedBinary_stable (h : NamedBinaryWF n p) (u v : Fin n) :
    namedBin n (rawWLStable p) u v = WL.namedIter (namedBin n p) (n ^ 2 * n ^ 2) u v := by
  rw [rawWLStable_eq_iterate, namedBinary_length_table h]
  exact namedBinary_iter h _ u v

/-- Extra rounds after stability leave the raw routine's names unchanged. -/
theorem namedBinary_stable_rounds (h : NamedBinaryWF n p) {R : ℕ}
    (hR : n ^ 2 * n ^ 2 ≤ R) (u v : Fin n) :
    namedBin n (rawWLStable p) u v = WL.namedIter (namedBin n p) R u v := by
  rw [namedBinary_stable h]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le u.val) u.isLt
  have hr : 1 ≤ n ^ 2 * n ^ 2 := Nat.mul_pos (pow_pos hn _) (pow_pos hn _)
  have hs : WL.IsStable (WL.iter (namedBin n p) (n ^ 2 * n ^ 2)) :=
    WL.isStable_iter_of_card_le _ (by simp [pow_two])
  have he := WL.namedIter_freeze (namedBin n p) hr hs (R - n ^ 2 * n ^ 2)
  rw [Nat.add_sub_of_le hR] at he
  exact (congrFun (congrFun he u) v).symm

/-- After stable refinement all names obey the usual raw table bound. -/
theorem namedBinary_stable_wf (h : NamedBinaryWF n p) : RawWL.WF n 2 (rawWLStable p) := by
  rw [rawWLStable_eq_iterate]
  cases he : p.2.length * p.2.length with
  | zero =>
    have hl : p.2 = [] := List.length_eq_zero_iff.1 (by nlinarith)
    exact ⟨h.domNodup, h.domMem, h.keyNodup, h.keyMem, by simp [hl]⟩
  | succ r =>
    rw [Function.iterate_succ_apply']
    exact namedBinary_step_wf (namedBinary_iter_wf h r)

end Algo
