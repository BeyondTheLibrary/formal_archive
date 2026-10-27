/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  The process on a raw
input, vertex by vertex: what the RAM program computes, round by round.
-/
import Workspace.Algo.TagLinRows
import Workspace.Algo.TaggedCost

/-!
# The tagged process on a raw input

For a raw input `r` (colors, edges, tag) with `n` vertices, `sX r j v`, `rX r j v`, `NX r j`
and `PX r j` are the color of `v` after `j` rounds, its rank `st(c_j)(v)`, the number of colors
and the ordered palette `C` of round `j` (`Babai.TaggedDigraph.tagIter`).  This file proves
the facts the RAM program of `Workspace/Algo/TagLinMain.lean` relies on:

* round `0` is the input coloring (`sX_zero`), and round `j + 1` is the string
  `rowStr` built from the ranks and the edge list (`sX_succ`): the counts `d⁺ᵢ`, `d⁻ᵢ` of
  §4.1 are the numbers of edges in the list (`outCnt_eq`, `inCnt_eq`);
* a strictly increasing list of representatives is the ordered palette (`PX_of_sorted`);
* the number of colors never decreases (`NX_mono`) and is at most `n` (`NX_le`);
* the stopping round (`stopIdx_eq_of`) and the output `X*` (`taggedOut_eq`).

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open Babai Babai.TaggedDigraph

/-- The color of vertex `v` after `j` rounds. -/
noncomputable def sX (r : RawTagged) (j v : ℕ) : List ℕ :=
  if h : v < r.1.length then (tagIter (decTagged r) j).c ⟨v, h⟩ else []

/-- The rank `st(c_j)(v)` of vertex `v` in round `j`. -/
noncomputable def rX (r : RawTagged) (j v : ℕ) : ℕ :=
  if h : v < r.1.length then (tagIter (decTagged r) j).rank ⟨v, h⟩ else 0

/-- The number of colors of round `j`. -/
noncomputable def NX (r : RawTagged) (j : ℕ) : ℕ := (tagIter (decTagged r) j).numColors

/-- The ordered palette of round `j`. -/
noncomputable def PX (r : RawTagged) (j : ℕ) : List (List ℕ) := (tagIter (decTagged r) j).oldColors

theorem sX_zero (r : RawTagged) {v : ℕ} (hv : v < r.1.length) : sX r 0 v = r.1[v] := by
  simp [sX, hv, decTagged]

theorem rX_lt (r : RawTagged) (j : ℕ) {v : ℕ} (hv : v < r.1.length) : rX r j v < NX r j := by
  simp only [rX, hv, dif_pos, NX]; exact rank_lt _ _

theorem rX_eq (r : RawTagged) (j : ℕ) {v : ℕ} (hv : v < r.1.length) :
    rX r j v = (PX r j).idxOf (sX r j v) := by
  simp [rX, sX, hv, PX, rank]

theorem E_decTagged (r : RawTagged) (j : ℕ) :
    (tagIter (decTagged r) j).E = {p | ((p.1 : ℕ), (p.2 : ℕ)) ∈ r.2.1} := by
  rw [E_tagIter]; rfl

/-- The count of edges in a nodup list with prescribed first end, by second end. -/
theorem ncard_eq_countP {n : ℕ} (es : List (ℕ × ℕ)) (hnd : es.Nodup)
    (hlt : ∀ e ∈ es, e.1 < n ∧ e.2 < n) (Q : ℕ → Prop) [DecidablePred Q] (x : ℕ) :
    {y : Fin n | (x, (y : ℕ)) ∈ es ∧ Q y}.ncard = es.countP (fun e => e.1 = x ∧ Q e.2) := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  rw [← Set.ncard_coe_finset]
  let φ : Fin n → ℕ × ℕ := fun y => (x, (y : ℕ))
  have hφ : Function.Injective φ := fun a b h => Fin.ext (by simpa [φ] using h)
  rw [← Set.ncard_image_of_injective _ hφ]
  congr 1
  ext e
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq, φ]
  constructor
  · rintro ⟨y, ⟨hy, hq⟩, rfl⟩; exact ⟨hy, rfl, hq⟩
  · rintro ⟨he, hx, hq⟩
    refine ⟨⟨e.2, (hlt e he).2⟩, ⟨?_, hq⟩, ?_⟩
    · rw [← hx]; exact he
    · rw [← hx]

theorem ncard_eq_countP' {n : ℕ} (es : List (ℕ × ℕ)) (hnd : es.Nodup)
    (hlt : ∀ e ∈ es, e.1 < n ∧ e.2 < n) (Q : ℕ → Prop) [DecidablePred Q] (x : ℕ) :
    {y : Fin n | ((y : ℕ), x) ∈ es ∧ Q y}.ncard = es.countP (fun e => e.2 = x ∧ Q e.1) := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  rw [← Set.ncard_coe_finset]
  let φ : Fin n → ℕ × ℕ := fun y => ((y : ℕ), x)
  have hφ : Function.Injective φ := fun a b h => Fin.ext (by simpa [φ] using h)
  rw [← Set.ncard_image_of_injective _ hφ]
  congr 1
  ext e
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq, φ]
  constructor
  · rintro ⟨y, ⟨hy, hq⟩, rfl⟩; exact ⟨hy, rfl, hq⟩
  · rintro ⟨he, hx, hq⟩
    refine ⟨⟨e.1, (hlt e he).1⟩, ⟨?_, hq⟩, ?_⟩
    · rw [← hx]; exact he
    · rw [← hx]

theorem edges_lt {r : RawTagged} (hr : r.WF) : ∀ e ∈ r.2.1, e.1 < r.1.length ∧ e.2 < r.1.length :=
  fun e he => ⟨(hr.2 e he).1, (hr.2 e he).2.1⟩

/-- `d⁺ᵢ(x)` is the number of listed edges `(x, y)` with `st(c)(y) = i`. -/
theorem outCnt_eq {r : RawTagged} (hr : r.WF) (j i : ℕ) (x : Fin r.1.length) :
    (tagIter (decTagged r) j).outCnt i x = outC r.2.1 (rX r j) i x := by
  unfold outCnt outC
  rw [E_decTagged]
  have : {y | (x, y) ∈ {p : Fin r.1.length × Fin r.1.length | ((p.1 : ℕ), (p.2 : ℕ)) ∈ r.2.1} ∧
      (tagIter (decTagged r) j).rank y = i} =
      {y : Fin r.1.length | ((x : ℕ), (y : ℕ)) ∈ r.2.1 ∧ rX r j y = i} := by
    ext y; simp [rX, y.isLt]
  rw [this, ncard_eq_countP r.2.1 hr.1 (edges_lt hr) (fun y => rX r j y = i)]

/-- `d⁻ᵢ(x)` is the number of listed edges `(y, x)` with `st(c)(y) = i`. -/
theorem inCnt_eq {r : RawTagged} (hr : r.WF) (j i : ℕ) (x : Fin r.1.length) :
    (tagIter (decTagged r) j).inCnt i x = inC r.2.1 (rX r j) i x := by
  unfold inCnt inC
  rw [E_decTagged]
  have : {y | (y, x) ∈ {p : Fin r.1.length × Fin r.1.length | ((p.1 : ℕ), (p.2 : ℕ)) ∈ r.2.1} ∧
      (tagIter (decTagged r) j).rank y = i} =
      {y : Fin r.1.length | ((y : ℕ), (x : ℕ)) ∈ r.2.1 ∧ rX r j y = i} := by
    ext y; simp [rX, y.isLt]
  rw [this, ncard_eq_countP' r.2.1 hr.1 (edges_lt hr) (fun y => rX r j y = i)]

/-- Round `j + 1` is the string of the rank and the counts. -/
theorem sX_succ {r : RawTagged} (hr : r.WF) (j : ℕ) {v : ℕ} (hv : v < r.1.length) :
    sX r (j + 1) v = rowStr r.2.1 (rX r j) (NX r j) v := by
  simp only [sX, hv, dif_pos, tagIter_succ]
  change (tagIter (decTagged r) j).tagColor ⟨v, hv⟩ = _
  unfold tagColor rowStr
  have hr0 : (tagIter (decTagged r) j).rank ⟨v, hv⟩ = rX r j v := by simp [rX, hv]
  rw [hr0]
  congr 1
  refine List.flatMap_congr (fun i _ => ?_)
  rw [outCnt_eq hr, inCnt_eq hr]

/-- A strictly increasing list of representatives is the ordered palette. -/
theorem PX_of_sorted (r : RawTagged) (j : ℕ) (Dl : List ℕ)
    (hs : (Dl.map (sX r j)).Pairwise (· < ·)) (hlt : ∀ v ∈ Dl, v < r.1.length)
    (hcov : ∀ v < r.1.length, ∃ w ∈ Dl, sX r j w = sX r j v) : Dl.map (sX r j) = PX r j := by
  unfold PX oldColors
  refine eq_sort_of hs _ (fun a => ?_)
  simp only [List.mem_map, realizedColors, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hlt w hw⟩, by simp [sX, hlt w hw]⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw, he⟩ := hcov v v.isLt
    exact ⟨w, hw, by rw [he]; simp [sX]⟩

theorem NX_eq_length (r : RawTagged) (j : ℕ) : NX r j = (PX r j).length := rfl

theorem NX_le (r : RawTagged) (j : ℕ) : NX r j ≤ r.1.length := by
  have := numColors_le_card (tagIter (decTagged r) j)
  simpa [NX] using this

theorem NX_mono (r : RawTagged) (j : ℕ) : NX r j ≤ NX r (j + 1) := by
  unfold NX
  rw [numColors_eq_card_range, numColors_eq_card_range]
  exact card_range_le_of_kernelSet_subset _ _ (kernelSet_tagIter_succ_subset _ j)

theorem NX_pos (r : RawTagged) (j : ℕ) (hn : 0 < r.1.length) : 0 < NX r j := by
  have := rank_lt (tagIter (decTagged r) j) ⟨0, hn⟩
  unfold NX; omega

/-- The stopping round is the first round that does not change the number of colors. -/
theorem stopIdx_eq_of (r : RawTagged) {k : ℕ} (hk : NX r (k + 1) = NX r k)
    (hlt : ∀ i < k, NX r (i + 1) ≠ NX r i) : stopIdx (decTagged r) = k := by
  classical
  unfold stopIdx
  rw [Nat.find_eq_iff]
  exact ⟨hk, fun i hi => hlt i hi⟩

theorem tag_tagIter (r : RawTagged) (j : ℕ) :
    (tagIter (decTagged r) j).tag = r.2.2 ++ (List.range j).map (PX r) := by
  induction j with
  | zero => simp [decTagged]
  | succ j ih =>
    rw [tagIter_succ]
    change (tagIter (decTagged r) j).tag ++ [(tagIter (decTagged r) j).oldColors] = _
    rw [ih, List.range_succ, List.map_append, List.append_assoc]
    rfl

/-- **The output `X*`**, round by round. -/
theorem taggedOut_eq (r : RawTagged) :
    taggedOut r = ((List.range r.1.length).map (fun v => [rX r (stopIdx (decTagged r)) v]),
      (r.2.1, r.2.2 ++ (List.range (stopIdx (decTagged r) + 1)).map (PX r))) := by
  unfold taggedOut
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    simp only [List.length_ofFn] at h1
    simp [stableTagged, stStr, rX, h1]
  · change (stableTagged (decTagged r)).tag = _
    rw [← tag_tagIter]
    rfl

end TagLin

end Algo
