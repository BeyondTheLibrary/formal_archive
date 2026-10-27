/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: canonicity of the refinement routines (§4, Eq. (22)).
-/
import Workspace.Algo.WLRaw
import Workspace.Algo.Perm

/-!
# §4, Eq. (22) — the computed colorings are canonical

§4 (line 2820) asks of a refinement that it be **canonical**: *"`f ∈ Iso(X, Y)` implies
`f ∈ Iso(X*, Y*)`"*, and the naming of the colors must be canonical too, or the colorings of
two isomorphic inputs cannot be compared at all.  The routines of
`Workspace/Algo/RefineRaw.lean` (naive vertex-refinement, §4.1.1) and
`Workspace/Algo/WLRaw.lean` (`k`-ary WL refinement, §5.4.1) name their colors by the **rank**
of a tag among the tags that occur, so the statement to prove is the strong one: an
isomorphism of the inputs carries the computed coloring of one to the computed coloring of the
other **with the same color names**, not merely with the same partition.

That is what this file proves.  An isomorphism of raw inputs is a relabeling along a raw
permutation `π` (`Algo.relabelCD`, `Algo.relabelWL`), and the theorems are

```
Algo.rawStableRefine_relabelCD : rawStableRefine (relabelCD (π, X)) = relabelCD (π, rawStableRefine X)
Algo.rawWLStable_relabelWL     : rawWLStable (relabelWL (π, p))     = relabelWL (π, rawWLStable p)
```

with the colorwise corollaries `Algo.color_rawStableRefine_relabelCD` and
`Algo.tblGet_rawWLStable_relabelWL`.

## Does the order of the table enter the names?

**No.**  This is the design fact the rest of the algorithmic layer needs.  Every ingredient of
a color name is order-independent:

* a color is `Algo.rankIn (D, t)`, the number of entries of `D` that are lexicographically
  smaller than `t`, and this depends only on the *set* `D` (`Algo.rankIn_congr_mem`);
* the counts inside a tag are tallied at the rank of the tuple they count
  (`Algo.wlCount`), not at its position in the deduplicated list;
* a table is read by `Algo.tblGet`, i.e. by `List.lookup`, which depends only on the
  assignment when the keys are duplicate-free.

So relabeling permutes the *rows* of the answer, and nothing else: the color a given tuple
gets is unchanged.  No sorting routine is needed anywhere, and none is used.

## Main definitions

* `Algo.invAt` — the inverse of a raw permutation, read at a point;
* `Algo.relabelCD` — the relabeling of a raw colored digraph;
* `Algo.permList`, `Algo.relabelWL` — the relabeling of a raw table of `k`-tuples.

## Main results

* `Algo.tagAt_relabelCD`, `Algo.wlTagAt_relabelWL` — the tags transport;
* `Algo.rawNewCol_relabelCD`, `Algo.wlNewCol_relabelWL` — one round is canonical;
* `Algo.rawStableRefine_relabelCD`, `Algo.rawWLStable_relabelWL` — the whole process is.

No axiom and no `sorry`.
-/

namespace Algo

open Babai

/-! ## A raw permutation as a bijection of `[0, n)` -/

/-- The inverse of a raw permutation, read at a point. -/
def invAt (π : RawPerm) (y : ℕ) : ℕ := (rawInv π).getD y 0

theorem rawApply_lt {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {x : ℕ} (hx : x < n) :
    rawApply (π, x) < n := by
  rw [rawApply_of_wf h hx]
  exact (decPerm n π ⟨x, hx⟩).isLt

theorem rawApply_inj {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {x y : ℕ} (hx : x < n)
    (hy : y < n) (hxy : rawApply (π, x) = rawApply (π, y)) : x = y := by
  rw [rawApply_of_wf h hx, rawApply_of_wf h hy] at hxy
  have : (decPerm n π) ⟨x, hx⟩ = (decPerm n π) ⟨y, hy⟩ := Fin.ext hxy
  have := (decPerm n π).injective this
  simpa using congrArg Fin.val this

/-- **The specification of `Algo.invAt`**: it is the inverse of the decoded permutation. -/
theorem invAt_eq {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {y : ℕ} (hy : y < n) :
    invAt π y = ((decPerm n π)⁻¹ ⟨y, hy⟩ : ℕ) := by
  have hlen : y < (encPerm n (decPerm n π)⁻¹).length := by
    rw [length_encPerm]; exact hy
  have hrw : (rawInv π).getD y 0 = (encPerm n (decPerm n π)⁻¹).getD y 0 := by
    rw [rawInv_of_wf h]
  rw [invAt, hrw, List.getD_eq_getElem _ _ hlen, getElem_encPerm n _ y hy]

theorem invAt_lt {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {y : ℕ} (hy : y < n) :
    invAt π y < n := by
  rw [invAt_eq h hy]
  exact ((decPerm n π)⁻¹ ⟨y, hy⟩).isLt

theorem rawApply_invAt {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {y : ℕ} (hy : y < n) :
    rawApply (π, invAt π y) = y := by
  have hval : invAt π y = ((decPerm n π)⁻¹ ⟨y, hy⟩ : ℕ) := invAt_eq h hy
  rw [rawApply_of_wf h (invAt_lt h hy)]
  have : (⟨invAt π y, invAt_lt h hy⟩ : Fin n) = (decPerm n π)⁻¹ ⟨y, hy⟩ := Fin.ext hval
  rw [this]
  simp

theorem invAt_rawApply {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {x : ℕ} (hx : x < n) :
    invAt π (rawApply (π, x)) = x :=
  rawApply_inj h (invAt_lt h (rawApply_lt h hx)) hx
    (rawApply_invAt h (rawApply_lt h hx))

/-- The image of a list of vertices under a raw permutation. -/
def permList (π : RawPerm) (t : List ℕ) : List ℕ := t.map (fun a => rawApply (π, a))

@[simp] theorem length_permList (π : RawPerm) (t : List ℕ) :
    (permList π t).length = t.length := by simp [permList]

theorem permList_lt {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) {t : List ℕ}
    (ht : ∀ a ∈ t, a < n) : ∀ b ∈ permList π t, b < n := by
  intro b hb
  rw [permList, List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact rawApply_lt h (ht a ha)

theorem permList_inj {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) :
    ∀ {u t : List ℕ}, (∀ a ∈ u, a < n) → (∀ a ∈ t, a < n) → permList π u = permList π t → u = t
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hh => by simp [permList] at hh
  | _ :: _, [], _, _, hh => by simp [permList] at hh
  | a :: u, b :: t, hu, ht, hh => by
      rw [permList, permList, List.map_cons, List.map_cons] at hh
      have h1 : rawApply (π, a) = rawApply (π, b) := List.head_eq_of_cons_eq hh
      have h2 : permList π u = permList π t := List.tail_eq_of_cons_eq hh
      have hab : a = b := rawApply_inj h (hu a (List.mem_cons_self ..))
        (ht b (List.mem_cons_self ..)) h1
      rw [hab, permList_inj h (fun c hc => hu c (List.mem_cons_of_mem _ hc))
        (fun c hc => ht c (List.mem_cons_of_mem _ hc)) h2]

/-! ## §4.1.1 — the naive refinement is canonical

The relabeling of a raw colored digraph: the vertex `x` becomes `π(x)`, so the color list and
the adjacency list are both read through `π⁻¹`, and the entries of the adjacency rows are sent
through `π`. -/

/-- **The relabeling of a raw colored digraph along a raw permutation.** -/
def relabelCD (z : RawPerm × RawCD) : RawCD :=
  ((rawInv z.1).map (fun w => z.2.1.getD w 0),
    (rawInv z.1).map (fun w => permList z.1 (z.2.2.getD w [])))

@[simp] theorem length_relabelCD_fst (π : RawPerm) (X : RawCD) :
    (relabelCD (π, X)).1.length = π.length := by simp [relabelCD]

@[simp] theorem length_relabelCD_snd (π : RawPerm) (X : RawCD) :
    (relabelCD (π, X)).2.length = π.length := by simp [relabelCD]

theorem col_relabelCD {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) (X : RawCD) {y : ℕ}
    (hy : y < n) : (relabelCD (π, X)).1.getD y 0 = X.1.getD (invAt π y) 0 := by
  have hlen : y < (relabelCD (π, X)).1.length := by
    rw [length_relabelCD_fst, h.length]; exact hy
  have hlen' : y < (rawInv π).length := by rw [length_rawInv, h.length]; exact hy
  rw [List.getD_eq_getElem _ _ hlen]
  show ((rawInv π).map (fun w => X.1.getD w 0))[y]'hlen = _
  rw [List.getElem_map, invAt, List.getD_eq_getElem _ _ hlen']

theorem adj_relabelCD {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) (X : RawCD) {y : ℕ}
    (hy : y < n) :
    (relabelCD (π, X)).2.getD y [] = permList π (X.2.getD (invAt π y) []) := by
  have hlen : y < (relabelCD (π, X)).2.length := by
    rw [length_relabelCD_snd, h.length]; exact hy
  have hlen' : y < (rawInv π).length := by rw [length_rawInv, h.length]; exact hy
  rw [List.getD_eq_getElem _ _ hlen]
  show ((rawInv π).map (fun w => permList π (X.2.getD w [])))[y]'hlen = _
  rw [List.getElem_map, invAt, List.getD_eq_getElem _ _ hlen']

/-- **The relabeled digraph is well formed.** -/
theorem relabelCD_wf {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) : RawCD.WF n (relabelCD (π, X)) where
  colLen := by rw [length_relabelCD_fst, hπ.length]
  colLt := by
    intro a ha
    rw [relabelCD, List.mem_map] at ha
    obtain ⟨w, hw, rfl⟩ := ha
    have hwn : w < n := (wf_rawInv hπ).lt hw
    have hwl : w < X.1.length := by rw [hX.colLen]; exact hwn
    rw [List.getD_eq_getElem _ _ hwl]
    exact hX.colLt _ (List.getElem_mem hwl)
  adjLen := by rw [length_relabelCD_snd, hπ.length]
  adjLt := by
    intro l hl a ha
    rw [relabelCD, List.mem_map] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    have hwn : w < n := (wf_rawInv hπ).lt hw
    have hwl : w < X.2.length := by rw [hX.adjLen]; exact hwn
    have hrow : X.2.getD w [] ∈ X.2 := by
      rw [List.getD_eq_getElem _ _ hwl]; exact List.getElem_mem hwl
    exact permList_lt hπ (hX.adjLt _ hrow) a ha
  adjNodup := by
    intro l hl
    rw [relabelCD, List.mem_map] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    have hwn : w < n := (wf_rawInv hπ).lt hw
    have hwl : w < X.2.length := by rw [hX.adjLen]; exact hwn
    have hrow : X.2.getD w [] ∈ X.2 := by
      rw [List.getD_eq_getElem _ _ hwl]; exact List.getElem_mem hwl
    have hnd := hX.adjNodup _ hrow
    have hlt := hX.adjLt _ hrow
    refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    exact rawApply_inj hπ (hlt a ha) (hlt b hb) hab

/-! ### The tag transports -/

theorem countAt_congr_perm {l l' : List ℕ} (hp : l.Perm l') (i : ℕ) :
    countAt (i, l) = countAt (i, l') := by
  rw [countAt, countAt, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    hp.countP_eq]

theorem tallyCols_congr_perm {col : List ℕ} {l l' : List ℕ} (hp : l.Perm l') :
    tallyCols col l = tallyCols col l' := by
  rw [tallyCols, tallyCols]
  exact List.map_congr_left (fun i _ => countAt_congr_perm hp i)

theorem tallyCols_congr_length {col col' : List ℕ} (h : col.length = col'.length) (l : List ℕ) :
    tallyCols col l = tallyCols col' l := by
  rw [tallyCols, tallyCols, h]

/-- The out-neighbors transport exactly. -/
theorem outNbrs_relabelCD {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) (X : RawCD) {x : ℕ}
    (hx : x < n) :
    outNbrs (relabelCD (π, X)).2 (rawApply (π, x)) = permList π (outNbrs X.2 x) := by
  rw [outNbrs, outNbrs, adj_relabelCD h X (rawApply_lt h hx), invAt_rawApply h hx]

/-- The colors of a relabeled list of vertices are the colors of the list. -/
theorem nbrCols_relabelCD {n : ℕ} {π : RawPerm} (h : RawPerm.WF n π) (X : RawCD) {l : List ℕ}
    (hl : ∀ a ∈ l, a < n) :
    nbrCols (relabelCD (π, X)).1 (permList π l) = nbrCols X.1 l := by
  rw [nbrCols, nbrCols, permList, List.map_map]
  refine List.map_congr_left (fun a ha => ?_)
  show (relabelCD (π, X)).1.getD (rawApply (π, a)) 0 = X.1.getD a 0
  rw [col_relabelCD h X (rawApply_lt h (hl a ha)), invAt_rawApply h (hl a ha)]

/-- The in-neighbors transport up to the order in which they are listed. -/
theorem inNbrs_relabelCD_perm {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) {x : ℕ} (hx : x < n) :
    ((inNbrs (relabelCD (π, X)).2 (rawApply (π, x))).map (fun z => invAt π z)).Perm
      (inNbrs X.2 x) := by
  classical
  set Y := relabelCD (π, X) with hY
  have hYlen : Y.2.length = n := by rw [hY, length_relabelCD_snd, hπ.length]
  have hXlen : X.2.length = n := hX.adjLen
  have hmemY : ∀ z, z ∈ inNbrs Y.2 (rawApply (π, x)) ↔ (z < n ∧ invAt π z ∈ inNbrs X.2 x) := by
    intro z
    rw [mem_inNbrs, hYlen]
    constructor
    · rintro ⟨hz, hmem⟩
      refine ⟨hz, ?_⟩
      rw [hY, adj_relabelCD hπ X hz] at hmem
      rw [mem_inNbrs, hXlen]
      refine ⟨invAt_lt hπ hz, ?_⟩
      rw [permList, List.mem_map] at hmem
      obtain ⟨b, hb, hbx⟩ := hmem
      have hbn : b < n := by
        have hwl : invAt π z < X.2.length := by rw [hXlen]; exact invAt_lt hπ hz
        have hrow : X.2.getD (invAt π z) [] ∈ X.2 := by
          rw [List.getD_eq_getElem _ _ hwl]; exact List.getElem_mem hwl
        exact hX.adjLt _ hrow b hb
      have : b = x := rawApply_inj hπ hbn hx hbx
      rwa [this] at hb
    · rintro ⟨hz, hmem⟩
      refine ⟨hz, ?_⟩
      rw [hY, adj_relabelCD hπ X hz, permList, List.mem_map]
      obtain ⟨-, hmem'⟩ := mem_inNbrs.1 hmem
      exact ⟨x, hmem', rfl⟩
  refine List.perm_of_nodup_nodup_toFinset_eq ?_ (nodup_inNbrs _ _) ?_
  · refine List.Nodup.map_on ?_ (nodup_inNbrs _ _)
    intro a ha b hb hab
    have han : a < n := by
      have := inNbrs_lt ha; rw [hYlen] at this; exact this
    have hbn : b < n := by
      have := inNbrs_lt hb; rw [hYlen] at this; exact this
    have : rawApply (π, invAt π a) = rawApply (π, invAt π b) := by rw [hab]
    rwa [rawApply_invAt hπ han, rawApply_invAt hπ hbn] at this
  · ext w
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ((hmemY z).1 hz).2
    · intro hw
      have hwn : w < n := by
        have := inNbrs_lt hw; rw [hXlen] at this; exact this
      refine ⟨rawApply (π, w), ?_, invAt_rawApply hπ hwn⟩
      refine (hmemY _).2 ⟨rawApply_lt hπ hwn, ?_⟩
      rwa [invAt_rawApply hπ hwn]

/-- **§4.1.1: the tag of a vertex transports along a relabeling.** -/
theorem tagAt_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) {x : ℕ} (hx : x < n) :
    tagAt (relabelCD (π, X)) (rawApply (π, x)) = tagAt X x := by
  set Y := relabelCD (π, X) with hY
  have hcolLen : Y.1.length = X.1.length := by
    rw [hY, length_relabelCD_fst, hπ.length, hX.colLen]
  have hhead : Y.1.getD (rawApply (π, x)) 0 = X.1.getD x 0 := by
    rw [hY, col_relabelCD hπ X (rawApply_lt hπ hx), invAt_rawApply hπ hx]
  -- out-neighbors
  have hout : nbrCols Y.1 (outNbrs Y.2 (rawApply (π, x))) = nbrCols X.1 (outNbrs X.2 x) := by
    have hrowlt : ∀ a ∈ outNbrs X.2 x, a < n := by
      have hxl : x < X.2.length := by rw [hX.adjLen]; exact hx
      have hrow : outNbrs X.2 x ∈ X.2 := by
        rw [outNbrs, List.getD_eq_getElem _ _ hxl]; exact List.getElem_mem hxl
      exact hX.adjLt _ hrow
    rw [hY, outNbrs_relabelCD hπ X hx, nbrCols_relabelCD hπ X hrowlt]
  -- in-neighbors, up to order
  have hinperm := inNbrs_relabelCD_perm hπ hX hx
  have hin : (nbrCols Y.1 (inNbrs Y.2 (rawApply (π, x)))).Perm
      (nbrCols X.1 (inNbrs X.2 x)) := by
    have hmaplt : ∀ z ∈ inNbrs Y.2 (rawApply (π, x)), z < n := by
      intro z hz
      have := inNbrs_lt hz
      rw [hY, length_relabelCD_snd, hπ.length] at this
      exact this
    have hstep : nbrCols Y.1 (inNbrs Y.2 (rawApply (π, x)))
        = nbrCols X.1 ((inNbrs Y.2 (rawApply (π, x))).map (fun z => invAt π z)) := by
      rw [nbrCols, nbrCols, List.map_map]
      refine List.map_congr_left (fun z hz => ?_)
      show Y.1.getD z 0 = X.1.getD (invAt π z) 0
      rw [hY, col_relabelCD hπ X (hmaplt z hz)]
    rw [hstep]
    exact (hinperm.map (fun w => X.1.getD w 0) : _)
  rw [tagAt, tagAt, hhead, hout, tallyCols_congr_length hcolLen,
    tallyCols_congr_length hcolLen (nbrCols Y.1 (inNbrs Y.2 (rawApply (π, x)))),
    tallyCols_congr_perm hin]

/-! ### The names are the same

The set of tags is the same on both sides, so the rank of a tag is the same, and the new color
of `π(x)` is the new color of `x` — the *same* natural number, not only the same class. -/

theorem rawTags_relabelCD_mem {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) (t : List ℕ) :
    t ∈ rawTags (relabelCD (π, X)) ↔ t ∈ rawTags X := by
  have hYcol : (relabelCD (π, X)).1.length = n := by
    rw [length_relabelCD_fst, hπ.length]
  constructor
  · intro ht
    obtain ⟨y, hy, rfl⟩ := mem_rawTags.1 ht
    rw [hYcol] at hy
    have hx : invAt π y < n := invAt_lt hπ hy
    refine mem_rawTags.2 ⟨invAt π y, by rw [hX.colLen]; exact hx, ?_⟩
    rw [← tagAt_relabelCD hπ hX hx, rawApply_invAt hπ hy]
  · intro ht
    obtain ⟨x, hx, rfl⟩ := mem_rawTags.1 ht
    rw [hX.colLen] at hx
    refine mem_rawTags.2 ⟨rawApply (π, x), by rw [hYcol]; exact rawApply_lt hπ hx, ?_⟩
    exact tagAt_relabelCD hπ hX hx

/-- **§4.1.1: one round of naive refinement is canonical, names included.**  The new color of
`π(x)` in the relabeled digraph is the new color of `x`, as a natural number. -/
theorem rawNewCol_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) {x : ℕ} (hx : x < n) :
    (rawNewCol (relabelCD (π, X))).getD (rawApply (π, x)) 0 = (rawNewCol X).getD x 0 := by
  have hYcol : (relabelCD (π, X)).1.length = n := by
    rw [length_relabelCD_fst, hπ.length]
  rw [getD_rawNewCol (by rw [hYcol]; exact rawApply_lt hπ hx),
    getD_rawNewCol (by rw [hX.colLen]; exact hx), tagAt_relabelCD hπ hX hx]
  exact rankIn_rawColorSet_congr (rawTags_relabelCD_mem hπ hX) _

/-- **One round commutes with the relabeling.** -/
theorem rawRefineStep_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) :
    rawRefineStep (relabelCD (π, X)) = relabelCD (π, rawRefineStep X) := by
  have hYcol : (relabelCD (π, X)).1.length = n := by
    rw [length_relabelCD_fst, hπ.length]
  refine Prod.ext ?_ rfl
  show rawNewCol (relabelCD (π, X)) = (rawInv π).map (fun w => (rawNewCol X).getD w 0)
  refine List.ext_getElem ?_ (fun y h1 h2 => ?_)
  · rw [length_rawNewCol, hYcol, List.length_map, length_rawInv, hπ.length]
  · have hy : y < n := by rw [length_rawNewCol, hYcol] at h1; exact h1
    have hlen' : y < (rawInv π).length := by rw [length_rawInv, hπ.length]; exact hy
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
    have hright : ((rawInv π).map (fun w => (rawNewCol X).getD w 0)).getD y 0
        = (rawNewCol X).getD (invAt π y) 0 := by
      rw [List.getD_eq_getElem _ _ h2]
      show ((rawInv π).map (fun w => (rawNewCol X).getD w 0))[y]'h2 = _
      rw [List.getElem_map, invAt, List.getD_eq_getElem _ _ hlen']
    have hstep := rawNewCol_relabelCD hπ hX (invAt_lt hπ hy)
    rw [rawApply_invAt hπ hy] at hstep
    rw [hright, hstep]

theorem rawRefineIter_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) :
    ∀ j : ℕ, rawRefineStep^[j] (relabelCD (π, X)) = relabelCD (π, rawRefineStep^[j] X)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', rawRefineIter_relabelCD hπ hX j,
        Function.iterate_succ_apply']
      exact rawRefineStep_relabelCD hπ (wf_iterate hX j)

/-- **§4.1, `X*`: the stable refinement commutes with the relabeling.**  This is the canonicity
of §4, Eq. (22) for the routine of `Workspace/Algo/RefineRaw.lean`, in its strong form: the
answer on the relabeled input is the relabeled answer, so the color *names* agree. -/
theorem rawStableRefine_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD} (hπ : RawPerm.WF n π)
    (hX : RawCD.WF n X) :
    rawStableRefine (relabelCD (π, X)) = relabelCD (π, rawStableRefine X) := by
  have hYcol : (relabelCD (π, X)).1.length = n := by
    rw [length_relabelCD_fst, hπ.length]
  rw [rawStableRefine_eq_iterate, rawStableRefine_eq_iterate, hYcol, hX.colLen]
  exact rawRefineIter_relabelCD hπ hX (n * n)

/-- **The colorwise form**: the vertex `π(x)` of the relabeled digraph gets exactly the color
that `x` gets. -/
theorem color_rawStableRefine_relabelCD {n : ℕ} {π : RawPerm} {X : RawCD}
    (hπ : RawPerm.WF n π) (hX : RawCD.WF n X) {x : ℕ} (hx : x < n) :
    (rawStableRefine (relabelCD (π, X))).1.getD (rawApply (π, x)) 0
      = (rawStableRefine X).1.getD x 0 := by
  rw [rawStableRefine_relabelCD hπ hX,
    col_relabelCD hπ (rawStableRefine X) (rawApply_lt hπ hx), invAt_rawApply hπ hx]

/-! ## §5.4.1 — the `k`-ary WL refinement is canonical

The relabeling of a table of `k`-tuples: every vertex and every entry of every key is sent
through `π`, and the rows stay in the order they were in. -/

/-- **The relabeling of a raw table of `k`-tuples along a raw permutation.** -/
def relabelWL (z : RawPerm × RawWL) : RawWL :=
  (permList z.1 z.2.1, z.2.2.map (fun q => (permList z.1 q.1, q.2)))

@[simp] theorem relabelWL_fst (π : RawPerm) (p : RawWL) :
    (relabelWL (π, p)).1 = permList π p.1 := rfl

@[simp] theorem relabelWL_length (π : RawPerm) (p : RawWL) :
    (relabelWL (π, p)).2.length = p.2.length := by simp [relabelWL]

theorem mem_relabelWL_keys {π : RawPerm} {p : RawWL} {t : List ℕ} :
    t ∈ (relabelWL (π, p)).2.map Prod.fst ↔ ∃ s ∈ p.2.map Prod.fst, permList π s = t := by
  constructor
  · intro ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
    rw [relabelWL] at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact ⟨q'.1, List.mem_map_of_mem hq', rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs
    refine List.mem_map.2 ⟨(permList π q.1, q.2), ?_, rfl⟩
    rw [relabelWL]
    exact List.mem_map_of_mem hq

/-- **The relabeled table is well formed.** -/
theorem relabelWL_wf {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) : RawWL.WF n k (relabelWL (π, p)) where
  domNodup := by
    refine List.Nodup.map_on ?_ hp.domNodup
    intro a ha b hb hab
    exact rawApply_inj hπ ((hp.domMem a).1 ha) ((hp.domMem b).1 hb) hab
  domMem := by
    intro a
    constructor
    · intro ha
      rw [relabelWL_fst, permList, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact rawApply_lt hπ ((hp.domMem b).1 hb)
    · intro ha
      rw [relabelWL_fst, permList, List.mem_map]
      exact ⟨invAt π a, (hp.domMem _).2 (invAt_lt hπ ha), rawApply_invAt hπ ha⟩
  keyNodup := by
    rw [relabelWL]
    simp only [List.map_map, Function.comp_def]
    have hkeys : (p.2.map Prod.fst).Nodup := hp.keyNodup
    have := List.Nodup.map_on
      (f := fun s => permList π s)
      (l := p.2.map Prod.fst)
      (by
        intro a ha b hb hab
        exact permList_inj hπ ((hp.keyMem a).1 ha).2 ((hp.keyMem b).1 hb).2 hab) hkeys
    simpa [List.map_map, Function.comp_def] using this
  keyMem := by
    intro t
    rw [mem_relabelWL_keys]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨hlen, hlt⟩ := (hp.keyMem s).1 hs
      exact ⟨by rw [length_permList]; exact hlen, permList_lt hπ hlt⟩
    · rintro ⟨hlen, hlt⟩
      refine ⟨t.map (fun a => invAt π a), (hp.keyMem _).2 ⟨by simp [hlen], ?_⟩, ?_⟩
      · intro a ha
        rw [List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact invAt_lt hπ (hlt b hb)
      · rw [permList, List.map_map]
        refine List.map_congr_left (fun a ha => ?_) |>.trans (List.map_id _)
        show rawApply (π, invAt π a) = id a
        exact rawApply_invAt hπ (hlt a ha)
  colLt := by
    intro q hq
    rw [relabelWL] at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [relabelWL_length]
    exact hp.colLt q' hq'

/-! ### Reading the relabeled table -/

theorem lookup_permList {n : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π) :
    ∀ (l : List (List ℕ × ℕ)) (t : List ℕ), (∀ q ∈ l, ∀ a ∈ q.1, a < n) → (∀ a ∈ t, a < n) →
      (l.map (fun q => (permList π q.1, q.2))).lookup (permList π t) = l.lookup t
  | [], t, _, _ => rfl
  | q :: l, t, hl, ht => by
      have hq : ∀ a ∈ q.1, a < n := hl q (List.mem_cons_self ..)
      have hl' : ∀ r ∈ l, ∀ a ∈ r.1, a < n := fun r hr => hl r (List.mem_cons_of_mem _ hr)
      by_cases hqt : t = q.1
      · subst hqt
        simp [List.lookup]
      · have hne : permList π t ≠ permList π q.1 := fun hc => hqt (permList_inj hπ ht hq hc)
        have hb1 : (t == q.1) = false := beq_eq_false_iff_ne.2 hqt
        have hb2 : (permList π t == permList π q.1) = false := beq_eq_false_iff_ne.2 hne
        simp only [List.map_cons]
        rw [show List.lookup (permList π t) ((permList π q.1, q.2)
              :: l.map (fun r => (permList π r.1, r.2)))
            = List.lookup (permList π t) (l.map (fun r => (permList π r.1, r.2))) by
          simp [List.lookup, hb2]]
        rw [show List.lookup t (q :: l) = List.lookup t l by simp [List.lookup, hb1]]
        exact lookup_permList hπ l t hl' ht

/-- **The relabeled table answers at the relabeled tuple what the table answers.** -/
theorem tblGet_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) :
    tblGet ((relabelWL (π, p)).2, permList π t) = tblGet (p.2, t) := by
  rw [tblGet, tblGet, relabelWL]
  show ((p.2.map (fun q => (permList π q.1, q.2))).lookup (permList π t)).getD 0 = _
  rw [lookup_permList hπ p.2 t (fun q hq a ha =>
    ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).2 a ha) ht]

theorem substAt_permList (π : RawPerm) (i y : ℕ) (t : List ℕ) :
    substAt ((i, rawApply (π, y)), permList π t) = permList π (substAt ((i, y), t)) := by
  refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
  simp only [substAt, permList, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  by_cases hij : j = i <;> simp [hij]

/-- **The tuple of old colors transports.** -/
theorem innerVec_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) {y : ℕ} (hy : y < n) :
    innerVec (relabelWL (π, p)).2 (permList π t) (rawApply (π, y)) = innerVec p.2 t y := by
  rw [innerVec, innerVec, length_permList]
  refine List.map_congr_left (fun i _ => ?_)
  rw [substAt_permList]
  refine tblGet_relabelWL hπ hp ?_
  intro a ha
  rw [substAt_eq_set] at ha
  rcases List.mem_or_eq_of_mem_set ha with ha' | rfl
  · exact ht a ha'
  · exact hy

/-! ### The tag transports -/

theorem mem_allVecs_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) (v : List ℕ) :
    v ∈ allVecs (relabelWL (π, p)) ↔ v ∈ allVecs p := by
  constructor
  · intro hv
    obtain ⟨q, hq, y, hy, rfl⟩ := exists_of_mem_allVecs hv
    rw [relabelWL] at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    have hy' : y ∈ permList π p.1 := hy
    rw [permList, List.mem_map] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    have hzn : z < n := (hp.domMem z).1 hz
    have hkey : ∀ a ∈ q'.1, a < n := ((hp.keyMem q'.1).1 (List.mem_map_of_mem hq')).2
    rw [show ((permList π q'.1, q'.2) : List ℕ × ℕ).1 = permList π q'.1 from rfl,
      innerVec_relabelWL hπ hp hkey hzn]
    exact mem_allVecs hq' hz
  · intro hv
    obtain ⟨q, hq, y, hy, rfl⟩ := exists_of_mem_allVecs hv
    have hyn : y < n := (hp.domMem y).1 hy
    have hkey : ∀ a ∈ q.1, a < n := ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).2
    rw [← innerVec_relabelWL hπ hp hkey hyn]
    refine mem_allVecs (q := (permList π q.1, q.2)) ?_ ?_
    · rw [relabelWL]; exact List.mem_map_of_mem hq
    · show rawApply (π, y) ∈ permList π p.1
      exact List.mem_map_of_mem hy

theorem rankIn_vecSet_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) (v : List ℕ) :
    rankIn (vecSet (relabelWL (π, p)), v) = rankIn (vecSet p, v) :=
  rankIn_congr_mem (nodup_vecSet _) (nodup_vecSet _)
    (fun u => mem_vecSet.trans ((mem_allVecs_relabelWL hπ hp u).trans mem_vecSet.symm)) v

theorem length_vecSet_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) :
    (vecSet (relabelWL (π, p))).length = (vecSet p).length :=
  (List.perm_of_nodup_nodup_toFinset_eq (nodup_vecSet _) (nodup_vecSet _)
    (by
      ext u
      simpa using mem_vecSet.trans
        ((mem_allVecs_relabelWL hπ hp u).trans mem_vecSet.symm))).length_eq

theorem wlCount_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) (j : ℕ) :
    wlCount (relabelWL (π, p)) (permList π t) j = wlCount p t j := by
  rw [wlCount, wlCount, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    relabelWL_fst,
    show permList π p.1 = p.1.map (fun a => rawApply (π, a)) from rfl, List.countP_map]
  simp only [Function.comp_def]
  refine List.countP_congr (fun y hy => ?_)
  have hyn : y < n := (hp.domMem y).1 hy
  have h1 : innerVec (relabelWL (π, p)).2 (permList π t) (rawApply (π, y)) = innerVec p.2 t y :=
    innerVec_relabelWL hπ hp ht hyn
  have h2 := rankIn_vecSet_relabelWL hπ hp (innerVec p.2 t y)
  simp only [h1, h2]

/-- **§5.4.1: the tag of a tuple transports along a relabeling.** -/
theorem wlTagAt_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) :
    wlTagAt (relabelWL (π, p)) (permList π t) = wlTagAt p t := by
  rw [wlTagAt, wlTagAt, tblGet_relabelWL hπ hp ht, length_vecSet_relabelWL hπ hp]
  congr 1
  exact List.map_congr_left (fun j _ => wlCount_relabelWL hπ hp ht j)

theorem mem_wlTags_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) (t : List ℕ) :
    t ∈ wlTags (relabelWL (π, p)) ↔ t ∈ wlTags p := by
  constructor
  · intro ht
    rw [wlTags, List.mem_map] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    rw [relabelWL] at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    have hkey : ∀ a ∈ q'.1, a < n := ((hp.keyMem q'.1).1 (List.mem_map_of_mem hq')).2
    rw [show ((permList π q'.1, q'.2) : List ℕ × ℕ).1 = permList π q'.1 from rfl,
      wlTagAt_relabelWL hπ hp hkey]
    exact List.mem_map_of_mem hq'
  · intro ht
    rw [wlTags, List.mem_map] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    have hkey : ∀ a ∈ q.1, a < n := ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).2
    rw [← wlTagAt_relabelWL hπ hp hkey]
    refine List.mem_map.2 ⟨(permList π q.1, q.2), ?_, rfl⟩
    rw [relabelWL]
    exact List.mem_map_of_mem hq

theorem nodup_wlTagSet (p : RawWL) : (wlTagSet p).Nodup := RAM.nodup_dedupG _

/-- **§5.4.1: one round is canonical, names included.** -/
theorem wlNewCol_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) :
    wlNewCol (relabelWL (π, p)) (permList π t) = wlNewCol p t := by
  rw [wlNewCol, wlNewCol, wlTagAt_relabelWL hπ hp ht]
  exact rankIn_congr_mem (nodup_wlTagSet _) (nodup_wlTagSet _)
    (fun u => mem_wlTagSet.trans ((mem_wlTags_relabelWL hπ hp u).trans mem_wlTagSet.symm)) _

/-- **One round commutes with the relabeling.** -/
theorem rawWLStep_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) :
    rawWLStep (relabelWL (π, p)) = relabelWL (π, rawWLStep p) := by
  refine Prod.ext rfl ?_
  show ((relabelWL (π, p)).2.map (fun q => (q.1, wlNewCol (relabelWL (π, p)) q.1)))
    = (p.2.map (fun q => (q.1, wlNewCol p q.1))).map (fun q => (permList π q.1, q.2))
  rw [relabelWL]
  simp only [List.map_map, Function.comp_def]
  refine List.map_congr_left (fun q hq => ?_)
  have hkey : ∀ a ∈ q.1, a < n := ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).2
  show ((permList π q.1, wlNewCol (relabelWL (π, p)) (permList π q.1)) : List ℕ × ℕ)
    = (permList π q.1, wlNewCol p q.1)
  rw [wlNewCol_relabelWL hπ hp hkey]

theorem rawWLIter_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) :
    ∀ j : ℕ, rawWLStep^[j] (relabelWL (π, p)) = relabelWL (π, rawWLStep^[j] p)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', rawWLIter_relabelWL hπ hp j,
        Function.iterate_succ_apply']
      exact rawWLStep_relabelWL hπ (wf_rawWLIter hp j)

/-- **§5.4.1: the stable `k`-ary refinement commutes with the relabeling.**  This is the
canonicity of §4, Eq. (22) for the routine of `Workspace/Algo/WLRaw.lean`, in its strong form:
the answer on the relabeled table is the relabeled answer, so the color *names* agree. -/
theorem rawWLStable_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) :
    rawWLStable (relabelWL (π, p)) = relabelWL (π, rawWLStable p) := by
  rw [rawWLStable_eq_iterate, rawWLStable_eq_iterate, relabelWL_length]
  exact rawWLIter_relabelWL hπ hp _

/-- **The colorwise form**: the relabeled tuple gets exactly the color that the tuple gets. -/
theorem tblGet_rawWLStable_relabelWL {n k : ℕ} {π : RawPerm} {p : RawWL} (hπ : RawPerm.WF n π)
    (hp : RawWL.WF n k p) {t : List ℕ} (ht : ∀ a ∈ t, a < n) :
    tblGet ((rawWLStable (relabelWL (π, p))).2, permList π t)
      = tblGet ((rawWLStable p).2, t) := by
  rw [rawWLStable_relabelWL hπ hp]
  exact tblGet_relabelWL hπ (rawWLStable_wf hp) ht

end Algo
