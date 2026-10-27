/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the tests and the outcome of §8.2 are canonical relative to `x⃗`.
-/
import Workspace.Algo.DesignOut
import Workspace.Algo.Relabel
import Workspace.Algo.PipelineRelabel

/-!
# §8.2 — canonicity of the Design Lemma procedure relative to `x⃗`

Theorem 8.1.2 ends with *"Canonicity in the above statements is relative to `x⃗`"*: the objects
lines 05 and 08 return must depend on the input structure and on the string `x⃗` only, not on the
names of the vertices.  On raw data that is the statement of this file: relabel the vertices by
a permutation `π` and relabel the string with them, and

* the test of lines 03–08 gives the same Boolean (`Algo.returnsB_relabel`);
* the vertex coloring of line 05 is *unchanged* as a list — entry `j` is the color of the `j`-th
  vertex of the (relabeled) vertex list, and the color names agree (`Algo.restrVColors_relabel`);
* the dominant class of line 06 is the image `π(C(x⃗))` (`Algo.dominantList_relabel`);
* the rank of the `2`-skeleton on it is unchanged (`Algo.cliqueRank_relabel`).

With `Workspace/Algo/PipelineRelabel.lean` (line 01 is canonical) this closes the loop: the whole
of Procedure "Design Lemma" is canonical, `Algo.designOutcome_relabel`.  The string the scan
returns is the relabeled string — not because the choice among the returning strings of the least
length is canonical (it is not, risk R-A9-1), but because the routine enumerates the strings in
the order the fold produces them and the fold is order-preserving, so the enumeration over the
relabeled vertex list is the relabeled enumeration in the same order.

Everything rests on one equivariance: the individualized tuple of §8.2 is equivariant,
`Algo.indivTuple_permList`, so the relabeled table answers at the relabeled tuple what the table
answers (`Algo.tblGet_relabelWL`, A8).  Canonicity of line 01 itself is `Algo.rawWLStable_relabelWL`
(A8).  This closes risk R-A9-4 for the tests and the outcome at a **given** string, which is the
paper's "relative to `x⃗`"; the choice of the string among those of the least returning length is
not canonical and is not claimed to be (risk R-A9-1, `Babai.KAryPartStruct.procedure` chooses it
with `Exists.choose`).

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## Two list lemmas -/

theorem filter_map_comm {α β : Type*} (f : α → β) (q : β → Bool) : ∀ l : List α,
    (l.map f).filter q = (l.filter (fun a => q (f a))).map f
  | [] => rfl
  | a :: l => by
      by_cases h : q (f a) <;> simp [h, filter_map_comm f q l]

theorem map_permList {β : Type*} (f : ℕ → β) (π : RawPerm) (l : List ℕ) :
    (permList π l).map f = l.map (fun c => f (rawApply (π, c))) := by
  rw [permList, List.map_map]; rfl

theorem filter_permList (q : ℕ → Bool) (π : RawPerm) (l : List ℕ) :
    (permList π l).filter q = permList π (l.filter (fun c => q (rawApply (π, c)))) := by
  rw [permList, filter_map_comm]; rfl

theorem getD_permList (π : RawPerm) (t : List ℕ) (i d : ℕ) :
    (permList π t).getD i (rawApply (π, d)) = rawApply (π, t.getD i d) := by
  by_cases h : i < t.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
    simp [permList]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h),
      List.getD_eq_default _ _ (Nat.le_of_not_lt h)]

/-! ## The individualized tuple is equivariant -/

theorem indivTuple_lt {n : ℕ} {ks xs : List ℕ} {u v : ℕ} (hxs : ∀ c ∈ xs, c < n) (hu : u < n)
    (hv : v < n) : ∀ c ∈ indivTuple ((ks, xs), (u, v)), c < n := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ : ∃ i, ∃ h : i < (indivTuple ((ks, xs), (u, v))).length,
      (indivTuple ((ks, xs), (u, v)))[i] = c := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.1 hc
    exact ⟨i, hi.choose, hi.choose_spec⟩
  rw [getElem_indivTuple]
  by_cases h : i < xs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hxs _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    by_cases h2 : i = xs.length <;> simp [h2, hu, hv]

/-- **The individualized tuple `x⃗ u v v … v` is equivariant.**  This is the one equivariance the
whole of §8.2 rests on: relabeling the string and the two vertices relabels the tuple that is
looked up. -/
theorem indivTuple_permList (π : RawPerm) (ks xs : List ℕ) (u v : ℕ) :
    indivTuple ((ks, permList π xs), (rawApply (π, u), rawApply (π, v)))
      = permList π (indivTuple ((ks, xs), (u, v))) := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  rw [getElem_indivTuple]
  show (permList π xs).getD i (if i = (permList π xs).length then rawApply (π, u)
      else rawApply (π, v)) = (permList π (indivTuple ((ks, xs), (u, v))))[i]
  rw [length_permList]
  have hd : (if i = xs.length then rawApply (π, u) else rawApply (π, v))
      = rawApply (π, if i = xs.length then u else v) := by
    by_cases h : i = xs.length <;> simp [h]
  rw [hd, getD_permList]
  show _ = ((indivTuple ((ks, xs), (u, v))).map (fun a => rawApply (π, a)))[i]
  rw [List.getElem_map, getElem_indivTuple]

/-! ## The reads are equivariant -/

section Reads

variable {n k a b : ℕ} {π : RawPerm} {ks xs : List ℕ} {p : RawWL}

/-- **Line 07's read is canonical.**  The `2`-skeleton color of the relabeled pair in the
relabeled structure is the `2`-skeleton color of the pair. -/
theorem restrPairColorAt_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) {u v : ℕ} (hu : u < n) (hv : v < n) :
    restrPairColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)),
        (rawApply (π, u), rawApply (π, v)))
      = restrPairColorAt ((((ks, xs), p), (a, b)), (u, v)) := by
  show tblGet ((relabelWL (π, p)).2,
      indivTuple ((ks, permList π xs), (rawApply (π, u), rawApply (π, v))))
    = tblGet (p.2, indivTuple ((ks, xs), (u, v)))
  rw [indivTuple_permList]
  exact tblGet_relabelWL hπ hp (indivTuple_lt hxs hu hv)

/-- **Lines 04–06's read is canonical.** -/
theorem restrVColorAt_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) {u : ℕ} (hu : u < n) :
    restrVColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)), rawApply (π, u))
      = restrVColorAt ((((ks, xs), p), (a, b)), u) :=
  restrPairColorAt_relabel hπ hp hxs hu hu

/-- **Goal (i) is canonical.**  The vertex coloring of `X_x⃗` returned by line 05 is unchanged by
a relabeling: its `j`-th entry is the color of the `j`-th vertex of the vertex list, and the
color *names* agree, not only the partition. -/
theorem restrVColors_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    restrVColors (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = restrVColors (((ks, xs), p), (a, b)) := by
  show (permList π p.1).map (fun y =>
      restrVColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)), y))
    = p.1.map (fun c => restrVColorAt ((((ks, xs), p), (a, b)), c))
  rw [map_permList]
  refine List.map_congr_left (fun c hc => ?_)
  exact restrVColorAt_relabel hπ hp hxs ((hp.domMem c).1 hc)

theorem classSize_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) (i : ℕ) :
    classSize ((((ks, permList π xs), relabelWL (π, p)), (a, b)), i)
      = classSize ((((ks, xs), p), (a, b)), i) := by
  show ((permList π p.1).filter (fun y =>
      decide (restrVColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)), y) = i))).length
    = (p.1.filter (fun c => decide (restrVColorAt ((((ks, xs), p), (a, b)), c) = i))).length
  rw [filter_permList, length_permList]
  congr 1
  refine List.filter_congr (fun c hc => ?_)
  rw [restrVColorAt_relabel hπ hp hxs ((hp.domMem c).1 hc)]

theorem length_relabelWL_dom (π : RawPerm) (p : RawWL) :
    (relabelWL (π, p)).1.length = p.1.length := by simp

/-- **Lines 04–05 are canonical**: the test *"every vertex-color class has size `≤ αn`"* is
invariant under a relabeling. -/
theorem noDominantB_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    noDominantB (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = noDominantB (((ks, xs), p), (a, b)) := by
  show ((restrVColors (((ks, permList π xs), relabelWL (π, p)), (a, b))).filter fun i =>
      !decide (b * classSize ((((ks, permList π xs), relabelWL (π, p)), (a, b)), i)
        ≤ a * (relabelWL (π, p)).1.length)).isEmpty
    = ((restrVColors (((ks, xs), p), (a, b))).filter fun i =>
      !decide (b * classSize ((((ks, xs), p), (a, b)), i) ≤ a * p.1.length)).isEmpty
  rw [restrVColors_relabel hπ hp hxs, length_relabelWL_dom]
  congr 1
  refine List.filter_congr (fun i _ => ?_)
  rw [classSize_relabel hπ hp hxs i]

/-- **Line 06's dominant class is canonical**: `C(π x⃗) = π(C(x⃗))`. -/
theorem dominantList_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    dominantList (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = permList π (dominantList (((ks, xs), p), (a, b))) := by
  show (permList π p.1).filter (fun y => decide (a * (relabelWL (π, p)).1.length + 1
      ≤ b * classSize ((((ks, permList π xs), relabelWL (π, p)), (a, b)),
          restrVColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)), y))))
    = permList π (p.1.filter (fun c => decide (a * p.1.length + 1
      ≤ b * classSize ((((ks, xs), p), (a, b)),
          restrVColorAt ((((ks, xs), p), (a, b)), c)))))
  rw [length_relabelWL_dom, filter_permList]
  congr 1
  refine List.filter_congr (fun c hc => ?_)
  have hcn : c < n := (hp.domMem c).1 hc
  rw [restrVColorAt_relabel hπ hp hxs hcn, classSize_relabel hπ hp hxs]

/-- **Line 07's list of pair colors is canonical.** -/
theorem pairColors_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    pairColors (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = pairColors (((ks, xs), p), (a, b)) := by
  have hdlt : ∀ c ∈ dominantList (((ks, xs), p), (a, b)), c < n := fun c hc =>
    lt_of_mem_dominantList hp hc
  show ((dominantList (((ks, permList π xs), relabelWL (π, p)), (a, b))).map fun u =>
      (dominantList (((ks, permList π xs), relabelWL (π, p)), (a, b))).map fun v =>
        restrPairColorAt ((((ks, permList π xs), relabelWL (π, p)), (a, b)), (u, v))).flatten
    = ((dominantList (((ks, xs), p), (a, b))).map fun u =>
      (dominantList (((ks, xs), p), (a, b))).map fun v =>
        restrPairColorAt ((((ks, xs), p), (a, b)), (u, v))).flatten
  rw [dominantList_relabel hπ hp hxs, map_permList]
  congr 1
  refine List.map_congr_left (fun c hc => ?_)
  rw [map_permList]
  refine List.map_congr_left (fun d hd => ?_)
  exact restrPairColorAt_relabel hπ hp hxs (hdlt c hc) (hdlt d hd)

/-- **Line 07 is canonical**: the rank of the `2`-skeleton on the dominant class is unchanged. -/
theorem cliqueRank_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    cliqueRank (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = cliqueRank (((ks, xs), p), (a, b)) := by
  rw [cliqueRank, cliqueRank, pairColors_relabel hπ hp hxs]

/-- **Line 03 is canonical**: a relabeled string is a string of distinct vertices exactly when
the string is. -/
theorem nodupB_permList (hπ : RawPerm.WF n π) (hxs : ∀ c ∈ xs, c < n) :
    nodupB (permList π xs) = nodupB xs := by
  rw [Bool.eq_iff_iff, nodupB_eq_true, nodupB_eq_true]
  constructor
  · intro h; exact List.Nodup.of_map _ h
  · intro h
    exact List.Nodup.map_on
      (fun c hc d hd hcd => rawApply_inj hπ (hxs c hc) (hxs d hd) hcd) h

/-- **The test of lines 03–08 is canonical relative to `x⃗`.**  Relabeling the vertices and the
string does not change the Boolean the procedure computes at the string. -/
theorem returnsB_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    returnsB (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = returnsB (((ks, xs), p), (a, b)) := by
  show (if nodupB (permList π xs) then
      (if noDominantB (((ks, permList π xs), relabelWL (π, p)), (a, b)) then true
        else if decide ((permList π xs).length + 2 ≤ ks.length) then
          !decide (cliqueRank (((ks, permList π xs), relabelWL (π, p)), (a, b)) = 2)
        else false) else false)
    = (if nodupB xs then
      (if noDominantB (((ks, xs), p), (a, b)) then true
        else if decide (xs.length + 2 ≤ ks.length) then
          !decide (cliqueRank (((ks, xs), p), (a, b)) = 2) else false) else false)
  rw [nodupB_permList hπ hxs, noDominantB_relabel hπ hp hxs, cliqueRank_relabel hπ hp hxs,
    length_permList]

/-- **The outcome of lines 05 and 08 is canonical relative to `x⃗`.**  The vertex coloring is
unchanged, the dominant class is carried over by `π`, and the rank is unchanged. -/
theorem designOutRaw_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hxs : ∀ c ∈ xs, c < n) :
    designOutRaw (((ks, permList π xs), relabelWL (π, p)), (a, b))
      = ((designOutRaw (((ks, xs), p), (a, b))).1,
          (permList π (designOutRaw (((ks, xs), p), (a, b))).2.1,
            (designOutRaw (((ks, xs), p), (a, b))).2.2)) := by
  rw [designOutRaw, designOutRaw, restrVColors_relabel hπ hp hxs,
    dominantList_relabel hπ hp hxs, cliqueRank_relabel hπ hp hxs]

end Reads

/-! ## The scan, and the whole procedure

The loop of lines 02–03 enumerates the strings with the same fold that builds the table of
`k`-tuples, and that fold is order-preserving (`Algo.tuplesOf_permList`), so the enumeration over
the relabeled vertex list is the relabeled enumeration, entry by entry.  Since the test at a
string is invariant (`Algo.returnsB_relabel`), the first string that fires is the relabeled first
string that fires. -/

section Scan

variable {n k a b c₀ : ℕ} {π : RawPerm} {ks xs xs' dom : List ℕ} {p : RawWL}
  {rels : RawRelStruct}

/-- **Line 03 is canonical**: the loop over the strings of one length returns the relabeled
string. -/
theorem scanLen_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) (l : ℕ) :
    scanLen l (((ks, xs'), relabelWL (π, p)), (a, b))
      = (scanLen l (((ks, xs), p), (a, b))).map (permList π) := by
  have hkey : ∀ t ∈ tuplesOf p.1 l, ∀ c ∈ t, c < n := by
    intro t ht c hc
    exact (hp.domMem c).1 (((mem_tuplesOf p.1 l t).1 ht).2 c hc)
  show (((tuplesOf (permList π p.1) l).filter
      (fun t => returnsB (withStr ((((ks, xs'), relabelWL (π, p)), (a, b)), t)))).head?)
    = (((tuplesOf p.1 l).filter
      (fun t => returnsB (withStr ((((ks, xs), p), (a, b)), t)))).head?).map (permList π)
  rw [tuplesOf_permList, filter_map_comm, List.head?_map]
  refine congrArg (Option.map (permList π)) (congrArg List.head?
    (List.filter_congr (fun t ht => ?_)))
  show returnsB (((ks, permList π t), relabelWL (π, p)), (a, b))
    = returnsB (((ks, t), p), (a, b))
  exact returnsB_relabel hπ hp (hkey t ht)

/-- **Line 02 is canonical**: the answer after `j` rounds is the relabeled answer. -/
theorem ansUpTo_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) (x₀ x₁ : List ℕ) :
    ∀ j : ℕ, ansUpTo (((ks, x₁), relabelWL (π, p)), (a, b)) j
      = (ansUpTo (((ks, x₀), p), (a, b)) j).map (permList π) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [ansUpTo, ansUpTo, ih]
      cases h : ansUpTo (((ks, x₀), p), (a, b)) j with
      | none => simpa using scanLen_relabel (xs := x₀) (xs' := x₁) hπ hp j
      | some ys => simp

theorem scanRounds_relabel (c₀ : ℕ) :
    scanRounds c₀ (((ks, xs'), relabelWL (π, p)), (a, b))
      = scanRounds c₀ (((ks, xs), p), (a, b)) := by
  show (if ks.length ≤ guardBound c₀ (permList π p.1).length then ks.length else 0)
    = (if ks.length ≤ guardBound c₀ p.1.length then ks.length else 0)
  rw [length_permList]

/-- **Lines 02–08 are canonical.** -/
theorem rawDesignScan_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) (c₀ : ℕ) :
    rawDesignScan c₀ (((ks, xs'), relabelWL (π, p)), (a, b))
      = (rawDesignScan c₀ (((ks, xs), p), (a, b))).map (permList π) := by
  rw [rawDesignScan_eq, rawDesignScan_eq,
    scanRounds_relabel (xs := xs) (xs' := xs') c₀]
  exact ansUpTo_relabel hπ hp xs xs' _

/-- Every string the scan can return is a string of vertices. -/
theorem rawDesignScan_lt (hp : RawWL.WF n k p) {ys : List ℕ}
    (hs : rawDesignScan c₀ (((ks, xs), p), (a, b)) = some ys) : ∀ c ∈ ys, c < n := by
  rw [rawDesignScan_eq] at hs
  obtain ⟨l, -, hmem⟩ := ansUpTo_mem hs
  intro c hc
  exact (hp.domMem c).1 (((mem_tuplesOf _ _ _).1 hmem).2 c hc)

/-- **Procedure "Design Lemma" is canonical**: relabeling the input structure by `π` relabels the
string the procedure returns. -/
theorem designProcedure_relabel (hπ : RawPerm.WF n π) (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) (hg : ks.length ≤ guardBound c₀ dom.length)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    designProcedure c₀ (((ks, permList π dom), relabelRels (π, rels)), (a, b))
      = (designProcedure c₀ (((ks, dom), rels), (a, b))).map (permList π) := by
  have hwf : RawWL.WF n ks.length (guardedPipeline321 c₀ ((ks, dom), rels)) :=
    guardedPipeline321_wf (a := ((ks, dom), rels)) hnd hmem hg
  show rawDesignScan c₀ (((ks, []),
      guardedPipeline321 c₀ ((ks, permList π dom), relabelRels (π, rels))), (a, b)) = _
  rw [guardedPipeline321_relabel hπ hnd hmem hg hrels]
  exact rawDesignScan_relabel (xs := []) (xs' := []) hπ hwf c₀

/-- **The outcome of Procedure "Design Lemma" is canonical.**  Relabeling the input structure by
`π` leaves the vertex coloring of line 05 unchanged as a list, carries the dominant class of
line 06 over by `π`, and leaves the rank of line 07 unchanged.  This is Theorem 8.1.2's
*"Canonicity in the above statements is relative to `x⃗`"*, end to end. -/
theorem designOutcome_relabel (hπ : RawPerm.WF n π) (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) (hg : ks.length ≤ guardBound c₀ dom.length)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    designOutcome c₀ (((ks, permList π dom), relabelRels (π, rels)), (a, b))
      = (designOutcome c₀ (((ks, dom), rels), (a, b))).map
          (fun w => (w.1, (permList π w.2.1, w.2.2))) := by
  have hwf : RawWL.WF n ks.length (guardedPipeline321 c₀ ((ks, dom), rels)) :=
    guardedPipeline321_wf (a := ((ks, dom), rels)) hnd hmem hg
  have hpr := designProcedure_relabel (a := a) (b := b) (π := π) hπ hnd hmem hg hrels
  have htab : guardedPipeline321 c₀ ((ks, permList π dom), relabelRels (π, rels))
      = relabelWL (π, guardedPipeline321 c₀ ((ks, dom), rels)) :=
    guardedPipeline321_relabel hπ hnd hmem hg hrels
  cases hs : designProcedure c₀ (((ks, dom), rels), (a, b)) with
  | none =>
      rw [hs] at hpr
      rw [designOutcome_of_none hpr, designOutcome_of_none hs]
      rfl
  | some ys =>
      have hys : ∀ c ∈ ys, c < n := rawDesignScan_lt (xs := []) hwf hs
      rw [hs] at hpr
      rw [designOutcome_of_some hpr, designOutcome_of_some hs]
      show some (designOutRaw (((ks, permList π ys),
        guardedPipeline321 c₀ ((ks, permList π dom), relabelRels (π, rels))), (a, b))) = _
      rw [htab, designOutRaw_relabel hπ hwf hys]
      rfl

end Scan

end Algo
