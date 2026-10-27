/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: line 01 of Procedure "Design Lemma" is canonical (§5.2, §8.2).
-/
import Workspace.Algo.FunctorsGuarded
import Workspace.Algo.Relabel

/-!
# §5.2 — the pipeline `F3 ∘ F2 ∘ F1` is canonical

`Workspace/Algo/Relabel.lean` (work package A8) proves that `k`-ary WL refinement commutes with
a relabeling of the vertices.  That is the last of the three functors of §5.2; this file does
the other two and the table they start from, so that line 01 of Procedure "Design Lemma" is
canonical end to end:

```
guardedPipeline321 c₀ ((ks, π(Ω)), π(R))  =  relabelWL (π, guardedPipeline321 c₀ ((ks, Ω), R))
```

The proof is one equivariance per layer, and in every case the *color names* agree, not merely
the partitions — the colors are ranks among the tags that occur (§4.1.1), the tags of the
relabeled table are the same list in the same order, and only the keys move.

* the enumeration of the `k`-tuples is order-preserving (`Algo.tuplesOf_permList`);
* `F1` reads the relations, which move with the vertices (`Algo.rawF1_relabel`);
* `F2` reads the table at the substituted strings, which move with the vertices
  (`Algo.rawF2I_relabel`).

## Main definitions

* `Algo.relabelRels` — the image of a raw relational structure under a relabeling.

## Main results

* `Algo.tuplesOf_permList`, `Algo.tupleTable_permList`, `Algo.guardedTable_permList`;
* `Algo.rawF1_relabel`, `Algo.rawF2I_relabel`;
* `Algo.guardedPipeline321_relabel` — line 01 is canonical.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## The enumeration of the tuples is order-preserving -/

theorem extendStep_permList (π : RawPerm) (dom : List ℕ) : ∀ L : List (List ℕ),
    extendStep (permList π dom, L.map (permList π)) = (extendStep (dom, L)).map (permList π)
  | [] => rfl
  | s :: L => by
      have h1 : extendStep (permList π dom, (s :: L).map (permList π))
          = (permList π dom).map (fun y => y :: permList π s)
            ++ extendStep (permList π dom, L.map (permList π)) := by
        simp [extendStep]
      have h2 : extendStep (dom, s :: L)
          = dom.map (fun y => y :: s) ++ extendStep (dom, L) := by
        simp [extendStep]
      rw [h1, h2, List.map_append, extendStep_permList π dom L]
      congr 1
      simp [permList, List.map_map, Function.comp_def]

/-- **The enumeration of the `j`-tuples is equivariant.**  The fold that builds the table of
`k`-tuples is order-preserving, so the tuples over the relabeled vertex list are the relabeled
tuples, in the order they were in. -/
theorem tuplesOf_permList (π : RawPerm) (dom : List ℕ) :
    ∀ j : ℕ, tuplesOf (permList π dom) j = (tuplesOf dom j).map (permList π)
  | 0 => rfl
  | j + 1 => by
      rw [tuplesOf_succ, tuplesOf_succ, tuplesOf_permList π dom j, extendStep_permList]

@[simp] theorem relabelWL_snd (π : RawPerm) (p : RawWL) :
    (relabelWL (π, p)).2 = p.2.map (fun q => (permList π q.1, q.2)) := rfl

/-- **The table of `k`-tuples is canonical.** -/
theorem tupleTable_permList (π : RawPerm) (dom : List ℕ) (k : ℕ) :
    tupleTable (permList π dom) k = relabelWL (π, tupleTable dom k) := by
  rw [tupleTable, tupleTable, relabelWL, tuplesOf_permList, List.map_map, List.map_map]
  rfl

/-- **The guarded table of `k`-tuples is canonical.**  The guard reads only the *length* of the
vertex list, which a relabeling does not change. -/
theorem guardedTable_permList (c₀ : ℕ) (π : RawPerm) (ks dom : List ℕ) :
    guardedTable c₀ (ks, permList π dom) = relabelWL (π, guardedTable c₀ (ks, dom)) := by
  by_cases hg : ks.length ≤ guardBound c₀ dom.length
  · have hg' : ks.length ≤ guardBound c₀ (permList π dom).length := by
      rw [length_permList]; exact hg
    rw [guardedTable_of_guard (a := (ks, permList π dom)) hg',
      guardedTable_of_guard (a := (ks, dom)) hg]
    exact tupleTable_permList π dom ks.length
  · have hg' : ¬ ks.length ≤ guardBound c₀ (permList π dom).length := by
      rw [length_permList]; exact hg
    rw [guardedTable_of_not_guard (a := (ks, permList π dom)) hg',
      guardedTable_of_not_guard (a := (ks, dom)) hg]
    rfl

/-! ## §5.1.3 — the functor `F1` is canonical

A relabeling of the vertices carries the relations of the input structure along: `Rᵢ` becomes
`π(Rᵢ)`.  The characteristic vector `c(x⃗) = {i | x⃗ ∈ Rᵢ}` is then unchanged at the relabeled
tuple, because `π` is injective on the vertices. -/

/-- **The image of a raw relational structure under a relabeling**: every tuple of every
relation is sent through `π`. -/
def relabelRels (z : RawPerm × RawRelStruct) : RawRelStruct :=
  z.2.map (fun R => R.map (permList z.1))

section F1

variable {n k : ℕ} {π : RawPerm} {p : RawWL} {rels : RawRelStruct}

theorem mem_relabel_rel (hπ : RawPerm.WF n π) {R : RawRel}
    (hR : ∀ s ∈ R, ∀ c ∈ s, c < n) {t : List ℕ} (ht : ∀ c ∈ t, c < n) :
    permList π t ∈ R.map (permList π) ↔ t ∈ R := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := List.mem_map.1 h
    rwa [permList_inj hπ (hR s hs) ht hst] at hs
  · intro h
    exact List.mem_map_of_mem h

theorem membVec_relabel (hπ : RawPerm.WF n π)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) {t : List ℕ} (ht : ∀ c ∈ t, c < n) :
    membVec (relabelRels (π, rels), permList π t) = membVec (rels, t) := by
  rw [relabelRels, membVec, membVec, List.map_map]
  refine List.map_congr_left (fun R hR => ?_)
  show (if permList π t ∈ R.map (permList π) then 1 else 0) = (if t ∈ R then 1 else 0)
  by_cases h : t ∈ R
  · rw [if_pos ((mem_relabel_rel hπ (hrels R hR) ht).2 h), if_pos h]
  · rw [if_neg (fun hc => h ((mem_relabel_rel hπ (hrels R hR) ht).1 hc)), if_neg h]

theorem key_lt (hp : RawWL.WF n k p) {q : List ℕ × ℕ} (hq : q ∈ p.2) : ∀ c ∈ q.1, c < n :=
  ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).2

theorem f1Tags_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    f1Tags (relabelWL (π, p), relabelRels (π, rels)) = f1Tags (p, rels) := by
  show ((relabelWL (π, p)).2).map (fun q => membVec (relabelRels (π, rels), q.1))
    = p.2.map (fun q => membVec (rels, q.1))
  rw [relabelWL_snd, List.map_map]
  refine List.map_congr_left (fun q hq => ?_)
  exact membVec_relabel hπ hrels (key_lt hp hq)

theorem f1TagSet_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    f1TagSet (relabelWL (π, p), relabelRels (π, rels)) = f1TagSet (p, rels) := by
  rw [f1TagSet, f1TagSet, f1Tags_relabel hπ hp hrels]

theorem f1NewCol_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) {t : List ℕ} (ht : ∀ c ∈ t, c < n) :
    f1NewCol (relabelWL (π, p), relabelRels (π, rels)) (permList π t)
      = f1NewCol (p, rels) t := by
  rw [f1NewCol, f1NewCol, f1TagSet_relabel hπ hp hrels, membVec_relabel hπ hrels ht]

/-- **§5.1.3: the functor `F1` is canonical.**  Relabeling the vertices and the relations
relabels the answer, with the same color names. -/
theorem rawF1_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    rawF1 (relabelWL (π, p), relabelRels (π, rels)) = relabelWL (π, rawF1 (p, rels)) := by
  rw [rawF1, rawF1, relabelWL, relabelWL]
  refine Prod.ext rfl ?_
  show ((relabelWL (π, p)).2).map
      (fun q => (q.1, f1NewCol (relabelWL (π, p), relabelRels (π, rels)) q.1))
    = (p.2.map (fun q => (q.1, f1NewCol (p, rels) q.1))).map
      (fun q => (permList π q.1, q.2))
  rw [relabelWL_snd, List.map_map, List.map_map]
  refine List.map_congr_left (fun q hq => ?_)
  show ((permList π q.1, f1NewCol (relabelWL (π, p), relabelRels (π, rels)) (permList π q.1))
      : List ℕ × ℕ) = (permList π q.1, f1NewCol (p, rels) q.1)
  rw [f1NewCol_relabel hπ hp hrels (key_lt hp hq)]

end F1

/-! ## §5.1.5 — the functor `F2` is canonical

`F2` reads the equality type of `x⃗` and the colors of all the substituted strings `τ(x⃗)`.  Both
are equivariant: `π` is injective on the vertices, so the equality type is unchanged, and
`τ(π x⃗) = π(τ(x⃗))`, so the relabeled table answers at the relabeled string what the table
answers.  The index sets are read off the arity and do not move. -/

section F2

variable {n k : ℕ} {π : RawPerm} {p : RawWL}

theorem getD_permList_lt (π : RawPerm) {t : List ℕ} {i : ℕ} (hi : i < t.length) :
    (permList π t).getD i 0 = rawApply (π, t.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp [permList]

theorem getD_mem {t : List ℕ} {i : ℕ} (hi : i < t.length) : t.getD i 0 ∈ t := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem rhoCodeI_permList (hπ : RawPerm.WF n π) {P : List (List ℕ)}
    (hP : ∀ s ∈ P, s.getD 0 0 < k ∧ s.getD 1 0 < k) {t : List ℕ} (hlen : t.length = k)
    (ht : ∀ c ∈ t, c < n) : rhoCodeI P (permList π t) = rhoCodeI P t := by
  rw [rhoCodeI, rhoCodeI]
  refine List.map_congr_left (fun s hs => ?_)
  obtain ⟨h0, h1⟩ := hP s hs
  have hi0 : s.getD 0 0 < t.length := by rw [hlen]; exact h0
  have hi1 : s.getD 1 0 < t.length := by rw [hlen]; exact h1
  rw [getD_permList_lt π hi0, getD_permList_lt π hi1]
  have he : rawApply (π, t.getD (s.getD 0 0) 0) = rawApply (π, t.getD (s.getD 1 0) 0)
      ↔ t.getD (s.getD 0 0) 0 = t.getD (s.getD 1 0) 0 := by
    constructor
    · exact rawApply_inj hπ (ht _ (getD_mem hi0)) (ht _ (getD_mem hi1))
    · intro h; rw [h]
  by_cases hc : t.getD (s.getD 0 0) 0 = t.getD (s.getD 1 0) 0
  · rw [if_pos (he.2 hc), if_pos hc]
  · rw [if_neg (fun hcc => hc (he.1 hcc)), if_neg hc]

theorem applyIdx_permList (π : RawPerm) {t σ : List ℕ} (hσ : ∀ i ∈ σ, i < t.length) :
    applyIdx (permList π t, σ) = permList π (applyIdx (t, σ)) := by
  show σ.map (fun i => (permList π t).getD i 0)
    = (σ.map (fun i => t.getD i 0)).map (fun a => rawApply (π, a))
  rw [List.map_map]
  refine List.map_congr_left (fun i hi => ?_)
  exact getD_permList_lt π (hσ i hi)

theorem applyIdx_lt {t σ : List ℕ} (hσ : ∀ i ∈ σ, i < t.length) (ht : ∀ c ∈ t, c < n) :
    ∀ c ∈ applyIdx (t, σ), c < n := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  exact ht _ (getD_mem (hσ i hi))

theorem pairIdx_getD_lt {s : List ℕ} (hs : s ∈ pairIdx k) :
    s.getD 0 0 < k ∧ s.getD 1 0 < k := by
  obtain ⟨hlen, hlt⟩ := mem_pairIdx.1 hs
  have h0 : (0 : ℕ) < s.length := by rw [hlen]; omega
  have h1 : (1 : ℕ) < s.length := by rw [hlen]; omega
  exact ⟨hlt _ (getD_mem h0), hlt _ (getD_mem h1)⟩

theorem f2TagAtI_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) {I : IdxP}
    (hI1 : ∀ s ∈ I.1, s.getD 0 0 < k ∧ s.getD 1 0 < k) (hI2 : ∀ σ ∈ I.2, ∀ i ∈ σ, i < k)
    {t : List ℕ} (hlen : t.length = k) (ht : ∀ c ∈ t, c < n) :
    f2TagAtI I (relabelWL (π, p)) (permList π t) = f2TagAtI I p t := by
  rw [f2TagAtI, f2TagAtI, rhoCodeI_permList hπ hI1 hlen ht]
  congr 1
  refine List.map_congr_left (fun σ hσ => ?_)
  have hσt : ∀ i ∈ σ, i < t.length := by
    intro i hi; rw [hlen]; exact hI2 σ hσ i hi
  rw [applyIdx_permList π hσt]
  exact tblGet_relabelWL hπ hp (applyIdx_lt hσt ht)

theorem f2TagsI_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) {I : IdxP}
    (hI1 : ∀ s ∈ I.1, s.getD 0 0 < k ∧ s.getD 1 0 < k) (hI2 : ∀ σ ∈ I.2, ∀ i ∈ σ, i < k) :
    f2TagsI I (relabelWL (π, p)) = f2TagsI I p := by
  rw [f2TagsI, f2TagsI, relabelWL_snd, List.map_map]
  refine List.map_congr_left (fun q hq => ?_)
  show f2TagAtI I (relabelWL (π, p)) (permList π q.1) = f2TagAtI I p q.1
  exact f2TagAtI_relabel hπ hp hI1 hI2
    ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).1 (key_lt hp hq)

/-- **§5.1.5: the functor `F2` is canonical.** -/
theorem rawF2I_relabel (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) {I : IdxP}
    (hI1 : ∀ s ∈ I.1, s.getD 0 0 < k ∧ s.getD 1 0 < k) (hI2 : ∀ σ ∈ I.2, ∀ i ∈ σ, i < k) :
    rawF2I I (relabelWL (π, p)) = relabelWL (π, rawF2I I p) := by
  have hset : f2TagSetI I (relabelWL (π, p)) = f2TagSetI I p := by
    rw [f2TagSetI, f2TagSetI, f2TagsI_relabel hπ hp hI1 hI2]
  rw [rawF2I, rawF2I, relabelWL, relabelWL]
  refine Prod.ext rfl ?_
  show ((relabelWL (π, p)).2).map
      (fun q => (q.1, f2NewColI I (relabelWL (π, p)) q.1))
    = (p.2.map (fun q => (q.1, f2NewColI I p q.1))).map (fun q => (permList π q.1, q.2))
  rw [relabelWL_snd, List.map_map, List.map_map]
  refine List.map_congr_left (fun q hq => ?_)
  show ((permList π q.1, f2NewColI I (relabelWL (π, p)) (permList π q.1)) : List ℕ × ℕ)
    = (permList π q.1, f2NewColI I p q.1)
  rw [f2NewColI, f2NewColI, hset, f2TagAtI_relabel hπ hp hI1 hI2
    ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).1 (key_lt hp hq)]

end F2

/-! ## Line 01 is canonical -/

/-- **Line 01 of Procedure "Design Lemma" is canonical.**  Relabeling the vertices of the input
structure `X = (Ω, R)` by `π` relabels the `k`-ary coherent configuration line 01 computes, with
the same color names. -/
theorem guardedPipeline321_relabel {n c₀ : ℕ} {π : RawPerm} {ks dom : List ℕ}
    {rels : RawRelStruct} (hπ : RawPerm.WF n π) (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) (hg : ks.length ≤ guardBound c₀ dom.length)
    (hrels : ∀ R ∈ rels, ∀ s ∈ R, ∀ c ∈ s, c < n) :
    guardedPipeline321 c₀ ((ks, permList π dom), relabelRels (π, rels))
      = relabelWL (π, guardedPipeline321 c₀ ((ks, dom), rels)) := by
  set k := ks.length with hk
  -- the index sets do not move: they are read off the arity and the length of the vertex list
  have hidx : guardedIdx c₀ ((ks, permList π dom), relabelRels (π, rels))
      = guardedIdx c₀ ((ks, dom), rels) := by
    have hpair : pairIdxOf ((ks, permList π dom), relabelRels (π, rels))
        = pairIdxOf ((ks, dom), rels) := rfl
    have hmon : guardedMon c₀ ((ks, permList π dom), relabelRels (π, rels))
        = guardedMon c₀ ((ks, dom), rels) := by
      rw [guardedMon, guardedMon, monSetUp, monSetUp]
      show (tabStep^[(if ks.length ≤ guardBound c₀ (permList π dom).length then
          (ks.length, (List.range ks.length, [[]])) else (0, ([], []))).1]
          (if ks.length ≤ guardBound c₀ (permList π dom).length then
          (ks.length, (List.range ks.length, [[]])) else (0, ([], []))).2).2 = _
      rw [length_permList]
    rw [guardedIdx, guardedIdx, hpair, hmon]
  have hIg : guardedIdx c₀ ((ks, dom), rels) = idxOf k :=
    guardedIdx_of_guard (a := ((ks, dom), rels)) hg
  have hI1 : ∀ s ∈ (idxOf k).1, s.getD 0 0 < k ∧ s.getD 1 0 < k :=
    fun s hs => pairIdx_getD_lt hs
  have hI2 : ∀ σ ∈ (idxOf k).2, ∀ i ∈ σ, i < k := fun σ hσ => (mem_monIdx.1 hσ).2
  -- the tables
  have hwfT : RawWL.WF n k (guardedTable c₀ (ks, dom)) := by
    rw [guardedTable_of_guard (a := (ks, dom)) hg]
    exact wf_tupleTable hnd hmem
  have hwf1 : RawWL.WF n k (rawF1 (guardedTable c₀ (ks, dom), rels)) :=
    rawF1_wf (a := (guardedTable c₀ (ks, dom), rels)) hwfT
  have hwf2 : RawWL.WF n k (rawF2I (idxOf k) (rawF1 (guardedTable c₀ (ks, dom), rels))) :=
    rawF2I_wf hwf1
  rw [guardedPipeline321, guardedPipeline321, hidx, hIg, rawPipelineI, rawPipelineI]
  show rawWLStable (rawF2I (idxOf k)
      (rawF1 (guardedTable c₀ (ks, permList π dom), relabelRels (π, rels)))) = _
  rw [guardedTable_permList c₀ π ks dom,
    rawF1_relabel (p := guardedTable c₀ (ks, dom)) hπ hwfT hrels,
    rawF2I_relabel hπ hwf1 hI1 hI2, rawWLStable_relabelWL hπ hwf2]

end Algo
