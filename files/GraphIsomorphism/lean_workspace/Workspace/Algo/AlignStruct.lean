/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 1 — the isomorphism test for the
canonical structures, in the colored-partition case, on the unit-cost RAM.
-/
import Workspace.Algo.BlockSystem
import Workspace.Canonical.Align
import Workspace.ColoredPartitions.Basic

/-!
# §14.1, Procedure Align, line 1: the structure isomorphism test

> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit.

and (§14.1, line 5705)

> A common feature of the categories of these types of structures is that their
> `G^ϕ`-isomorphisms are easy to find.  (This is trivial in linear time for colored
> equipartitions, and polynomial time for Johnson schemes.)

This file does the **colored-partition** half on raw data.

## The raw encoding

A colored partition of `Γ = [0, m)` (Def. 7.1.1: a coloring of `Γ` together with a partition
of each color class) is two labellings of `Γ` in the sense of `Workspace/Algo/BlockSystem.lean`
(`Algo.RawLab`): the color labelling and the block labelling.  The *cell* of a point is the
pair of its two labels (`Algo.cellOf`), so the blocks are automatically inside the color
classes and the decoding `Algo.decColPartition` is total, as every routine of the algorithmic
layer must be.

## The invariant

A cell is monochromatic, so the *profile* of a cell — the multiset of colors of its points —
is the pair `(color, size)`.  Two colored partitions of `[0, m)` are therefore isomorphic
exactly when the multisets of the pairs `(color of the cell, size of the cell)` agree, and
this file computes that multiset point by point (`Algo.colPartStat`) and compares the two
multisets by counting (`Algo.cpStatEq`).  This is the "equal color-class and block-size
statistics" of the paper's "trivial in linear time".

## Main definitions

* `Algo.RawColPart`, `Algo.cellOf`, `Algo.RawColPart.WF` — the raw encoding;
* `Algo.decColPartition`, `Algo.decColStruct` — the decodings, into
  `Babai.ColoredPartition (Fin m) ℕ` (Def. 7.1.1) and into `Babai.ColStruct (Fin m) ℕ`
  (the `S(Γ)`-set Procedure Align acts on);
* `Algo.ColPartIso` — the paper's isomorphism of colored partitions, worded as in the
  category `Babai.ColoredPartitions` (§7.1);
* `Algo.colPartStat`, `Algo.cpStatEq`, `Algo.alignColPartTest` — the test of line 1;
* `Algo.rawColPartIsoCheck` — the verification of a candidate isomorphism.

## Main results

* `Algo.colPartIso_iff_coloredPartition` — `Algo.ColPartIso` is membership in the morphism
  set of the category `Babai.ColoredPartitions` (§7.1);
* `Algo.colPartIso_iff_smul` — and it is the action of `S(Γ)` on `Babai.ColStruct`, so
  `Babai.structIso` is what the test decides;
* `Algo.colPartStat_perm` — **the statistic is an isomorphism invariant**;
* `Algo.alignColPartTest_eq_false_structIso` — a failed test means there is no isomorphism at
  all, in particular none in `G^ϕ`;
* `Algo.Align_line1_reject_colPart` — **Procedure Align, line 1**: a failed test justifies the
  reject exit, `Iso_G(x, y) = ∅`;
* `Algo.rawColPartIsoCheck_iff` — the verification is correct both ways;
* `Algo.polyFun_colPartStat`, `Algo.polyFun_alignColPartTest`,
  `Algo.polyFun_rawColPartIsoCheck` — **the running time**: line 1 is a `RAM.PolyFun` in the
  colored-partition case.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Raw colored partitions -/

/-- §14.1, line 4 and Def. 7.1.1.  A **colored partition of `Γ = [0, m)` on raw data**: the
color labelling and the block labelling of the points, in the sense of `Algo.RawLab`. -/
abbrev RawColPart := RawLab × RawLab

/-- The **cell** of a point: the pair (its color, its block label).  Using the pair rather
than the block label alone makes the blocks lie inside the color classes for *every* pair of
labellings, which is what Def. 7.1.1 asks and what makes `Algo.decColPartition` total. -/
def cellOf (P : RawColPart) (u : ℕ) : ℕ × ℕ := (labAt P.1 u, labAt P.2 u)

/-- A raw colored partition is **well formed** for the degree `m` when both labellings list
one entry per point. -/
def RawColPart.WF (m : ℕ) (P : RawColPart) : Prop := P.1.length = m ∧ P.2.length = m

theorem cellOf_fst (P : RawColPart) (u : ℕ) : (cellOf P u).1 = labAt P.1 u := rfl

/-! ## The decodings -/

/-- Def. 7.1.1.  The colored partition of `Fin m` that a raw colored partition describes:
the color of a point is its color label, and two points are in one block when their cells
agree. -/
def decColPartition (m : ℕ) (P : RawColPart) : Babai.ColoredPartition (Fin m) ℕ where
  color u := labAt P.1 (u : ℕ)
  part := ⟨fun u v => cellOf P (u : ℕ) = cellOf P (v : ℕ), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  part_le_color := fun h => congrArg Prod.fst h

/-- §14.  The structure on `Γ` that a raw colored partition describes, as an element of the
`S(Γ)`-set `Babai.ColStruct` Procedure Align acts on: the vertex coloring is the color
labelling, and the pair coloring is `0` on a pair inside one block and `1` otherwise — the
equivalence relation of line 7 (A). -/
def decColStruct (m : ℕ) (P : RawColPart) : Babai.ColStruct (Fin m) ℕ where
  vcol u := labAt P.1 (u : ℕ)
  ecol u v := if cellOf P (u : ℕ) = cellOf P (v : ℕ) then 0 else 1

@[simp] theorem decColStruct_vcol (m : ℕ) (P : RawColPart) (u : Fin m) :
    (decColStruct m P).vcol u = labAt P.1 (u : ℕ) := rfl

@[simp] theorem decColStruct_ecol (m : ℕ) (P : RawColPart) (u v : Fin m) :
    (decColStruct m P).ecol u v = if cellOf P (u : ℕ) = cellOf P (v : ℕ) then 0 else 1 := rfl

/-! ## The isomorphism notion -/

/-- §7.1, the category `Babai.ColoredPartitions`: *"the morphisms are the bijections that
preserve color and preserve the given equivalence relation (partition) in each color
class."*  Written for two raw colored partitions of `[0, m)`. -/
def ColPartIso (m : ℕ) (P Q : RawColPart) (f : Perm (Fin m)) : Prop :=
  (∀ u : Fin m, labAt Q.1 ((f u : Fin m) : ℕ) = labAt P.1 (u : ℕ)) ∧
    (∀ u v : Fin m, cellOf P (u : ℕ) = cellOf P (v : ℕ) ↔
      cellOf Q ((f u : Fin m) : ℕ) = cellOf Q ((f v : Fin m) : ℕ))

/-- `Algo.ColPartIso` **is** the morphism condition of the category `Babai.ColoredPartitions`
(§7.1) for the decoded colored partitions. -/
theorem colPartIso_iff_coloredPartition (m : ℕ) (P Q : RawColPart) (f : Perm (Fin m)) :
    ColPartIso m P Q f ↔
      ((∀ u, (decColPartition m Q).color (f u) = (decColPartition m P).color u) ∧
        ∀ u v, (decColPartition m P).part u v ↔ (decColPartition m Q).part (f u) (f v)) :=
  Iff.rfl

/-- `Algo.ColPartIso` is the action of `S(Γ)` on `Babai.ColStruct`, so the set of
isomorphisms the test decides is `Babai.structIso`.

(Lean's `α • X` reads the structure at `α⁻¹ γ`, so `α • X = Y` says `Y` at `α u` is `X` at
`u`, which is the direction the paper's `X(x)^{σ̄} = X(y)` has.) -/
theorem colPartIso_iff_smul (m : ℕ) (P Q : RawColPart) (f : Perm (Fin m)) :
    ColPartIso m P Q f ↔ f • decColStruct m P = decColStruct m Q := by
  constructor
  · rintro ⟨hc, hp⟩
    ext u v
    · show labAt P.1 ((f⁻¹ u : Fin m) : ℕ) = labAt Q.1 (u : ℕ)
      have h0 := hc (f⁻¹ u)
      rw [show f (f⁻¹ u) = u from by simp] at h0
      exact h0.symm
    · show (if cellOf P ((f⁻¹ u : Fin m) : ℕ) = cellOf P ((f⁻¹ v : Fin m) : ℕ) then 0 else 1)
        = if cellOf Q (u : ℕ) = cellOf Q (v : ℕ) then 0 else 1
      have h := hp (f⁻¹ u) (f⁻¹ v)
      rw [show f (f⁻¹ u) = u from by simp, show f (f⁻¹ v) = v from by simp] at h
      exact if_congr h rfl rfl
  · intro h
    refine ⟨fun u => ?_, fun u v => ?_⟩
    · have h0 := congrArg (fun Y : Babai.ColStruct (Fin m) ℕ => Y.vcol (f u)) h
      exact (by simpa using h0 : labAt P.1 (u : ℕ) = labAt Q.1 ((f u : Fin m) : ℕ)).symm
    · have := congrArg (fun Y : Babai.ColStruct (Fin m) ℕ => Y.ecol (f u) (f v)) h
      simp only [Babai.ColStruct.smul_ecol, decColStruct_ecol,
        show f⁻¹ (f u) = u from by simp, show f⁻¹ (f v) = v from by simp] at this
      by_cases h1 : cellOf P (u : ℕ) = cellOf P (v : ℕ) <;>
        by_cases h2 : cellOf Q ((f u : Fin m) : ℕ) = cellOf Q ((f v : Fin m) : ℕ) <;>
        simp [h1, h2] at this ⊢

/-! ## The statistic

A cell is monochromatic, so the profile of a cell — the multiset of the colors of its points —
is the pair `(color, size)`.  The statistic of a colored partition is therefore the multiset
over the *points* of `(color of the point, size of its cell)`: a cell of profile `(k, s)`
contributes `s` copies of `(k, s)`, so the multiset over the points and the multiset over the
cells determine each other. -/

/-- The points of the domain of a raw colored partition. -/
def cpDom (P : RawColPart) : List ℕ := List.range P.1.length

/-- The number of points in the cell of a point. -/
def cellSize (p : RawColPart × ℕ) : ℕ :=
  ((cpDom p.1).filter (fun v => decide (cellOf p.1 v = cellOf p.1 p.2))).length

/-- The **key** of a point: the color of its cell and the size of its cell. -/
def cpKey (p : RawColPart × ℕ) : ℕ × ℕ := (labAt p.1.1 p.2, cellSize p)

/-- §14.1, line 1.  **The statistic of a colored partition**: the list of the keys of its
points.  Two colored partitions of `[0, m)` are isomorphic exactly when these two lists are
equal as multisets; `Algo.colPartStat_perm` is the half this file proves and uses. -/
def colPartStat (P : RawColPart) : List (ℕ × ℕ) := (cpDom P).map (fun u => cpKey (P, u))

/-! ### The statistic is an isomorphism invariant -/

/-- Filtering commutes with mapping, in the direction this file needs. -/
theorem cpFilterMapComm {α β : Type*} (g : α → β) (q : β → Bool) : ∀ l : List α,
    (l.map g).filter q = (l.filter (fun a => q (g a))).map g
  | [] => rfl
  | a :: l => by by_cases h : q (g a) <;> simp [h, cpFilterMapComm g q l]

/-- A permutation of `Fin m` as a map of the point labels, extended by the identity. -/
def cpAct (m : ℕ) (f : Perm (Fin m)) (u : ℕ) : ℕ :=
  if h : u < m then ((f ⟨u, h⟩ : Fin m) : ℕ) else u

theorem cpAct_of_lt {m : ℕ} (f : Perm (Fin m)) {u : ℕ} (h : u < m) :
    cpAct m f u = ((f ⟨u, h⟩ : Fin m) : ℕ) := dif_pos h

theorem cpAct_lt {m : ℕ} (f : Perm (Fin m)) {u : ℕ} (h : u < m) : cpAct m f u < m := by
  rw [cpAct_of_lt f h]; exact (f ⟨u, h⟩).isLt

theorem cpAct_injOn {m : ℕ} (f : Perm (Fin m)) {u v : ℕ} (hu : u < m) (hv : v < m)
    (h : cpAct m f u = cpAct m f v) : u = v := by
  rw [cpAct_of_lt f hu, cpAct_of_lt f hv] at h
  have := f.injective (Fin.ext h)
  exact congrArg Fin.val this

/-- The domain is permuted, so the list of the images of the points is a rearrangement of the
list of the points. -/
theorem cpAct_perm_range {m : ℕ} (f : Perm (Fin m)) :
    ((List.range m).map (cpAct m f)).Perm (List.range m) := by
  have hnd : ((List.range m).map (cpAct m f)).Nodup := by
    refine (List.nodup_range).map_on ?_
    intro u hu v hv h
    exact cpAct_injOn f (List.mem_range.1 hu) (List.mem_range.1 hv) h
  refine List.perm_of_nodup_nodup_toFinset_eq hnd (List.nodup_range) ?_
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro a ha
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at ha ⊢
    obtain ⟨u, hu, rfl⟩ := ha
    exact cpAct_lt f hu
  · rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup (List.nodup_range)]
    simp

/-- **The key of a point is an isomorphism invariant.** -/
theorem cpKey_cpAct {m : ℕ} {P Q : RawColPart} (hP : P.1.length = m) (hQ : Q.1.length = m)
    {f : Perm (Fin m)} (h : ColPartIso m P Q f) {u : ℕ} (hu : u < m) :
    cpKey (Q, cpAct m f u) = cpKey (P, u) := by
  have hcp : cpAct m f u = ((f ⟨u, hu⟩ : Fin m) : ℕ) := cpAct_of_lt f hu
  refine Prod.ext ?_ ?_
  · show labAt Q.1 (cpAct m f u) = labAt P.1 u
    rw [hcp]; exact h.1 ⟨u, hu⟩
  · show cellSize (Q, cpAct m f u) = cellSize (P, u)
    have hdQ : cpDom Q = List.range m := by rw [cpDom, hQ]
    have hdP : cpDom P = List.range m := by rw [cpDom, hP]
    set q : ℕ → Bool := fun v => decide (cellOf Q v = cellOf Q (cpAct m f u)) with hq
    have h1 : ((List.range m).filter q).length
        = (((List.range m).map (cpAct m f)).filter q).length :=
      ((cpAct_perm_range f).filter q).length_eq.symm
    have h2 : (((List.range m).map (cpAct m f)).filter q).length
        = ((List.range m).filter (fun v => q (cpAct m f v))).length := by
      rw [cpFilterMapComm, List.length_map]
    have h3 : (List.range m).filter (fun v => q (cpAct m f v))
        = (List.range m).filter (fun v => decide (cellOf P v = cellOf P u)) := by
      refine List.filter_congr ?_
      intro v hv
      have hvm : v < m := List.mem_range.1 hv
      have := h.2 ⟨v, hvm⟩ ⟨u, hu⟩
      rw [show ((⟨v, hvm⟩ : Fin m) : ℕ) = v from rfl, show ((⟨u, hu⟩ : Fin m) : ℕ) = u from rfl]
        at this
      simp only [hq, hcp, cpAct_of_lt f hvm, decide_eq_decide]
      exact this.symm
    show ((cpDom Q).filter q).length = _
    rw [hdQ, h1, h2, h3]
    show _ = ((cpDom P).filter (fun v => decide (cellOf P v = cellOf P u))).length
    rw [hdP]

/-- §14.1, line 1.  **The statistic is an isomorphism invariant**: isomorphic colored
partitions of `[0, m)` have the same multiset of keys.  This is the half of the test the
reject exit needs. -/
theorem colPartStat_perm {m : ℕ} {P Q : RawColPart} (hP : P.1.length = m) (hQ : Q.1.length = m)
    {f : Perm (Fin m)} (h : ColPartIso m P Q f) :
    (colPartStat P).Perm (colPartStat Q) := by
  have h1 : colPartStat P = (List.range m).map (fun u => cpKey (Q, cpAct m f u)) := by
    rw [colPartStat, cpDom, hP]
    refine List.map_congr_left ?_
    intro u hu
    exact (cpKey_cpAct hP hQ h (List.mem_range.1 hu)).symm
  have h2 : ((List.range m).map (cpAct m f)).map (fun w => cpKey (Q, w))
      = (List.range m).map (fun u => cpKey (Q, cpAct m f u)) := List.map_map
  have h3 : colPartStat Q = (List.range m).map (fun w => cpKey (Q, w)) := by
    rw [colPartStat, cpDom, hQ]
  rw [h1, h3, ← h2]
  exact (cpAct_perm_range f).map _

/-! ## Comparing the two statistics

Two lists are equal as multisets exactly when every key occurring in either occurs the same
number of times in both, so the comparison is a count and needs no sorting. -/

/-- The number of occurrences of a key in a statistic. -/
def cpCount (p : List (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  (p.1.filter (fun a => decide (a = p.2))).length

theorem cpCount_eq_count (L : List (ℕ × ℕ)) (a : ℕ × ℕ) : cpCount (L, a) = L.count a := by
  rw [cpCount, List.count_eq_countP, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr ?_
  intro b _
  by_cases hb : b = a <;> simp [hb]

/-- The keys on which the two statistics disagree. -/
def cpBadKeys (p : List (ℕ × ℕ) × List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (p.1 ++ p.2).filter (fun a => decide (cpCount (p.1, a) ≠ cpCount (p.2, a)))

/-- **The two statistics are equal as multisets.** -/
def cpStatEq (p : List (ℕ × ℕ) × List (ℕ × ℕ)) : Bool := (cpBadKeys p).isEmpty

theorem cpStatEq_iff (L L' : List (ℕ × ℕ)) : cpStatEq (L, L') = true ↔ L.Perm L' := by
  rw [cpStatEq, List.isEmpty_iff]
  constructor
  · intro h
    rw [List.perm_iff_count]
    intro a
    by_cases ha : a ∈ L ++ L'
    · by_contra hne
      have hmem : a ∈ cpBadKeys (L, L') := by
        refine List.mem_filter.2 ⟨ha, ?_⟩
        simp only [decide_eq_true_eq, cpCount_eq_count]
        exact hne
      rw [h] at hmem
      exact absurd hmem (List.not_mem_nil)
    · have h1 : L.count a = 0 :=
        List.count_eq_zero.2 (fun hm => ha (List.mem_append_left _ hm))
      have h2 : L'.count a = 0 :=
        List.count_eq_zero.2 (fun hm => ha (List.mem_append_right _ hm))
      rw [h1, h2]
  · intro h
    rw [cpBadKeys, List.filter_eq_nil_iff]
    intro a _
    simp only [decide_eq_true_eq, cpCount_eq_count, not_not]
    exact h.count_eq a

/-- §14.1, **Procedure Align, line 1**, in the colored-partition case: the two structures are
tested by their statistics.  *"This is trivial in linear time for colored equipartitions."* -/
def alignColPartTest (p : RawColPart × RawColPart) : Bool :=
  cpStatEq (colPartStat p.1, colPartStat p.2)

/-- **A failed test means there is no isomorphism at all**, in particular none in `G^ϕ`. -/
theorem alignColPartTest_eq_false_structIso {m : ℕ} {P Q : RawColPart}
    (hP : P.1.length = m) (hQ : Q.1.length = m) (h : alignColPartTest (P, Q) = false)
    (K : Set (Perm (Fin m))) :
    Babai.structIso K (decColStruct m P) (decColStruct m Q) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨-, hf⟩
  have hiso : ColPartIso m P Q f := (colPartIso_iff_smul m P Q f).2 hf
  have htrue : cpStatEq (colPartStat P, colPartStat Q) = true :=
    (cpStatEq_iff _ _).2 (colPartStat_perm hP hQ hiso)
  rw [alignColPartTest, htrue] at h
  exact Bool.noConfusion h

/-- §14.1, **Procedure Align, line 1**: *"If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then
reject isomorphism, exit."*

When the canonical structures of the two input strings are colored partitions of `Γ = [0, m)`
and the statistics differ, the reject exit is correct: `Iso_G(x, y) = ∅`.  The mathematical
step is `Babai.Align_reject_struct`; what this file adds is that the test is decided by a
`RAM.PolyFun` (`Algo.polyFun_alignColPartTest`). -/
theorem Align_line1_reject_colPart {Ω : Type*} {A : Type*} {m : ℕ}
    {G : Subgroup (Perm Ω)} {ϕ : G →* Perm (Fin m)}
    {X : (Ω → A) → Babai.ColStruct (Fin m) ℕ}
    (hcan : Babai.IsCanonicalStructure ϕ X) (x y : Ω → A) {P Q : RawColPart}
    (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hXx : X x = decColStruct m P) (hXy : X y = decColStruct m Q)
    (h : alignColPartTest (P, Q) = false) :
    Babai.strIso (G : Set (Perm Ω)) x y = ∅ := by
  refine Babai.Align_reject_struct hcan x y ?_
  rw [hXx, hXy]
  exact alignColPartTest_eq_false_structIso hP hQ h _

/-! ## The running time

Line 2 of Procedure Align is *"executed in polynomial (in `m`) time"* (§14.2).  In the
colored-partition case the test is a `RAM.PolyFun`. -/

theorem polyFun_labAtPair : PolyFun (fun p : RawLab × ℕ => labAt p.1 p.2) :=
  (polyFun_id.pair (polyFun_const 0)).comp polyFun_getD

theorem polyFun_cellOfPair : PolyFun (fun p : RawColPart × ℕ => cellOf p.1 p.2) := by
  have h1 : PolyFun (fun p : RawColPart × ℕ => labAt p.1.1 p.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_labAtPair
  have h2 : PolyFun (fun p : RawColPart × ℕ => labAt p.1.2 p.2) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_labAtPair
  exact h1.pair h2

theorem polyFun_pairNatEq : PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1 = p.2)) := by
  have h1 : PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.1 = p.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_natEq
  have h2 : PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.2 = p.2.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_natEq
  refine (PolyFun.ite h1 h2 (polyFun_const false)).of_eq (fun p => ?_)
  by_cases hh : p.1.1 = p.2.1 <;> simp [hh, Prod.ext_iff]

theorem polyFun_natNe : PolyFun (fun p : ℕ × ℕ => decide (p.1 ≠ p.2)) := by
  refine (PolyFun.ite polyFun_natEq (polyFun_const false) (polyFun_const true)).of_eq
    (fun p => ?_)
  by_cases hh : p.1 = p.2 <;> simp [hh]

theorem polyFun_cpDom : PolyFun cpDom := polyFun_fst.comp polyFun_rangeLength

theorem polyFun_cellSize : PolyFun cellSize := by
  have ha : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cellOfPair
  have hb : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.1.2) :=
    polyFun_fst.comp polyFun_cellOfPair
  have hq : PolyFun (fun z : (RawColPart × ℕ) × ℕ =>
      decide (cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2)) := (ha.pair hb).comp polyFun_pairNatEq
  have hf := PolyFun.filterParam hq
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp hf).comp polyFun_length

theorem polyFun_cpKey : PolyFun cpKey := by
  have h1 : PolyFun (fun p : RawColPart × ℕ => labAt p.1.1 p.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_labAtPair
  exact h1.pair polyFun_cellSize

theorem polyFun_colPartStat : PolyFun colPartStat :=
  (polyFun_id.pair polyFun_cpDom).comp (PolyFun.mapParam polyFun_cpKey)

theorem polyFun_cpCount : PolyFun cpCount := by
  have hq : PolyFun (fun z : (ℕ × ℕ) × (ℕ × ℕ) => decide (z.2 = z.1)) :=
    polyFun_swap.comp polyFun_pairNatEq
  exact ((polyFun_swap.comp (PolyFun.filterParam hq)).comp polyFun_length)

theorem polyFun_cpBadKeys : PolyFun cpBadKeys := by
  have h1 : PolyFun (fun z : (List (ℕ × ℕ) × List (ℕ × ℕ)) × (ℕ × ℕ) =>
      cpCount (z.1.1, z.2)) := ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
        polyFun_cpCount
  have h2 : PolyFun (fun z : (List (ℕ × ℕ) × List (ℕ × ℕ)) × (ℕ × ℕ) =>
      cpCount (z.1.2, z.2)) := ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp
        polyFun_cpCount
  have hq : PolyFun (fun z : (List (ℕ × ℕ) × List (ℕ × ℕ)) × (ℕ × ℕ) =>
      decide (cpCount (z.1.1, z.2) ≠ cpCount (z.1.2, z.2))) := (h1.pair h2).comp polyFun_natNe
  exact (polyFun_id.pair polyFun_append).comp (PolyFun.filterParam hq)

theorem polyFun_cpStatEq : PolyFun cpStatEq := polyFun_cpBadKeys.comp polyFun_isEmpty

/-- §14.1, line 1 in the colored-partition case **runs in polynomial time**. -/
theorem polyFun_alignColPartTest : PolyFun alignColPartTest :=
  ((polyFun_fst.comp polyFun_colPartStat).pair
    (polyFun_snd.comp polyFun_colPartStat)).comp polyFun_cpStatEq

/-! ## Verifying a candidate isomorphism

Line 2 (i) picks a `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`.  Whatever produces the candidate, *checking*
it is a direct reading of the definition, and unlike `Algo.alignColPartTest` the check is
correct in both directions. -/

/-- A raw permutation of `Γ` is a list, so the image of a point is `Algo.labAt` again. -/
theorem labAt_eq_decPerm {m : ℕ} {σ : RawPerm} (h : RawPerm.WF m σ) {u : ℕ} (hu : u < m) :
    labAt σ u = ((decPerm m σ ⟨u, hu⟩ : Fin m) : ℕ) := by
  have hlen : u < σ.length := by rw [h.length]; exact hu
  rw [labAt, List.getD_eq_getElem _ _ hlen, decPerm_val_of_wf h ⟨u, hu⟩]

/-- The ordered pairs of points of a domain list. -/
def cpPairs (dom : List ℕ) : List (ℕ × ℕ) := dom.flatMap (fun u => dom.map (fun v => (u, v)))

theorem mem_cpPairs {dom : List ℕ} {q : ℕ × ℕ} :
    q ∈ cpPairs dom ↔ q.1 ∈ dom ∧ q.2 ∈ dom := by
  rw [cpPairs, List.mem_flatMap]
  constructor
  · rintro ⟨u, hu, hq⟩
    rw [List.mem_map] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    exact ⟨hu, hv⟩
  · rintro ⟨h1, h2⟩
    exact ⟨q.1, h1, List.mem_map.2 ⟨q.2, h2, rfl⟩⟩

/-- Two booleans differ. -/
def boolNe (p : Bool × Bool) : Bool := if p.1 then !p.2 else p.2

theorem boolNe_eq_false_iff (a b : Bool) : boolNe (a, b) = false ↔ a = b := by
  cases a <;> cases b <;> simp [boolNe]

/-- The points at which a candidate fails to preserve the color. -/
def cpBadColor (p : (RawColPart × RawColPart) × RawPerm) : List ℕ :=
  (cpDom p.1.1).filter (fun u => decide (labAt p.1.2.1 (labAt p.2 u) ≠ labAt p.1.1.1 u))

/-- The pairs of points at which a candidate fails to preserve the partition. -/
def cpBadPair (p : (RawColPart × RawColPart) × RawPerm) : List (ℕ × ℕ) :=
  (cpPairs (cpDom p.1.1)).filter (fun q =>
    boolNe (decide (cellOf p.1.1 q.1 = cellOf p.1.1 q.2),
      decide (cellOf p.1.2 (labAt p.2 q.1) = cellOf p.1.2 (labAt p.2 q.2))))

/-- §14.1, line 1: **the check that a candidate permutation of `Γ` is an isomorphism** of the
two colored partitions, in the words of the category `Babai.ColoredPartitions` (§7.1): it
preserves the color, and it preserves the partition. -/
def rawColPartIsoCheck (p : (RawColPart × RawColPart) × RawPerm) : Bool :=
  if (cpBadColor p).isEmpty then (cpBadPair p).isEmpty else false

/-- **The check is correct, both ways.** -/
theorem rawColPartIsoCheck_iff {m : ℕ} {P Q : RawColPart} (hP : P.1.length = m)
    {σ : RawPerm} (hσ : RawPerm.WF m σ) :
    rawColPartIsoCheck ((P, Q), σ) = true ↔ ColPartIso m P Q (decPerm m σ) := by
  have hdom : cpDom P = List.range m := by rw [cpDom, hP]
  have hcol : (cpBadColor ((P, Q), σ)).isEmpty = true ↔
      ∀ u : Fin m, labAt Q.1 ((decPerm m σ u : Fin m) : ℕ) = labAt P.1 (u : ℕ) := by
    rw [List.isEmpty_iff, cpBadColor]
    show ((cpDom P).filter _ = []) ↔ _
    rw [hdom, List.filter_eq_nil_iff]
    constructor
    · intro h u
      have := h (u : ℕ) (List.mem_range.2 u.isLt)
      simp only [decide_eq_true_eq, not_not] at this
      rw [← labAt_eq_decPerm hσ u.isLt]
      exact this
    · intro h u hu
      simp only [decide_eq_true_eq, not_not]
      have := h ⟨u, List.mem_range.1 hu⟩
      rwa [← labAt_eq_decPerm hσ (List.mem_range.1 hu)] at this
  have hpair : (cpBadPair ((P, Q), σ)).isEmpty = true ↔
      ∀ u v : Fin m, cellOf P (u : ℕ) = cellOf P (v : ℕ) ↔
        cellOf Q ((decPerm m σ u : Fin m) : ℕ) = cellOf Q ((decPerm m σ v : Fin m) : ℕ) := by
    rw [List.isEmpty_iff, cpBadPair]
    show ((cpPairs (cpDom P)).filter _ = []) ↔ _
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h u v
      have hmem : ((u : ℕ), (v : ℕ)) ∈ cpPairs (cpDom P) := by
        rw [mem_cpPairs, hdom]
        exact ⟨List.mem_range.2 u.isLt, List.mem_range.2 v.isLt⟩
      have h2 := h _ hmem
      rw [Bool.not_eq_true] at h2
      rw [boolNe_eq_false_iff] at h2
      rw [← labAt_eq_decPerm hσ u.isLt, ← labAt_eq_decPerm hσ v.isLt]
      exact decide_eq_decide.1 h2
    · intro h q hq
      rw [mem_cpPairs, hdom] at hq
      obtain ⟨h1, h2⟩ := hq
      have hu : q.1 < m := List.mem_range.1 h1
      have hv : q.2 < m := List.mem_range.1 h2
      rw [Bool.not_eq_true, boolNe_eq_false_iff]
      have := h ⟨q.1, hu⟩ ⟨q.2, hv⟩
      rw [← labAt_eq_decPerm hσ hu, ← labAt_eq_decPerm hσ hv] at this
      exact decide_eq_decide.2 this
  rw [rawColPartIsoCheck, ColPartIso]
  by_cases hc : (cpBadColor ((P, Q), σ)).isEmpty = true
  · rw [if_pos hc]
    rw [hpair]
    exact ⟨fun h => ⟨hcol.1 hc, h⟩, fun h => h.2⟩
  · rw [if_neg hc]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd (hcol.2 h.1) hc

theorem polyFun_cpPairs : PolyFun cpPairs := by
  have h1 : PolyFun (fun p : ℕ × List ℕ => p.2.map (fun v => (p.1, v))) :=
    PolyFun.mapParam polyFun_id
  have h2 : PolyFun (fun z : List ℕ × ℕ => z.1.map (fun v => (z.2, v))) :=
    polyFun_swap.comp h1
  have h3 := PolyFun.flatMapParam h2
  exact (polyFun_id.pair polyFun_id).comp h3

theorem polyFun_boolNe : PolyFun boolNe := by
  have hnot : PolyFun (fun p : Bool × Bool => !p.2) := by
    refine (PolyFun.ite polyFun_snd (polyFun_const false) (polyFun_const true)).of_eq
      (fun p => ?_)
    cases hp : p.2 <;> simp [hp]
  exact PolyFun.ite polyFun_fst hnot polyFun_snd

theorem polyFun_cpBadColor : PolyFun cpBadColor := by
  have himg : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ =>
      labAt z.1.1.2.1 (labAt z.1.2 z.2)) := by
    have ha : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ =>
        labAt z.1.2 z.2) :=
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_labAtPair
    have hb : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ => z.1.1.2.1) :=
      ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
    exact (hb.pair ha).comp polyFun_labAtPair
  have hsrc : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ =>
      labAt z.1.1.1.1 z.2) := by
    have hb : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ => z.1.1.1.1) :=
      ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
    exact (hb.pair polyFun_snd).comp polyFun_labAtPair
  have hq : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × ℕ =>
      decide (labAt z.1.1.2.1 (labAt z.1.2 z.2) ≠ labAt z.1.1.1.1 z.2)) :=
    (himg.pair hsrc).comp polyFun_natNe
  have hdom : PolyFun (fun p : (RawColPart × RawColPart) × RawPerm => cpDom p.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_cpDom
  exact (polyFun_id.pair hdom).comp (PolyFun.filterParam hq)

theorem polyFun_cpBadPair : PolyFun cpBadPair := by
  have hP : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hQ : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hs : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hu : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hiu : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      labAt z.1.2 z.2.1) := (hs.pair hu).comp polyFun_labAtPair
  have hiv : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      labAt z.1.2 z.2.2) := (hs.pair hv).comp polyFun_labAtPair
  have hc1 : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      cellOf z.1.1.1 z.2.1) := (hP.pair hu).comp polyFun_cellOfPair
  have hc2 : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      cellOf z.1.1.1 z.2.2) := (hP.pair hv).comp polyFun_cellOfPair
  have hd1 : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      cellOf z.1.1.2 (labAt z.1.2 z.2.1)) := (hQ.pair hiu).comp polyFun_cellOfPair
  have hd2 : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      cellOf z.1.1.2 (labAt z.1.2 z.2.2)) := (hQ.pair hiv).comp polyFun_cellOfPair
  have hq : PolyFun (fun z : ((RawColPart × RawColPart) × RawPerm) × (ℕ × ℕ) =>
      boolNe (decide (cellOf z.1.1.1 z.2.1 = cellOf z.1.1.1 z.2.2),
        decide (cellOf z.1.1.2 (labAt z.1.2 z.2.1) = cellOf z.1.1.2 (labAt z.1.2 z.2.2)))) :=
    (((hc1.pair hc2).comp polyFun_pairNatEq).pair
      ((hd1.pair hd2).comp polyFun_pairNatEq)).comp polyFun_boolNe
  have hdom : PolyFun (fun p : (RawColPart × RawColPart) × RawPerm =>
      cpPairs (cpDom p.1.1)) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_cpDom).comp polyFun_cpPairs
  exact (polyFun_id.pair hdom).comp (PolyFun.filterParam hq)

/-- Verifying a candidate isomorphism **runs in polynomial time**. -/
theorem polyFun_rawColPartIsoCheck : PolyFun rawColPartIsoCheck :=
  PolyFun.ite (polyFun_cpBadColor.comp polyFun_isEmpty)
    (polyFun_cpBadPair.comp polyFun_isEmpty) (polyFun_const false)

end Algo
