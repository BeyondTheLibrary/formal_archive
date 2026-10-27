import Workspace.Algo.SplitUpccTransport
import Workspace.Algo.AlignJohnson
import Workspace.SplitOrJohnson.BlkCases

/-!
# Section 9.8: raw input and finite scans

The table is on the points of the first part and the blocks of the second
part. A block has one name. Its underlying points stay in the caller's
dictionary. Well-formedness below checks the encoding. The UPCC hypotheses
are supplied by `Babai.UPCCObj` in the outcome specification.

The threshold is one half, as in `Babai.case_9_8`. Section 9.8 does not call
Lemma 9.3.1. It reads a local constituent of the input table directly.
-/

namespace Algo
open Babai RAM

/-- Section 9.8: a binary table and the two ordered lists of vertex names. -/
abbrev RawUpccCase := RawConfig × (List ℕ × List ℕ)

/-- A bounded universal test. The list is part of the input. -/
def upccCaseAllB {α β : Type*} (test : α × β → Bool) (z : α × List β) : Bool :=
  (z.2.filter (fun b => !test (z.1,b))).isEmpty

theorem upccCaseAllB_spec {α β : Type*} (test : α × β → Bool) (a : α) (l : List β) :
    upccCaseAllB test (a,l) = true ↔ ∀ b ∈ l, test (a,b) = true := by
  simp [upccCaseAllB, List.filter_eq_nil_iff]

theorem upccCasePoly_all {α β : Type*} [Enc α] [Enc β] {test : α × β → Bool}
    (h : PolyFun test) : PolyFun (upccCaseAllB test) :=
  (PolyFun.filterParam (polyFun_rawJNot h)).comp polyFun_isEmpty

/-- Inclusion of two raw lists. -/
def upccCaseSubsetB {α : Type*} [DecidableEq α] (z : List α × List α) : Bool :=
  upccCaseAllB (fun q : List α × α => decide (q.2 ∈ q.1)) (z.2,z.1)

theorem upccCaseSubsetB_spec {α : Type*} [DecidableEq α] (l k : List α) :
    upccCaseSubsetB (l,k) = true ↔ l ⊆ k := by
  simp [upccCaseSubsetB, upccCaseAllB_spec, List.subset_def]

theorem upccCasePoly_subset {α : Type*} [Enc α] [DecidableEq α]
    (h : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (upccCaseSubsetB (α := α)) := by
  have hm := (polyFun_snd.pair polyFun_fst).comp (polyFun_listMem h)
  exact (polyFun_snd.pair polyFun_fst).comp (upccCasePoly_all hm)

/-- Equality of the sets listed by two raw lists. -/
def upccCaseSameB {α : Type*} [DecidableEq α] (z : List α × List α) : Bool :=
  upccCaseSubsetB z && upccCaseSubsetB (z.2,z.1)

theorem upccCaseSameB_spec {α : Type*} [DecidableEq α] (l k : List α) :
    upccCaseSameB (l,k) = true ↔ ∀ a, a ∈ l ↔ a ∈ k := by
  simp only [upccCaseSameB, Bool.and_eq_true, upccCaseSubsetB_spec, List.subset_def]
  aesop

theorem upccCasePoly_same {α : Type*} [Enc α] [DecidableEq α]
    (h : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (upccCaseSameB (α := α)) :=
  polyFun_rawJAnd (upccCasePoly_subset h)
    ((polyFun_snd.pair polyFun_fst).comp (upccCasePoly_subset h))

/-- Binary table validation. The comparison table has quadratic length. -/
def upccCaseTableB (p : RawConfig) : Bool :=
  nodupB p.1 && upccCaseSameB (p.1, List.range p.1.length) &&
    rawJNodupB (p.2.map Prod.fst) &&
    upccCaseSameB (p.2.map Prod.fst, tuplesOf p.1 2) &&
    rawJAllLtB (p.2.length, p.2.map Prod.snd)

theorem upccCaseTableB_spec (p : RawConfig) :
    upccCaseTableB p = true ↔ RawWL.WF p.1.length 2 p := by
  simp only [upccCaseTableB, Bool.and_eq_true, nodupB_eq_true, upccCaseSameB_spec,
    rawJNodupB_iff, rawJAllLtB_iff, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨hnd,hd⟩,hkeys⟩,hk⟩,hc⟩
    refine ⟨hnd,hd,hkeys,?_,?_⟩
    · intro t
      rw [hk,mem_tuplesOf]
      simp only [hd]
    · intro q hq
      exact hc q.2 (List.mem_map.2 ⟨q,hq,rfl⟩)
  · intro h
    refine ⟨⟨⟨⟨h.domNodup,h.domMem⟩,h.keyNodup⟩,?_⟩,?_⟩
    · intro t
      rw [h.keyMem,mem_tuplesOf]
      simp only [h.domMem]
    · intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.1 ha
      exact h.colLt q hq

theorem upccCasePoly_table : PolyFun upccCaseTableB := by
  have hd : PolyFun (fun p : RawConfig => nodupB p.1) := polyFun_fst.comp polyFun_nodupB
  have hr : PolyFun (fun p : RawConfig => upccCaseSameB (p.1,List.range p.1.length)) :=
    (polyFun_fst.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (upccCasePoly_same polyFun_natEq)
  have hk : PolyFun (fun p : RawConfig => p.2.map Prod.fst) :=
    polyFun_snd.comp (PolyFun.map polyFun_fst)
  have ht : PolyFun (fun p : RawConfig => tuplesOf p.1 2) :=
    polyFun_fst.comp ((polyFun_tuplesOf 2).comp polyFun_snd)
  have hc : PolyFun (fun p : RawConfig => rawJAllLtB (p.2.length,p.2.map Prod.snd)) :=
    ((polyFun_snd.comp polyFun_length).pair
    (polyFun_snd.comp (PolyFun.map polyFun_snd))).comp polyFun_rawJAllLtB
  exact polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd hd hr)
    (hk.comp polyFun_rawJNodupB)) ((hk.pair ht).comp
      (upccCasePoly_same polyFun_listNatEq))) hc

/-- Section 9.8: the table and the two disjoint parts have exact coverage. -/
structure RawUpccCase.WF (r : RawUpccCase) : Prop where
  table : RawWL.WF r.1.1.length 2 r.1
  left_nodup : r.2.1.Nodup
  right_nodup : r.2.2.Nodup
  disjoint : ∀ a ∈ r.2.1, a ∉ r.2.2
  cover : ∀ a, a ∈ r.2.1 ++ r.2.2 ↔ a ∈ r.1.1
  /-- Version indices are the names of the second part. -/
  right_names : ∀ a, a ∈ r.2.2 ↔ a < r.2.2.length

/-- Section 9.8: validate the raw encoding, including malformed inputs. -/
def upccCaseWFb (r : RawUpccCase) : Bool :=
  upccCaseTableB r.1 && nodupB r.2.1 && nodupB r.2.2 &&
    upccCaseAllB (fun z : List ℕ × ℕ => !decide (z.2 ∈ z.1)) (r.2.2,r.2.1) &&
    upccCaseSameB (r.2.1 ++ r.2.2,r.1.1) &&
    upccCaseSameB (r.2.2,List.range r.2.2.length)

theorem upccCaseWFb_spec (r : RawUpccCase) : upccCaseWFb r = true ↔ r.WF := by
  simp only [upccCaseWFb, Bool.and_eq_true, upccCaseTableB_spec, nodupB_eq_true,
    upccCaseAllB_spec, Bool.not_eq_true', decide_eq_false_iff_not, upccCaseSameB_spec, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨ht,hl⟩,hr⟩,hd⟩,hc⟩,hn⟩; exact ⟨ht,hl,hr,hd,hc,hn⟩
  · intro h; exact ⟨⟨⟨⟨⟨h.table,h.left_nodup⟩,h.right_nodup⟩,h.disjoint⟩,h.cover⟩,h.right_names⟩

theorem upccCasePoly_wf : PolyFun upccCaseWFb := by
  have hl : PolyFun (fun r : RawUpccCase => r.2.1) := polyFun_snd.comp polyFun_fst
  have hr : PolyFun (fun r : RawUpccCase => r.2.2) := polyFun_snd.comp polyFun_snd
  have hm := (polyFun_snd.pair polyFun_fst).comp polyFun_natListMem
  have hd := (hr.pair hl).comp (upccCasePoly_all (polyFun_rawJNot hm))
  have hc := (((hl.pair hr).comp polyFun_append).pair
    (polyFun_fst.comp polyFun_fst)).comp (upccCasePoly_same polyFun_natEq)
  have hn := (hr.pair (hr.comp polyFun_rangeLength)).comp
    (upccCasePoly_same polyFun_natEq)
  exact polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd
    (polyFun_fst.comp upccCasePoly_table) (hl.comp polyFun_nodupB))
      (hr.comp polyFun_nodupB)) hd) hc) hn

/-- Section 9.8: the cell at a named vertex, restricted to a supplied part. -/
def upccCaseCell (z : ((RawConfig × List ℕ) × ℕ) × ℕ) : List ℕ :=
  z.1.1.2.filter (fun y => decide (binColor (z.1.1.1,(z.1.2,y)) = z.2))

/-- Section 9.8: first-part local cells, read in direction `V₂` to `V₁`. -/
def upccCaseLink (z : (RawUpccCase × ℕ) × ℕ) : List ℕ :=
  upccCaseCell (((z.1.1.1,z.1.1.2.1),z.1.2),z.2)

/-- Section 9.8: cells inside the second part. -/
def upccCaseBlock (z : (RawUpccCase × ℕ) × ℕ) : List ℕ :=
  upccCaseCell (((z.1.1.1,z.1.1.2.2),z.1.2),z.2)

theorem upccCasePoly_cell : PolyFun upccCaseCell := by
  have hp : PolyFun (fun z : (((RawConfig × List ℕ) × ℕ) × ℕ) × ℕ => z.1.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : (((RawConfig × List ℕ) × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hc := ((hp.pair (hx.pair polyFun_snd)).comp polyFun_binColor).pair
    (polyFun_fst.comp polyFun_snd)
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp
    (PolyFun.filterParam (hc.comp polyFun_natEq))

theorem upccCasePoly_link : PolyFun upccCaseLink :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)).pair
      (polyFun_fst.comp polyFun_snd)).pair polyFun_snd).comp upccCasePoly_cell

theorem upccCasePoly_block : PolyFun upccCaseBlock :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd)).pair
      (polyFun_fst.comp polyFun_snd)).pair polyFun_snd).comp upccCasePoly_cell

/-- Section 9.8: strict dominance at threshold one half. -/
def upccCaseBig (z : (RawUpccCase × ℕ) × ℕ) : Bool :=
  decide (z.1.1.2.1.length + 1 ≤ 2 * (upccCaseLink z).length)

/-- Section 9.8: occurrence off the diagonal and size at most one half. -/
def upccCaseSmall (z : (RawUpccCase × ℕ) × ℕ) : Bool :=
  !((upccCaseBlock z).filter (fun y => decide (y ≠ z.1.2))).isEmpty &&
    decide (2 * (upccCaseBlock z).length ≤ z.1.1.2.2.length)

/-- A finite scan for colors passing the given test. -/
def upccCaseCandidates (test : (RawUpccCase × ℕ) × ℕ → Bool)
    (z : RawUpccCase × ℕ) : List ℕ :=
  (binaryColorsRaw z.1.1).filter (fun k => test (z,k))

/-- Least color in a list, or zero on the empty list. -/
def upccCaseLeast (l : List ℕ) : ℕ :=
  (upccLeastPair (l.map (fun k => (0,k)))).2

/-- Section 9.8: the least dominant link color. -/
def upccCaseM (z : RawUpccCase × ℕ) : ℕ :=
  upccCaseLeast (upccCaseCandidates upccCaseBig z)

/-- Section 9.8: the first non-dominant off-diagonal second-part color. -/
def upccCaseL (z : RawUpccCase × ℕ) : ℕ :=
  upccCaseLeast (upccCaseCandidates upccCaseSmall z)

/-- Section 9.8, step 2: no dominant color at this vertex. -/
def upccCaseSplits (z : RawUpccCase × ℕ) : Bool :=
  (upccCaseCandidates upccCaseBig z).isEmpty

theorem upccCasePoly_big : PolyFun upccCaseBig :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp
    polyFun_length).add (polyFun_const 1)).le
      ((polyFun_const 2).mul (upccCasePoly_link.comp polyFun_length))

theorem upccCasePoly_small : PolyFun upccCaseSmall := by
  have hn := (polyFun_id.pair upccCasePoly_block).comp (PolyFun.filterParam
    ((polyFun_snd.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp
      polyFun_upccNatNe))
  have hb := ((polyFun_const 2).mul (upccCasePoly_block.comp polyFun_length)).le
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_length)
  exact polyFun_rawJAnd (polyFun_rawJNot (hn.comp polyFun_isEmpty)) hb

theorem upccCasePoly_candidates {test : (RawUpccCase × ℕ) × ℕ → Bool}
    (ht : PolyFun test) : PolyFun (upccCaseCandidates test) :=
  (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_binaryColorsRaw)).comp
    (PolyFun.filterParam ht)

theorem upccCasePoly_least : PolyFun upccCaseLeast :=
  ((PolyFun.map ((polyFun_const 0).pair polyFun_id)).comp polyFun_upccLeastPair).comp
    polyFun_snd

theorem upccCasePoly_m : PolyFun upccCaseM :=
  (upccCasePoly_candidates upccCasePoly_big).comp upccCasePoly_least

theorem upccCasePoly_l : PolyFun upccCaseL :=
  (upccCasePoly_candidates upccCasePoly_small).comp upccCasePoly_least

theorem upccCasePoly_splits : PolyFun upccCaseSplits :=
  (upccCasePoly_candidates upccCasePoly_big).comp polyFun_isEmpty

end Algo
