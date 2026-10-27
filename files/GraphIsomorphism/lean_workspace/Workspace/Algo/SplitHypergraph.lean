import Workspace.Algo.SplitNeighborhood

/-!
# Hypergraph twins

Hypergraph twins may exchange hyperedges. We test multiplicities after swapping
two vertices, rather than requiring their incidence columns to be equal.
Only the listed edges need testing: the swap is an involution, so it also
preserves zero multiplicities outside their support.
-/

namespace Algo

open Babai RAM

/-- A hypergraph on positions in a domain list, with repeated edge rows allowed. -/
abbrev RawSplitHypergraph := List ℕ × List (List ℕ)

/-- Normalize a subset row by scanning the domain positions. -/
def splitNormalizeRow (z : List ℕ × List ℕ) : List ℕ :=
  (List.range z.1.length).filter (fun v => decide (v ∈ z.2))

theorem splitNormalizeRow_eq (dom a b : List ℕ) :
    splitNormalizeRow (dom, a) = splitNormalizeRow (dom, b) ↔
      splitRowSet dom.length a = splitRowSet dom.length b := by
  constructor
  · intro he
    ext v
    have hm : (v : ℕ) ∈ splitNormalizeRow (dom, a) ↔
        (v : ℕ) ∈ splitNormalizeRow (dom, b) := by rw [he]
    simpa [splitNormalizeRow] using hm
  · intro he
    apply List.filter_congr
    intro v hv
    apply Bool.eq_iff_iff.2
    simpa using Finset.ext_iff.1 he ⟨v, List.mem_range.1 hv⟩

theorem polyFun_splitNormalizeRow : PolyFun splitNormalizeRow := by
  have hf : PolyFun (fun z : (List ℕ × List ℕ) × ℕ => decide (z.2 ∈ z.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp (polyFun_listMem polyFun_natEq)
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

/-- Count the multiplicity of the subset represented by a row. -/
def splitRowMultiplicity (z : RawSplitHypergraph × List ℕ) : ℕ :=
  ((List.range z.1.2.length).filter (fun i => decide
    (splitNormalizeRow (z.1.1, z.1.2.getD i []) = splitNormalizeRow (z.1.1, z.2)))).length

theorem splitRowMultiplicity_spec (z : RawSplitHypergraph) (row : List ℕ) :
    splitRowMultiplicity (z, row) =
      (decSplitHypergraph z.1.length z.2).mult (splitRowSet z.1.length row) := by
  have hh := ncard_eq_length_filter (List.range z.2.length) List.nodup_range
    (fun a ha => List.mem_range.1 ha)
    (fun i => decide (splitNormalizeRow (z.1, z.2.getD i []) = splitNormalizeRow (z.1, row)))
  have he : {i : Fin z.2.length | (i : ℕ) ∈ List.range z.2.length ∧
      decide (splitNormalizeRow (z.1, z.2.getD i []) = splitNormalizeRow (z.1, row)) = true} =
      (↑(Finset.univ.filter (fun i : Fin z.2.length =>
        splitRowSet z.1.length (z.2.getD i []) = splitRowSet z.1.length row)) : Set (Fin z.2.length)) := by
    ext i
    simp only [Set.mem_setOf_eq, List.mem_range, i.isLt, true_and, decide_eq_true_eq,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, splitNormalizeRow_eq]
  rw [he, Set.ncard_coe_finset] at hh
  exact hh.symm

theorem polyFun_splitRowMultiplicity : PolyFun splitRowMultiplicity := by
  let T := RawSplitHypergraph × List ℕ
  have hd : PolyFun (fun z : T × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hr : PolyFun (fun z : T × ℕ => z.1.1.2.getD z.2 []) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).pair
      (polyFun_const ([] : List ℕ))).comp polyFun_getD
  have ha := (hd.pair hr).comp polyFun_splitNormalizeRow
  have hb := (hd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_splitNormalizeRow
  have hp := (ha.pair hb).comp polyFun_listNatEq
  exact (((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hp)).comp polyFun_length).of_eq (fun _ => rfl)

/-- Swap two vertices of a row, then list the resulting subset in position order. -/
def splitSwapRow (z : (List ℕ × List ℕ) × (ℕ × ℕ)) : List ℕ :=
  (List.range z.1.1.length).filter (fun w => decide (swapPointRaw (z.2, w) ∈ z.1.2))

theorem splitSwapRow_spec (dom row : List ℕ) (u v : Fin dom.length) :
    splitRowSet dom.length (splitSwapRow ((dom, row), ((u : ℕ), (v : ℕ)))) =
      (splitRowSet dom.length row).image (Equiv.swap u v) := by
  ext w
  simp only [mem_splitRowSet, splitSwapRow, List.mem_filter, List.mem_range, w.isLt,
    true_and, decide_eq_true_eq, swapPointRaw_spec]
  constructor
  · intro h
    exact Finset.mem_image.2 ⟨Equiv.swap u v w, (mem_splitRowSet _ _).2 h, by simp⟩
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    simpa using (mem_splitRowSet row a).1 ha

theorem polyFun_splitSwapRow : PolyFun splitSwapRow := by
  have hs : PolyFun (fun z : ((List ℕ × List ℕ) × (ℕ × ℕ)) × ℕ =>
      swapPointRaw (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_swapPointRaw
  have hp := (hs.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp
    (polyFun_listMem polyFun_natEq)
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hp)).of_eq (fun _ => rfl)

/-- Definition 2.5.6: test multiplicities under a transposition. -/
def hypergraphTwinTest (z : RawSplitHypergraph × (ℕ × ℕ)) : Bool :=
  ((List.range z.1.2.length).filter (fun i => decide
    (splitRowMultiplicity (z.1, splitSwapRow ((z.1.1, z.1.2.getD i []), z.2)) ≠
      splitRowMultiplicity (z.1, z.1.2.getD i [])))).isEmpty

private theorem splitSwap_mem_aut_iff {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (u v : V) : Equiv.swap u v ∈ H.Aut ↔
      ∀ i, H.mult ((H.edge i).image (Equiv.swap u v)) = H.mult (H.edge i) := by
  have hinv (A : Finset V) : (A.image (Equiv.swap u v)).image (Equiv.swap u v) = A := by
    simp [Finset.image_image, Function.comp_def]
  have hz (A : Finset V) (hA : ¬ ∃ i, H.edge i = A) : H.mult A = 0 := by
    simp only [Hypergraph.mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies]
    exact fun i hi => hA ⟨i, hi⟩
  constructor
  · intro h i; exact h (H.edge i)
  · intro h A
    by_cases ha : ∃ i, H.edge i = A
    · obtain ⟨i, rfl⟩ := ha; exact h i
    · by_cases hb : ∃ i, H.edge i = A.image (Equiv.swap u v)
      · obtain ⟨i, hi⟩ := hb
        have hh := h i
        rw [hi, hinv] at hh
        exact hh.symm
      · rw [hz A ha, hz _ hb]

/-- The hypergraph test is the paper's twin-or-equal relation, with edge multiplicities. -/
theorem hypergraphTwinTest_spec (z : RawSplitHypergraph) (u v : Fin z.1.length) :
    hypergraphTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      TwinOrEq (decSplitHypergraph z.1.length z.2).Aut u v := by
  have he : hypergraphTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      Equiv.swap u v ∈ (decSplitHypergraph z.1.length z.2).Aut := by
    rw [splitSwap_mem_aut_iff]
    simp only [hypergraphTwinTest, List.isEmpty_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_not, List.mem_range, splitRowMultiplicity_spec,
      splitSwapRow_spec]
    exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [he]
  by_cases huv : u = v
  · subst v
    exact ⟨fun _ => Or.inl rfl, fun _ => by
      simpa only [Equiv.swap_self] using (decSplitHypergraph z.1.length z.2).Aut.one_mem⟩
  · simp [TwinOrEq, IsTwin, huv]

theorem polyFun_hypergraphTwinTest : PolyFun hypergraphTwinTest := by
  let T := RawSplitHypergraph × (ℕ × ℕ)
  have hz : PolyFun (fun z : T × ℕ => z.1.1) := polyFun_fst.comp polyFun_fst
  have hr : PolyFun (fun z : T × ℕ => z.1.1.2.getD z.2 []) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).pair
      (polyFun_const ([] : List ℕ))).comp polyFun_getD
  have hs := ((((hz.comp polyFun_fst).pair hr).pair (polyFun_fst.comp polyFun_snd))).comp
    polyFun_splitSwapRow
  have hbefore := (hz.pair hr).comp polyFun_splitRowMultiplicity
  have hafter := (hz.pair hs).comp polyFun_splitRowMultiplicity
  have hp : PolyFun (fun z : T × ℕ => decide
      (splitRowMultiplicity (z.1.1, splitSwapRow ((z.1.1.1, z.1.1.2.getD z.2 []), z.1.2)) ≠
        splitRowMultiplicity (z.1.1, z.1.1.2.getD z.2 []))) :=
    (PolyFun.ite ((hafter.pair hbefore).comp polyFun_natEq) (polyFun_const false)
      (polyFun_const true)).of_eq (fun z => by
        by_cases h : splitRowMultiplicity (z.1.1,
            splitSwapRow ((z.1.1.1, z.1.1.2.getD z.2 []), z.1.2)) =
              splitRowMultiplicity (z.1.1, z.1.1.2.getD z.2 []) <;> simp [h])
  exact (((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hp)).comp polyFun_isEmpty).of_eq (fun _ => rfl)

/-- Definition 2.5.6: the hypergraph twin classes, including singleton classes. -/
def hypergraphTwinsRaw (z : RawSplitHypergraph) : RawLab :=
  relationLabRaw hypergraphTwinTest (z, z.1)

@[simp] theorem length_hypergraphTwinsRaw (z : RawSplitHypergraph) :
    (hypergraphTwinsRaw z).length = z.1.length := length_relationLabRaw _ _

theorem hypergraphTwinsRaw_spec (z : RawSplitHypergraph) (u v : Fin z.1.length) :
    LabRel (hypergraphTwinsRaw z) u v ↔ TwinOrEq (decSplitHypergraph z.1.length z.2).Aut u v :=
  relationLabRaw_spec rfl (twinOrEq_equivalence _) (hypergraphTwinTest_spec z) u v

theorem polyFun_hypergraphTwinsRaw : PolyFun hypergraphTwinsRaw :=
  ((polyFun_id.pair polyFun_fst).comp
    (polyFun_relationLabRaw polyFun_hypergraphTwinTest)).of_eq (fun _ => rfl)

/-- Count the hypergraph twin class of a vertex. -/
theorem hypergraphTwinSize_spec (z : RawSplitHypergraph) (u : Fin z.1.length) :
    classSizeRaw (hypergraphTwinsRaw z, u) =
      (twinClass (decSplitHypergraph z.1.length z.2).Aut u).ncard := by
  rw [classSizeRaw_spec_of_length (length_hypergraphTwinsRaw z)]
  congr 1
  ext v
  rw [labSet, Set.mem_setOf_eq, hypergraphTwinsRaw_spec]
  exact ⟨fun h => (twinOrEq_equivalence _).symm h, fun h => (twinOrEq_equivalence _).symm h⟩

/-- The domain list supplies only the number of hypergraph vertices. -/
theorem hypergraphTwinsRaw_domain_congr {dom dom' : List ℕ} (hlen : dom.length = dom'.length)
    (rows : List (List ℕ)) : hypergraphTwinsRaw (dom, rows) = hypergraphTwinsRaw (dom', rows) := by
  unfold hypergraphTwinsRaw relationLabRaw relationRepRaw relationClassRaw
    hypergraphTwinTest splitRowMultiplicity splitSwapRow splitNormalizeRow
  simp only [hlen]

/-- Neighborhood hypergraph twins keep their positions under ambient relabeling. -/
theorem neighborhoodHypergraphTwins_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n) :
    hypergraphTwinsRaw ((splitRelabelBipRaw (π, z)).2.2,
        neighborhoodRowsRaw (splitRelabelBipRaw (π, z))) =
      hypergraphTwinsRaw (z.2.2, neighborhoodRowsRaw z) := by
  rw [neighborhoodRowsRaw_relabel hp hπ hl hr]
  exact hypergraphTwinsRaw_domain_congr (splitRelabelBipRaw_right_length π z) _

end Algo
