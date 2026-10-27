import Workspace.Algo.SplitTwinTransport
import Workspace.Prelim.Hypergraphs

/-!
# Neighborhood rows

The vertices of the hypergraph are positions in the second supplied part.
There is one row for each vertex of the first part. Equal rows are retained
until the caller asks for the simple hypergraph. A row lists its vertices in
increasing position order, so no choice of an ordering on the abstract carrier
is made here.
-/

namespace Algo

open Babai RAM

/-- Section 9.7: the neighborhood in the second part of one first-part vertex. -/
def splitNeighborhoodRow (z : RawBipConstituent × ℕ) : List ℕ :=
  (List.range z.1.2.2.length).filter (fun v => bipAdjRaw (z.1, (z.2, v)))

theorem mem_splitNeighborhoodRow (z : RawBipConstituent) (u v : ℕ) :
    v ∈ splitNeighborhoodRow (z, u) ↔
      v < z.2.2.length ∧ bipAdjRaw (z, (u, v)) = true := by
  simp [splitNeighborhoodRow]

theorem polyFun_splitNeighborhoodRow : PolyFun splitNeighborhoodRow := by
  have hf : PolyFun (fun z : (RawBipConstituent × ℕ) × ℕ =>
      bipAdjRaw (z.1.1, (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_bipAdjRaw
  exact ((polyFun_id.pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_rangeLength)).comp
      (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

/-- Section 9.7: one neighborhood per first-part vertex, retaining multiplicities. -/
def neighborhoodRowsRaw (z : RawBipConstituent) : List (List ℕ) :=
  (List.range z.2.1.length).map (fun u => splitNeighborhoodRow (z, u))

@[simp] theorem length_neighborhoodRowsRaw (z : RawBipConstituent) :
    (neighborhoodRowsRaw z).length = z.2.1.length := by simp [neighborhoodRowsRaw]

theorem neighborhoodRowsRaw_get (z : RawBipConstituent) (u : Fin z.2.1.length) :
    (neighborhoodRowsRaw z).getD u [] = splitNeighborhoodRow (z, u) := by
  simp [neighborhoodRowsRaw, u.isLt]

theorem neighborhoodRowsRaw_spec (z : RawBipConstituent)
    (u : Fin z.2.1.length) (v : Fin z.2.2.length) :
    (v : ℕ) ∈ (neighborhoodRowsRaw z).getD u [] ↔ (u, v) ∈ (decBipConstituent z).E := by
  rw [neighborhoodRowsRaw_get, mem_splitNeighborhoodRow]
  exact and_iff_right v.isLt

theorem polyFun_neighborhoodRowsRaw : PolyFun neighborhoodRowsRaw :=
  ((polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_splitNeighborhoodRow)).of_eq (fun _ => rfl)

/-- A finite subset decoded from a row. Out-of-range names are ignored. -/
def splitRowSet (n : ℕ) (row : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (v : ℕ) ∈ row)

@[simp] theorem mem_splitRowSet {n : ℕ} (row : List ℕ) (v : Fin n) :
    v ∈ splitRowSet n row ↔ (v : ℕ) ∈ row := by simp [splitRowSet]

/-- Decode rows as a multiset of hyperedges, with row positions as edge indices. -/
def decSplitHypergraph (n : ℕ) (rows : List (List ℕ)) : Hypergraph (Fin n) where
  numEdges := rows.length
  edge i := splitRowSet n (rows.getD i [])

/-- Section 9.7: the incidence graph of the decoded rows is the supplied bipartite graph.
The edge-index map is the identity on first-part positions. -/
theorem neighborhoodRowsRaw_edge (z : RawBipConstituent) (u : Fin z.2.1.length) :
    (decSplitHypergraph z.2.2.length (neighborhoodRowsRaw z)).edge
        ⟨u, by simpa [decSplitHypergraph] using u.isLt⟩ =
      Finset.univ.filter (fun v : Fin z.2.2.length =>
        bipAdjRaw (z, ((u : ℕ), (v : ℕ))) = true) := by
  change splitRowSet _ ((neighborhoodRowsRaw z).getD u []) = _
  rw [neighborhoodRowsRaw_get]
  ext v
  simp [mem_splitNeighborhoodRow]

/-- Rows listed in increasing order and using only names below `n`. -/
def SplitRowsWF (n : ℕ) (rows : List (List ℕ)) : Prop :=
  ∀ row ∈ rows, row.Pairwise (· < ·) ∧ ∀ v ∈ row, v < n

theorem neighborhoodRowsRaw_wf (z : RawBipConstituent) :
    SplitRowsWF z.2.2.length (neighborhoodRowsRaw z) := by
  intro row hr
  obtain ⟨u, _, rfl⟩ := List.mem_map.1 hr
  exact ⟨List.pairwise_lt_range.filter _, fun v hv => (mem_splitNeighborhoodRow _ _ _).1 hv |>.1⟩

theorem splitRowSet_inj {n : ℕ} {rows : List (List ℕ)} (hw : SplitRowsWF n rows)
    {a b : List ℕ} (ha : a ∈ rows) (hb : b ∈ rows) :
    splitRowSet n a = splitRowSet n b ↔ a = b := by
  constructor
  · intro he
    apply (hw a ha).1.eq_of_mem_iff (hw b hb).1
    intro v
    by_cases hv : v < n
    · exact (mem_splitRowSet a ⟨v, hv⟩).symm.trans
        ((Finset.ext_iff.1 he ⟨v, hv⟩).trans (mem_splitRowSet b ⟨v, hv⟩))
    · exact iff_of_false (fun h => hv ((hw a ha).2 v h)) (fun h => hv ((hw b hb).2 v h))
  · rintro rfl; rfl

/-- Forget repeated edges, in reverse order of first occurrence as in `dedupG`. -/
def simpleHypergraphRowsRaw (rows : List (List ℕ)) : List (List ℕ) := dedupG ([], rows)

@[simp] theorem mem_simpleHypergraphRowsRaw (rows : List (List ℕ)) (row : List ℕ) :
    row ∈ simpleHypergraphRowsRaw rows ↔ row ∈ rows := mem_dedupG_nil _ _

theorem polyFun_simpleHypergraphRowsRaw : PolyFun simpleHypergraphRowsRaw :=
  (((polyFun_const ([] : List (List ℕ))).pair polyFun_id).comp
    (polyFun_dedupG polyFun_listNatEq)).of_eq (fun _ => rfl)

/-- Removing duplicate rows preserves exactly the edge set. -/
theorem simpleHypergraphRowsRaw_edgeSet (n : ℕ) (rows : List (List ℕ)) :
    (decSplitHypergraph n (simpleHypergraphRowsRaw rows)).edgeSet =
      (decSplitHypergraph n rows).edgeSet := by
  have hm (rs : List (List ℕ)) (A : Finset (Fin n)) :
      A ∈ (decSplitHypergraph n rs).edgeSet ↔ ∃ row ∈ rs, splitRowSet n row = A := by
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨rs.getD i [], ?_, rfl⟩
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact List.getElem_mem _
    · rintro ⟨row, hr, he⟩
      obtain ⟨i, hi, hi'⟩ := List.getElem_of_mem hr
      refine ⟨⟨i, hi⟩, ?_⟩
      change splitRowSet n (rs.getD i []) = A
      rw [List.getD_eq_getElem _ _ hi, hi']
      exact he
  ext A
  simp only [hm, mem_simpleHypergraphRowsRaw]

/-- Distinct normalized rows decode to distinct edges. -/
theorem simpleHypergraphRowsRaw_isSimple {n : ℕ} {rows : List (List ℕ)}
    (hw : SplitRowsWF n rows) :
    (decSplitHypergraph n (simpleHypergraphRowsRaw rows)).IsSimple := by
  intro i j hij
  have hi : (simpleHypergraphRowsRaw rows).getD i [] ∈ rows := by
    apply (mem_simpleHypergraphRowsRaw _ _).1
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem _
  have hj : (simpleHypergraphRowsRaw rows).getD j [] ∈ rows := by
    apply (mem_simpleHypergraphRowsRaw _ _).1
    rw [List.getD_eq_getElem _ _ j.isLt]
    exact List.getElem_mem _
  have he := (splitRowSet_inj hw hi hj).1 hij
  rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt] at he
  exact (List.nodup_iff_injective_getElem.1 (nodup_dedupG _)) he

/-- The ordered neighborhood rows stay unchanged when the two part lists carry
their positions along with a change of ambient vertex names. -/
theorem neighborhoodRowsRaw_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n) :
    neighborhoodRowsRaw (splitRelabelBipRaw (π, z)) = neighborhoodRowsRaw z := by
  unfold neighborhoodRowsRaw
  rw [splitRelabelBipRaw_left_length]
  apply List.map_congr_left
  intro u hu
  unfold splitNeighborhoodRow
  rw [splitRelabelBipRaw_right_length]
  apply List.filter_congr
  intro v hv
  exact bipAdjRaw_relabel hp hπ hl hr (List.mem_range.1 hu) (List.mem_range.1 hv)

/-- Repeated equal neighborhoods are removed in the same order after relabeling. -/
theorem simpleNeighborhoodRowsRaw_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n) :
    simpleHypergraphRowsRaw (neighborhoodRowsRaw (splitRelabelBipRaw (π, z))) =
      simpleHypergraphRowsRaw (neighborhoodRowsRaw z) := by
  rw [neighborhoodRowsRaw_relabel hp hπ hl hr]

end Algo
