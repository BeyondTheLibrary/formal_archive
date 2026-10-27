import Workspace.Algo.DesignRaw
import Workspace.Algo.BlockSystem
import Workspace.Algo.PipelineRelabel

/-!
# Binary tables used in Section 9

The input is the arity-two case of `RawWL`. We keep its color names when reading
diagonals and constituent relations. The decoder renames the realized colors to
`Fin rank`, as `PartitionStructure` requires. All loops run over lists, including
on malformed input.
-/

namespace Algo

open Babai RAM

/-- Section 9: a binary configuration uses the same table as binary WL. -/
abbrev RawConfig := RawWL

/-- Definition 3.1.1: read the color of an ordered pair. -/
def binColor (z : RawConfig × (ℕ × ℕ)) : ℕ :=
  tblGet (z.1.2, [z.2.1, z.2.2])

@[simp] theorem tupleOf_pair {n : ℕ} (u v : Fin n) :
    tupleOf ![u, v] = [(u : ℕ), (v : ℕ)] := by
  simp [tupleOf, List.ofFn_succ]

/-- Reading a pair is exactly the arity-two `decWL` color. -/
theorem binColor_spec {n : ℕ} (p : RawConfig) (u v : Fin n) :
    binColor (p, ((u : ℕ), (v : ℕ))) = (decWL n 2 p).color ![u, v] := by
  simp [binColor]

theorem polyFun_binColor : PolyFun binColor := by
  have hv : PolyFun (fun z : RawConfig × (ℕ × ℕ) => [z.2.2]) :=
    ((polyFun_snd.comp polyFun_snd).pair (polyFun_const ([] : List ℕ))).comp polyFun_cons
  have huv : PolyFun (fun z : RawConfig × (ℕ × ℕ) => [z.2.1, z.2.2]) :=
    ((polyFun_snd.comp polyFun_fst).pair hv).comp polyFun_cons
  exact (((polyFun_fst.comp polyFun_snd).pair huv).comp polyFun_tblGet).of_eq (fun _ => rfl)

/-- Definition 3.1.1: decode the binary table, renaming only its realized colors. -/
noncomputable def decConfig (n : ℕ) (p : RawConfig) : PartitionStructure (Fin n) :=
  PartitionStructure.ofColoring (fun u v => (decWL n 2 p).color ![u, v])

/-- The binary decoder changes color names but preserves every color class. -/
theorem decConfig_color_eq_iff {n : ℕ} (p : RawConfig) (u v a b : Fin n) :
    (decConfig n p).color u v = (decConfig n p).color a b ↔
      binColor (p, ((u : ℕ), (v : ℕ))) = binColor (p, ((a : ℕ), (b : ℕ))) := by
  rw [decConfig, PartitionStructure.ofColoring_color_eq_iff, ← binColor_spec, ← binColor_spec]

/-- Definition 3.1.4: the diagonal colors, indexed by vertex name. -/
def vertexColorsRaw (p : RawConfig) : RawLab :=
  (List.range p.1.length).map (fun u => binColor (p, (u, u)))

@[simp] theorem length_vertexColorsRaw (p : RawConfig) :
    (vertexColorsRaw p).length = p.1.length := by simp [vertexColorsRaw]

theorem labAt_vertexColorsRaw {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (u : Fin n) : labAt (vertexColorsRaw p) u = binColor (p, ((u : ℕ), (u : ℕ))) := by
  have hu : (u : ℕ) < p.1.length := by rw [card_eq_length_dom h]; exact u.isLt
  simp [labAt, vertexColorsRaw, hu]

/-- Definition 3.1.4: the fibers of the raw labelling are the vertex-color classes. -/
theorem vertexColorsRaw_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (u v : Fin n) : LabRel (vertexColorsRaw p) u v ↔
      u ∈ (decConfig n p).vertexClass ((decConfig n p).vcolor v) := by
  rw [LabRel, labAt_vertexColorsRaw h, labAt_vertexColorsRaw h]
  exact (decConfig_color_eq_iff p u u v v).symm

theorem polyFun_vertexColorsRaw : PolyFun vertexColorsRaw := by
  have hf : PolyFun (fun z : RawConfig × ℕ => binColor (z.1, (z.2, z.2))) :=
    (polyFun_fst.pair (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

/-- The color lookup respects a change of vertex names. -/
theorem binColor_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) {u v : ℕ} (hu : u < n) (hv : v < n) :
    binColor (relabelWL (π, p), (rawApply (π, u), rawApply (π, v))) =
      binColor (p, (u, v)) := by
  have ht : ∀ a ∈ [u, v], a < n := by simp only [List.mem_cons]; aesop
  simpa [binColor, permList] using tblGet_relabelWL hπ h ht

/-- The diagonal labels keep the original color names under relabeling. -/
theorem vertexColorsRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (u : Fin n) :
    labAt (vertexColorsRaw (relabelWL (π, p))) (rawApply (π, u)) =
      labAt (vertexColorsRaw p) u := by
  have hu := rawApply_lt hπ u.isLt
  rw [labAt_vertexColorsRaw (relabelWL_wf hπ h) ⟨_, hu⟩, labAt_vertexColorsRaw h]
  exact binColor_relabel h hπ u.isLt u.isLt

/-- The distinct colors of pairs, retaining the table's color names. -/
def binaryColorsRaw (p : RawConfig) : List ℕ :=
  dedupG ([], (tuplesOf p.1 2).map (fun t => tblGet (p.2, t)))

theorem mem_binaryColorsRaw {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p) (c : ℕ) :
    c ∈ binaryColorsRaw p ↔ ∃ u v : Fin n, binColor (p, ((u : ℕ), (v : ℕ))) = c := by
  rw [binaryColorsRaw, mem_dedupG_nil, List.mem_map]
  constructor
  · rintro ⟨t, ht, hc⟩
    obtain ⟨hlen, hmem⟩ := (mem_tuplesOf p.1 2 t).1 ht
    obtain ⟨x, rfl⟩ := exists_tupleOf hlen (fun a ha => (h.domMem a).1 (hmem a ha))
    refine ⟨x 0, x 1, ?_⟩
    have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx, tupleOf_pair] at hc
    exact hc
  · rintro ⟨u, v, hc⟩
    refine ⟨[(u : ℕ), (v : ℕ)], (mem_tuplesOf _ _ _).2 ⟨rfl, ?_⟩, hc⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact mem_dom h u
    · exact mem_dom h v

theorem polyFun_binaryColorsRaw : PolyFun binaryColorsRaw := by
  have hf : PolyFun (fun z : RawConfig × List ℕ => tblGet (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_tblGet
  have hm := (polyFun_id.pair (polyFun_fst.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam hf)
  exact (((polyFun_const ([] : List ℕ)).pair hm).comp
    (polyFun_dedupG polyFun_natEq)).of_eq (fun _ => rfl)

/-- The order of the constituent colors is unchanged when the vertex list is transported. -/
theorem binaryColorsRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) :
    binaryColorsRaw (relabelWL (π, p)) = binaryColorsRaw p := by
  unfold binaryColorsRaw
  rw [relabelWL_fst, tuplesOf_permList, List.map_map]
  congr 2
  apply List.map_congr_left
  intro t ht
  exact tblGet_relabelWL hπ h (fun a ha =>
    (h.domMem a).1 (((mem_tuplesOf _ _ _).1 ht).2 a ha))

/-- Definition 3.1.1: the rank counts realized colors, including diagonal colors. -/
def rankRaw (p : RawConfig) : ℕ := (binaryColorsRaw p).length

/-- The raw rank is the rank of the decoded partition structure. -/
theorem rankRaw_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p) :
    rankRaw p = (decConfig n p).rank := by
  classical
  have hset : (binaryColorsRaw p).toFinset =
      Finset.univ.image (fun q : Fin n × Fin n => (decWL n 2 p).color ![q.1, q.2]) := by
    ext c
    simp only [List.mem_toFinset, mem_binaryColorsRaw h, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.exists, ← binColor_spec]
  have hnd : (binaryColorsRaw p).Nodup := nodup_dedupG _
  change (binaryColorsRaw p).length = _
  rw [← List.toFinset_card_of_nodup hnd, hset]
  rfl

theorem polyFun_rankRaw : PolyFun rankRaw := polyFun_binaryColorsRaw.comp polyFun_length

theorem rankRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) :
    rankRaw (relabelWL (π, p)) = rankRaw p := by
  simp only [rankRaw, binaryColorsRaw_relabel h hπ]

/-- Definition 3.1.1: all pairs of the given color, as raw tuples. -/
def constituentRaw (z : RawConfig × ℕ) : List (List ℕ) :=
  (tuplesOf z.1.1 2).filter (fun t => decide (tblGet (z.1.2, t) = z.2))

theorem constituentRaw_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (c : ℕ) (u v : Fin n) :
    [(u : ℕ), (v : ℕ)] ∈ constituentRaw (p, c) ↔
      (decWL n 2 p).color ![u, v] = c := by
  have ht : [(u : ℕ), (v : ℕ)] ∈ tuplesOf p.1 2 := by
    rw [mem_tuplesOf]
    simp [mem_dom h u, mem_dom h v]
  simp [constituentRaw, ht, decWL_color]

/-- The same relation, with the decoded structure's color names. -/
theorem constituentRaw_rel {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (a b u v : Fin n) :
    [(u : ℕ), (v : ℕ)] ∈ constituentRaw (p, binColor (p, ((a : ℕ), (b : ℕ)))) ↔
      (u, v) ∈ (decConfig n p).rel ((decConfig n p).color a b) := by
  rw [constituentRaw_spec h, ← binColor_spec]
  exact (decConfig_color_eq_iff p u v a b).symm

theorem polyFun_constituentRaw : PolyFun constituentRaw := by
  have hc : PolyFun (fun z : (RawConfig × ℕ) × List ℕ => tblGet (z.1.1.2, z.2)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_tblGet
  have hf : PolyFun (fun z : (RawConfig × ℕ) × List ℕ =>
      decide (tblGet (z.1.1.2, z.2) = z.1.2)) :=
    (hc.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp
    ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

/-- Every constituent is transported as a list, with the order of its pairs preserved. -/
theorem constituentRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (c : ℕ) :
    constituentRaw (relabelWL (π, p), c) = (constituentRaw (p, c)).map (permList π) := by
  unfold constituentRaw
  rw [relabelWL_fst, tuplesOf_permList, List.filter_map]
  congr 1
  apply List.filter_congr
  intro t ht
  dsimp only [Function.comp_def]
  rw [tblGet_relabelWL hπ h (fun a ha =>
    (h.domMem a).1 (((mem_tuplesOf _ _ _).1 ht).2 a ha))]

/-- Definition 3.1.1: one entry for every constituent, paired with its raw color name. -/
def constituentsRaw (p : RawConfig) : List (ℕ × List (List ℕ)) :=
  (binaryColorsRaw p).map (fun c => (c, constituentRaw (p, c)))

/-- The list contains exactly the nonempty constituent relations. -/
theorem constituentsRaw_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (c : ℕ) (r : List (List ℕ)) : (c, r) ∈ constituentsRaw p ↔
      (∃ u v : Fin n, (decWL n 2 p).color ![u, v] = c) ∧ r = constituentRaw (p, c) := by
  simp only [constituentsRaw, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨d, hd, rfl, rfl⟩
    exact ⟨by simpa only [binColor_spec] using (mem_binaryColorsRaw h d).1 hd, rfl⟩
  · rintro ⟨hc, rfl⟩
    exact ⟨c, (mem_binaryColorsRaw h c).2 (by simpa only [binColor_spec] using hc), rfl, rfl⟩

theorem polyFun_constituentsRaw : PolyFun constituentsRaw := by
  have hf : PolyFun (fun z : RawConfig × ℕ => (z.2, constituentRaw z)) :=
    polyFun_snd.pair polyFun_constituentRaw
  exact ((polyFun_id.pair polyFun_binaryColorsRaw).comp
    (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

/-- Definition 3.1.1: adjacency in a constituent, with isolated vertices retained. -/
def constituentAdj (z : (RawConfig × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (binColor (z.1.1, z.2) = z.1.2)

theorem constituentAdj_spec {n : ℕ} (p : RawConfig) (a b u v : Fin n) :
    constituentAdj ((p, binColor (p, ((a : ℕ), (b : ℕ)))), ((u : ℕ), (v : ℕ))) = true ↔
      (u, v) ∈ ((decConfig n p).extConstituent ((decConfig n p).color a b)).E := by
  simp only [constituentAdj, decide_eq_true_eq, PartitionStructure.extConstituent_E,
    PartitionStructure.mem_rel]
  exact (decConfig_color_eq_iff p u v a b).symm

/-- Restricting the same adjacency test to effective vertices gives the constituent. -/
theorem constituentAdj_effective_spec {n : ℕ} (p : RawConfig) (a b : Fin n)
    (u v : (decConfig n p).effVertex ((decConfig n p).color a b)) :
    constituentAdj ((p, binColor (p, ((a : ℕ), (b : ℕ)))), ((u.val : ℕ), (v.val : ℕ))) = true ↔
      (u, v) ∈ ((decConfig n p).constituent ((decConfig n p).color a b)).E :=
  constituentAdj_spec p a b u.val v.val

theorem polyFun_constituentAdj : PolyFun constituentAdj := by
  have hc : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × ℕ) => binColor (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_binColor
  exact (hc.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq

end Algo
