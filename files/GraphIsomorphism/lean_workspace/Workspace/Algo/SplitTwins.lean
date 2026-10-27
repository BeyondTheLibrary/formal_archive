import Workspace.Algo.SplitRaw

/-!
# Twin classes for Section 9

An equivalence test gives a labelling by least members. The least member is only
a name for a class. It does not select one class from two classes of equal size.
For a digraph the test checks a transposition, including loops and both edge
directions, as Definition 2.3.9 requires.
-/

namespace Algo

open Babai RAM

section Labels

variable {α : Type*}

/-- The class of a point for a supplied relation test. The list supplies the domain size. -/
def relationClassRaw (test : α × (ℕ × ℕ) → Bool) (z : (α × List ℕ) × ℕ) : List ℕ :=
  (List.range z.1.2.length).filter (fun v => test (z.1.1, (z.2, v)))

theorem mem_relationClassRaw (test : α × (ℕ × ℕ) → Bool) (c : α) (dom : List ℕ)
    (u v : ℕ) : v ∈ relationClassRaw test ((c, dom), u) ↔
      v < dom.length ∧ test (c, (u, v)) = true := by
  simp [relationClassRaw]

theorem polyFun_relationClassRaw [Enc α] {test : α × (ℕ × ℕ) → Bool}
    (ht : PolyFun test) : PolyFun (relationClassRaw test) := by
  have hf : PolyFun (fun z : ((α × List ℕ) × ℕ) × ℕ => test (z.1.1.1, (z.1.2, z.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp ht
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

/-- The least member of a class; `0` for an empty class on malformed input. -/
def relationRepRaw (test : α × (ℕ × ℕ) → Bool) (z : (α × List ℕ) × ℕ) : ℕ :=
  labAt (relationClassRaw test z) 0

private theorem first_mem {l : List ℕ} {u : ℕ} (hu : u ∈ l) : labAt l 0 ∈ l := by
  cases l with
  | nil => simp at hu
  | cons a l => simp [labAt]

theorem relationRepRaw_mem {test : α × (ℕ × ℕ) → Bool} {c : α} {dom : List ℕ} {u : ℕ}
    (hu : u < dom.length) (hrefl : test (c, (u, u)) = true) :
    relationRepRaw test ((c, dom), u) ∈ relationClassRaw test ((c, dom), u) :=
  first_mem ((mem_relationClassRaw test c dom u u).2 ⟨hu, hrefl⟩)

/-- The representative is the least vertex name in the class. -/
theorem relationRepRaw_le {test : α × (ℕ × ℕ) → Bool} {c : α} {dom : List ℕ} {u v : ℕ}
    (hv : v ∈ relationClassRaw test ((c, dom), u)) :
    relationRepRaw test ((c, dom), u) ≤ v := by
  have hs : (relationClassRaw test ((c, dom), u)).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h)).filter _
  have hh := hs.rel_head hv
  unfold relationRepRaw
  cases he : relationClassRaw test ((c, dom), u) with
  | nil => simp [he] at hv
  | cons a l => simpa [he, labAt] using hh

theorem polyFun_relationRepRaw [Enc α] {test : α × (ℕ × ℕ) → Bool}
    (ht : PolyFun test) : PolyFun (relationRepRaw test) :=
  ((polyFun_relationClassRaw ht).pair (polyFun_const 0)).comp polyFun_labAt

/-- Name each equivalence class by its least member. -/
def relationLabRaw (test : α × (ℕ × ℕ) → Bool) (z : α × List ℕ) : RawLab :=
  (List.range z.2.length).map (fun u => relationRepRaw test (z, u))

@[simp] theorem length_relationLabRaw (test : α × (ℕ × ℕ) → Bool) (z : α × List ℕ) :
    (relationLabRaw test z).length = z.2.length := by simp [relationLabRaw]

theorem labAt_relationLabRaw (test : α × (ℕ × ℕ) → Bool) (c : α) (dom : List ℕ)
    {u : ℕ} (hu : u < dom.length) :
    labAt (relationLabRaw test (c, dom)) u = relationRepRaw test ((c, dom), u) := by
  simp [labAt, relationLabRaw, hu]

/-- For an equivalence test the raw labelling has exactly the tested classes. -/
theorem relationLabRaw_spec {test : α × (ℕ × ℕ) → Bool} {c : α} {dom : List ℕ} {n : ℕ}
    (hlen : dom.length = n) {r : Fin n → Fin n → Prop} (hr : Equivalence r)
    (hspec : ∀ u v : Fin n, test (c, ((u : ℕ), (v : ℕ))) = true ↔ r u v)
    (u v : Fin n) : LabRel (relationLabRaw test (c, dom)) u v ↔ r u v := by
  have hu : (u : ℕ) < dom.length := by rw [hlen]; exact u.isLt
  have hv : (v : ℕ) < dom.length := by rw [hlen]; exact v.isLt
  rw [LabRel, labAt_relationLabRaw _ _ _ hu, labAt_relationLabRaw _ _ _ hv]
  constructor
  · intro he
    have hmu := (mem_relationClassRaw _ _ _ _ _).1
      (relationRepRaw_mem hu ((hspec u u).2 (hr.refl u)))
    have hmv := (mem_relationClassRaw _ _ _ _ _).1
      (relationRepRaw_mem hv ((hspec v v).2 (hr.refl v)))
    rw [← he] at hmv
    let w : Fin n := ⟨_, by simpa [hlen] using hmu.1⟩
    exact hr.trans ((hspec u w).1 hmu.2) (hr.symm ((hspec v w).1 hmv.2))
  · intro huv
    have he : relationClassRaw test ((c, dom), (u : ℕ)) =
        relationClassRaw test ((c, dom), (v : ℕ)) := by
      apply List.filter_congr
      intro a ha
      have ha' : a < n := by simpa [hlen] using (List.mem_range.1 ha)
      apply Bool.eq_iff_iff.2
      rw [hspec u ⟨a, ha'⟩, hspec v ⟨a, ha'⟩]
      exact ⟨fun h => hr.trans (hr.symm huv) h, fun h => hr.trans huv h⟩
    exact congrArg (fun l => labAt l 0) he

theorem polyFun_relationLabRaw [Enc α] {test : α × (ℕ × ℕ) → Bool}
    (ht : PolyFun test) : PolyFun (relationLabRaw test) :=
  ((polyFun_id.pair (polyFun_snd.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam (polyFun_relationRepRaw ht))).of_eq (fun _ => rfl)

/-- Each label names a member of its own class and is no larger than any other member. -/
theorem relationLabRaw_label_spec {test : α × (ℕ × ℕ) → Bool} {c : α} {dom : List ℕ} {n : ℕ}
    (hlen : dom.length = n) {r : Fin n → Fin n → Prop} (hr : Equivalence r)
    (hspec : ∀ u v : Fin n, test (c, ((u : ℕ), (v : ℕ))) = true ↔ r u v)
    (u : Fin n) : ∃ w : Fin n,
      labAt (relationLabRaw test (c, dom)) u = (w : ℕ) ∧ r u w ∧
        ∀ v : Fin n, r u v → (w : ℕ) ≤ (v : ℕ) := by
  have hu : (u : ℕ) < dom.length := by rw [hlen]; exact u.isLt
  have hm := relationRepRaw_mem hu ((hspec u u).2 (hr.refl u))
  have hb := (mem_relationClassRaw _ _ _ _ _).1 hm
  let w : Fin n := ⟨_, by simpa [hlen] using hb.1⟩
  refine ⟨w, labAt_relationLabRaw _ _ _ hu, (hspec u w).1 hb.2, ?_⟩
  intro v hv
  exact relationRepRaw_le ((mem_relationClassRaw _ _ _ _ _).2
    ⟨by rw [hlen]; exact v.isLt, (hspec u v).2 hv⟩)

end Labels

/-- The extended constituent of a raw color, before renaming colors in `decConfig`. -/
def decConstituent (n : ℕ) (z : RawConfig × ℕ) : Digraph (Fin n) :=
  ⟨{q | binColor (z.1, ((q.1 : ℕ), (q.2 : ℕ))) = z.2}⟩

theorem decConstituent_spec {n : ℕ} (p : RawConfig) (a b u v : Fin n) :
    (u, v) ∈ (decConstituent n (p, binColor (p, ((a : ℕ), (b : ℕ))))).E ↔
      (u, v) ∈ ((decConfig n p).extConstituent ((decConfig n p).color a b)).E :=
  (decConfig_color_eq_iff p u v a b).symm

/-- Apply a transposition to a vertex name. -/
def swapPointRaw (z : (ℕ × ℕ) × ℕ) : ℕ :=
  if z.2 = z.1.1 then z.1.2 else if z.2 = z.1.2 then z.1.1 else z.2

theorem swapPointRaw_spec {n : ℕ} (u v w : Fin n) :
    swapPointRaw (((u : ℕ), (v : ℕ)), (w : ℕ)) = (Equiv.swap u v w : ℕ) := by
  by_cases hwu : w = u
  · subst w; simp [swapPointRaw]
  · by_cases hwv : w = v
    · subst w; simp [swapPointRaw]
    · simp [swapPointRaw, Equiv.swap_apply_of_ne_of_ne hwu hwv,
        show (w : ℕ) ≠ (u : ℕ) from fun he => hwu (Fin.ext he),
        show (w : ℕ) ≠ (v : ℕ) from fun he => hwv (Fin.ext he)]

theorem polyFun_swapPointRaw : PolyFun swapPointRaw := by
  have h1 : PolyFun (fun z : (ℕ × ℕ) × ℕ => decide (z.2 = z.1.1)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_natEq
  have h2 : PolyFun (fun z : (ℕ × ℕ) × ℕ => decide (z.2 = z.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq
  exact (PolyFun.ite h1 (polyFun_fst.comp polyFun_snd)
    (PolyFun.ite h2 (polyFun_fst.comp polyFun_fst) polyFun_snd)).of_eq (fun z => by
      by_cases h : z.2 = z.1.1 <;> by_cases h' : z.2 = z.1.2 <;> simp [swapPointRaw, h, h'])

private theorem polyFun_boolNe_split : PolyFun (fun z : Bool × Bool => decide (z.1 ≠ z.2)) :=
  (PolyFun.ite polyFun_fst
    (PolyFun.ite polyFun_snd (polyFun_const false) (polyFun_const true)) polyFun_snd).of_eq
      (fun z => by rcases z with ⟨a, b⟩; cases a <;> cases b <;> rfl)

/-- Definition 2.3.9: test whether the transposition preserves every directed edge. -/
def constituentTwinTest (z : (RawConfig × ℕ) × (ℕ × ℕ)) : Bool :=
  ((labPairsList z.1.1.1).filter (fun q => decide
    (constituentAdj (z.1, (swapPointRaw (z.2, q.1), swapPointRaw (z.2, q.2))) ≠
      constituentAdj (z.1, q)))).isEmpty

/-- The test includes equal vertices and is the paper's twin-or-equal relation. -/
theorem constituentTwinTest_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (c : ℕ) (u v : Fin n) :
    constituentTwinTest ((p, c), ((u : ℕ), (v : ℕ))) = true ↔
      TwinOrEq (decConstituent n (p, c)).Aut u v := by
  have htest : constituentTwinTest ((p, c), ((u : ℕ), (v : ℕ))) = true ↔
      Equiv.swap u v ∈ (decConstituent n (p, c)).Aut := by
    simp only [constituentTwinTest, List.isEmpty_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_not, Digraph.mem_aut]
    constructor
    · intro ht a b
      have he := ht ((a : ℕ), (b : ℕ))
        (mem_labPairsList.2 ⟨by rw [card_eq_length_dom h]; exact a.isLt,
          by rw [card_eq_length_dom h]; exact b.isLt⟩)
      rw [swapPointRaw_spec, swapPointRaw_spec] at he
      simpa [constituentAdj, decConstituent] using Bool.eq_iff_iff.1 he
    · intro ht q hq
      have hq' := mem_labPairsList.1 hq
      rw [card_eq_length_dom h] at hq'
      let a : Fin n := ⟨q.1, hq'.1⟩
      let b : Fin n := ⟨q.2, hq'.2⟩
      have hsa := swapPointRaw_spec u v a
      have hsb := swapPointRaw_spec u v b
      rw [hsa, hsb]
      apply Bool.eq_iff_iff.2
      simpa [constituentAdj, decConstituent, a, b] using ht a b
  rw [htest]
  by_cases huv : u = v
  · subst v; simp [TwinOrEq]
  · simp [TwinOrEq, IsTwin, huv]

theorem polyFun_constituentTwinTest : PolyFun constituentTwinTest := by
  let T := (RawConfig × ℕ) × (ℕ × ℕ)
  have hc : PolyFun (fun z : T × (ℕ × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hs : PolyFun (fun z : T × (ℕ × ℕ) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have ha : PolyFun (fun z : T × (ℕ × ℕ) => swapPointRaw (z.1.2, z.2.1)) :=
    (hs.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_swapPointRaw
  have hb : PolyFun (fun z : T × (ℕ × ℕ) => swapPointRaw (z.1.2, z.2.2)) :=
    (hs.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_swapPointRaw
  have hbefore : PolyFun (fun z : T × (ℕ × ℕ) => constituentAdj (z.1.1, z.2)) :=
    (hc.pair polyFun_snd).comp polyFun_constituentAdj
  have hafter : PolyFun (fun z : T × (ℕ × ℕ) =>
      constituentAdj (z.1.1, (swapPointRaw (z.1.2, z.2.1), swapPointRaw (z.1.2, z.2.2)))) :=
    (hc.pair (ha.pair hb)).comp polyFun_constituentAdj
  have hp := (hafter.pair hbefore).comp polyFun_boolNe_split
  have hdom : PolyFun (fun z : T => labPairsList z.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_labPairsList)
  exact (((polyFun_id.pair hdom).comp (PolyFun.filterParam hp)).comp
    polyFun_isEmpty).of_eq (fun _ => rfl)

/-- Definition 2.3.11: twin classes of a constituent, named by their least vertices. -/
def constituentTwinsRaw (z : RawConfig × ℕ) : RawLab :=
  relationLabRaw constituentTwinTest (z, z.1.1)

@[simp] theorem length_constituentTwinsRaw (z : RawConfig × ℕ) :
    (constituentTwinsRaw z).length = z.1.1.length := length_relationLabRaw _ _

/-- The decoded labelling is the twin equivalence relation, including singleton classes. -/
theorem constituentTwinsRaw_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (c : ℕ) (u v : Fin n) : LabRel (constituentTwinsRaw (p, c)) u v ↔
      TwinOrEq (decConstituent n (p, c)).Aut u v :=
  relationLabRaw_spec (card_eq_length_dom h) (twinOrEq_equivalence _)
    (constituentTwinTest_spec h c) u v

theorem polyFun_constituentTwinsRaw : PolyFun constituentTwinsRaw :=
  ((polyFun_id.pair (polyFun_fst.comp polyFun_fst)).comp
    (polyFun_relationLabRaw polyFun_constituentTwinTest)).of_eq (fun _ => rfl)

/-- A constituent with two specified parts. Vertices in each part are named by list position. -/
abbrev RawBipConstituent := (RawConfig × ℕ) × (List ℕ × List ℕ)

/-- Read adjacency at positions in the two given vertex lists. -/
def bipAdjRaw (z : RawBipConstituent × (ℕ × ℕ)) : Bool :=
  constituentAdj (z.1.1, (labAt z.1.2.1 z.2.1, labAt z.1.2.2 z.2.2))

/-- The bipartite constituent, with each part named by its positions. -/
def decBipConstituent (z : RawBipConstituent) :
    BipGraph (Fin z.2.1.length) (Fin z.2.2.length) :=
  ⟨{q | bipAdjRaw (z, ((q.1 : ℕ), (q.2 : ℕ))) = true}⟩

/-- The bipartite adjacency reads the original `decWL` color at the named vertices. -/
theorem bipAdjRaw_spec {n : ℕ} (z : RawBipConstituent) (u v : ℕ)
    (hu : labAt z.2.1 u < n) (hv : labAt z.2.2 v < n) :
    bipAdjRaw (z, (u, v)) = true ↔
      (decWL n 2 z.1.1).color ![⟨labAt z.2.1 u, hu⟩, ⟨labAt z.2.2 v, hv⟩] = z.1.2 := by
  simp [bipAdjRaw, constituentAdj, binColor_spec (n := n) z.1.1 ⟨_, hu⟩ ⟨_, hv⟩]

theorem polyFun_bipAdjRaw : PolyFun bipAdjRaw := by
  have hl : PolyFun (fun z : RawBipConstituent × (ℕ × ℕ) => labAt z.1.2.1 z.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      (polyFun_snd.comp polyFun_fst)).comp polyFun_labAt
  have hr : PolyFun (fun z : RawBipConstituent × (ℕ × ℕ) => labAt z.1.2.2 z.2.2) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
      (polyFun_snd.comp polyFun_snd)).comp polyFun_labAt
  exact (((polyFun_fst.comp polyFun_fst).pair (hl.pair hr)).comp
    polyFun_constituentAdj).of_eq (fun _ => rfl)

/-- Observation 2.4.28: compare two neighborhoods in the first part. -/
def bipTwinTest (z : RawBipConstituent × (ℕ × ℕ)) : Bool :=
  ((List.range z.1.2.2.length).filter (fun w =>
    decide (bipAdjRaw (z.1, (z.2.1, w)) ≠ bipAdjRaw (z.1, (z.2.2, w))))).isEmpty

theorem bipTwinTest_neighborhoods (z : RawBipConstituent) (u v : Fin z.2.1.length) :
    bipTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      {w | (u, w) ∈ (decBipConstituent z).E} = {w | (v, w) ∈ (decBipConstituent z).E} := by
  simp only [bipTwinTest, List.isEmpty_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq, not_not, List.mem_range]
  constructor
  · intro h
    ext w
    exact Bool.eq_iff_iff.1 (h w w.isLt)
  · intro h w hw
    exact Bool.eq_iff_iff.2 (Set.ext_iff.1 h ⟨w, hw⟩)

/-- The equal-neighborhood test is the bipartite twin relation used in Section 9.3. -/
theorem bipTwinTest_spec (z : RawBipConstituent) (u v : Fin z.2.1.length) :
    bipTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      TwinOrEq (decBipConstituent z).Aut (Sum.inl u) (Sum.inl v) := by
  rw [bipTwinTest_neighborhoods]
  by_cases huv : u = v
  · subst v; simp [TwinOrEq]
  · simp only [TwinOrEq, Sum.inl.injEq, huv, false_or]
    exact ((decBipConstituent z).isTwin_inl_iff_aux u v huv).symm

theorem polyFun_bipTwinTest : PolyFun bipTwinTest := by
  let T := RawBipConstituent × (ℕ × ℕ)
  have hc : PolyFun (fun z : T × ℕ => z.1.1) := polyFun_fst.comp polyFun_fst
  have hu : PolyFun (fun z : T × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hv : PolyFun (fun z : T × ℕ => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have ha := (hc.pair (hu.pair polyFun_snd)).comp polyFun_bipAdjRaw
  have hb := (hc.pair (hv.pair polyFun_snd)).comp polyFun_bipAdjRaw
  have hp := (ha.pair hb).comp polyFun_boolNe_split
  have hd : PolyFun (fun z : T => List.range z.1.2.2.length) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_rangeLength
  exact (((polyFun_id.pair hd).comp (PolyFun.filterParam hp)).comp
    polyFun_isEmpty).of_eq (fun _ => rfl)

/-- Bipartite twin classes in the first part, named by their least positions. -/
def bipTwinsRaw (z : RawBipConstituent) : RawLab := relationLabRaw bipTwinTest (z, z.2.1)

@[simp] theorem length_bipTwinsRaw (z : RawBipConstituent) :
    (bipTwinsRaw z).length = z.2.1.length := length_relationLabRaw _ _

theorem bipTwinsRaw_spec (z : RawBipConstituent) (u v : Fin z.2.1.length) :
    LabRel (bipTwinsRaw z) u v ↔
      TwinOrEq (decBipConstituent z).Aut (Sum.inl u) (Sum.inl v) := by
  have he := twinOrEq_equivalence (decBipConstituent z).Aut
  exact relationLabRaw_spec (r := fun u v =>
    TwinOrEq (decBipConstituent z).Aut (Sum.inl u) (Sum.inl v)) rfl
    ⟨fun u => he.refl _, fun h => he.symm h, fun h h' => he.trans h h'⟩
    (bipTwinTest_spec z) u v

theorem polyFun_bipTwinsRaw : PolyFun bipTwinsRaw :=
  ((polyFun_id.pair (polyFun_snd.comp polyFun_fst)).comp
    (polyFun_relationLabRaw polyFun_bipTwinTest)).of_eq (fun _ => rfl)

/-- Count the class of a given vertex. This routine makes no choice between classes. -/
def classSizeRaw (z : RawLab × ℕ) : ℕ := (labClass z.1 z.1 z.2).length

/-- A raw class size is the cardinality of the decoded fiber. -/
theorem classSizeRaw_spec (lab : RawLab) (u : ℕ) :
    classSizeRaw (lab, u) = (labSet lab.length lab u).ncard := by
  have he : labSet lab.length lab u = {v : Fin lab.length |
      (v : ℕ) ∈ List.range lab.length ∧ decide (labAt lab v = labAt lab u) = true} := by
    ext v
    simp [labSet, LabRel]
  rw [he]
  exact (ncard_eq_length_filter (List.range lab.length) List.nodup_range
    (fun a ha => List.mem_range.1 ha) (fun v => decide (labAt lab v = labAt lab u))).symm

theorem polyFun_classSizeRaw : PolyFun classSizeRaw := by
  have h1 : PolyFun (fun z : (RawLab × ℕ) × ℕ => labAt z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_labAt
  have h2 : PolyFun (fun z : (RawLab × ℕ) × ℕ => labAt z.1.1 z.1.2) :=
    polyFun_fst.comp polyFun_labAt
  have hp := (h1.pair h2).comp polyFun_natEq
  exact (((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hp)).comp polyFun_length).of_eq (fun _ => rfl)

/-- All class sizes, one per vertex. Equal sizes are retained for the caller's tie branch. -/
def classSizesRaw (lab : RawLab) : List ℕ :=
  (List.range lab.length).map (fun u => classSizeRaw (lab, u))

@[simp] theorem length_classSizesRaw (lab : RawLab) : (classSizesRaw lab).length = lab.length :=
  by simp [classSizesRaw]

theorem classSizesRaw_spec (lab : RawLab) (u : Fin lab.length) :
    labAt (classSizesRaw lab) u = (labSet lab.length lab u).ncard := by
  simp [classSizesRaw, labAt, u.isLt, classSizeRaw_spec]

theorem polyFun_classSizesRaw : PolyFun classSizesRaw :=
  ((polyFun_id.pair polyFun_rangeLength).comp (PolyFun.mapParam polyFun_classSizeRaw)).of_eq
    (fun _ => rfl)

private theorem foldl_max_le (l : List ℕ) (a m : ℕ) :
    l.foldl max a ≤ m ↔ a ≤ m ∧ ∀ b ∈ l, b ≤ m := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem foldl_max_eq_or_mem (l : List ℕ) (a : ℕ) :
    l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons b l ih =>
      rcases ih (max a b) with he | hm
      · rw [List.foldl_cons, he]
        rcases le_total a b with hab | hba
        · exact Or.inr (by simp [max_eq_right hab])
        · exact Or.inl (max_eq_left hba)
      · exact Or.inr (List.mem_cons_of_mem _ hm)

private theorem polyFun_listMax_split : PolyFun (fun l : List ℕ => l.foldl max 0) := by
  have hf : PolyFun (fun z : ℕ × ℕ => max z.1 z.2) := polyFun_max
  have hacc : ∀ (a : ℕ) (l : List ℕ) (j : ℕ),
      Enc.size ((l.take j).foldl max a) ≤ Enc.size (a, l) := by
    intro a l j
    rcases foldl_max_eq_or_mem (l.take j) a with he | hm
    · rw [he]; exact Combine.size_fst_le _ _
    · exact le_trans (size_mem_le (List.mem_of_mem_take hm)) (Combine.size_snd_le _ _)
  exact (((polyFun_const (0 : ℕ)).pair polyFun_id).comp
    (PolyFun.foldl hf polyBound_id hacc)).of_eq (fun _ => rfl)

/-- The largest class size, without selecting a class of that size. -/
def largestClassSizeRaw (lab : RawLab) : ℕ := (classSizesRaw lab).foldl max 0

/-- This is exactly the largest size: an upper bound holds precisely when every class fits. -/
theorem largestClassSizeRaw_spec (lab : RawLab) (m : ℕ) :
    largestClassSizeRaw lab ≤ m ↔ ∀ u : Fin lab.length, (labSet lab.length lab u).ncard ≤ m := by
  rw [largestClassSizeRaw, foldl_max_le]
  simp only [Nat.zero_le, true_and, classSizesRaw, List.mem_map, List.mem_range]
  constructor
  · intro h u
    rw [← classSizeRaw_spec]
    exact h _ ⟨u, u.isLt, rfl⟩
  · intro h b hb
    obtain ⟨u, hu, rfl⟩ := hb
    exact (classSizeRaw_spec lab u) ▸ h ⟨u, hu⟩

theorem polyFun_largestClassSizeRaw : PolyFun largestClassSizeRaw :=
  polyFun_classSizesRaw.comp polyFun_listMax_split

/-- The generic class-size routine also applies when a caller carries the domain size. -/
theorem classSizeRaw_spec_of_length {n : ℕ} {lab : RawLab} (hlen : lab.length = n) (u : ℕ) :
    classSizeRaw (lab, u) = (labSet n lab u).ncard := by
  subst n
  exact classSizeRaw_spec lab u

/-- Section 9: the sizes read from constituent twin labels count the paper's twin classes. -/
theorem constituentTwinSize_spec {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (c : ℕ) (u : Fin n) :
    classSizeRaw (constituentTwinsRaw (p, c), u) =
      (twinClass (decConstituent n (p, c)).Aut u).ncard := by
  rw [classSizeRaw_spec_of_length (n := n) (by simp [card_eq_length_dom h])]
  congr 1
  ext v
  rw [labSet, Set.mem_setOf_eq, constituentTwinsRaw_spec h]
  exact ⟨fun hv => (twinOrEq_equivalence _).symm hv,
    fun hv => (twinOrEq_equivalence _).symm hv⟩

/-- Section 9.3: count first-part twins, without counting vertices of the other part. -/
theorem bipTwinSize_spec (z : RawBipConstituent) (u : Fin z.2.1.length) :
    classSizeRaw (bipTwinsRaw z, u) =
      {v : Fin z.2.1.length |
        TwinOrEq (decBipConstituent z).Aut (Sum.inl u) (Sum.inl v)}.ncard := by
  rw [classSizeRaw_spec_of_length (length_bipTwinsRaw z)]
  congr 1
  ext v
  rw [labSet, Set.mem_setOf_eq, bipTwinsRaw_spec]
  exact ⟨fun hv => (twinOrEq_equivalence _).symm hv,
    fun hv => (twinOrEq_equivalence _).symm hv⟩

end Algo
