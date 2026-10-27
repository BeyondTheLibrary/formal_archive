import Workspace.Algo.SplitTwins

/-!
# Twins in the second part and transport of twin labels

A least member is a name for a class. After changing vertex names, recompute
that name. The transport statements compare the induced partitions and their
class sizes. For bipartite inputs the part lists carry their orders along, so
their positions and the labels at those positions stay unchanged.
-/

namespace Algo

open Babai RAM

/-- Observation 2.4.28: compare neighborhoods of vertices of the second part. -/
def bipSecondTwinTest (z : RawBipConstituent × (ℕ × ℕ)) : Bool :=
  ((List.range z.1.2.1.length).filter (fun w =>
    decide (bipAdjRaw (z.1, (w, z.2.1)) ≠ bipAdjRaw (z.1, (w, z.2.2))))).isEmpty

theorem bipSecondTwinTest_spec (z : RawBipConstituent) (u v : Fin z.2.2.length) :
    bipSecondTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      TwinOrEq (decBipConstituent z).Aut (Sum.inr u) (Sum.inr v) := by
  have he : bipSecondTwinTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      {w | (w, u) ∈ (decBipConstituent z).E} = {w | (w, v) ∈ (decBipConstituent z).E} := by
    simp only [bipSecondTwinTest, List.isEmpty_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_not, List.mem_range]
    constructor
    · intro h; ext w; exact Bool.eq_iff_iff.1 (h w w.isLt)
    · intro h w hw; exact Bool.eq_iff_iff.2 (Set.ext_iff.1 h ⟨w, hw⟩)
  rw [he]
  by_cases huv : u = v
  · subst v; simp [TwinOrEq]
  · simp only [TwinOrEq, Sum.inr.injEq, huv, false_or]
    exact ((decBipConstituent z).isTwin_inr_iff_aux u v huv).symm

theorem polyFun_bipSecondTwinTest : PolyFun bipSecondTwinTest := by
  let T := RawBipConstituent × (ℕ × ℕ)
  have hc : PolyFun (fun z : T × ℕ => z.1.1) := polyFun_fst.comp polyFun_fst
  have hu : PolyFun (fun z : T × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hv : PolyFun (fun z : T × ℕ => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have ha := (hc.pair (polyFun_snd.pair hu)).comp polyFun_bipAdjRaw
  have hb := (hc.pair (polyFun_snd.pair hv)).comp polyFun_bipAdjRaw
  have hp : PolyFun (fun z : T × ℕ =>
      decide (bipAdjRaw (z.1.1, (z.2, z.1.2.1)) ≠ bipAdjRaw (z.1.1, (z.2, z.1.2.2)))) :=
    (PolyFun.ite ha (PolyFun.ite hb (polyFun_const false) (polyFun_const true)) hb).of_eq
      (fun z => by cases bipAdjRaw (z.1.1, (z.2, z.1.2.1)) <;>
        cases bipAdjRaw (z.1.1, (z.2, z.1.2.2)) <;> rfl)
  exact (((polyFun_id.pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength)).comp
      (PolyFun.filterParam hp)).comp polyFun_isEmpty).of_eq (fun _ => rfl)

/-- Twin classes in the second part, named by least positions. -/
def bipSecondTwinsRaw (z : RawBipConstituent) : RawLab :=
  relationLabRaw bipSecondTwinTest (z, z.2.2)

@[simp] theorem length_bipSecondTwinsRaw (z : RawBipConstituent) :
    (bipSecondTwinsRaw z).length = z.2.2.length := length_relationLabRaw _ _

theorem bipSecondTwinsRaw_spec (z : RawBipConstituent) (u v : Fin z.2.2.length) :
    LabRel (bipSecondTwinsRaw z) u v ↔
      TwinOrEq (decBipConstituent z).Aut (Sum.inr u) (Sum.inr v) := by
  have he := twinOrEq_equivalence (decBipConstituent z).Aut
  exact relationLabRaw_spec (r := fun u v =>
    TwinOrEq (decBipConstituent z).Aut (Sum.inr u) (Sum.inr v)) rfl
    ⟨fun u => he.refl _, fun h => he.symm h, fun h h' => he.trans h h'⟩
    (bipSecondTwinTest_spec z) u v

theorem polyFun_bipSecondTwinsRaw : PolyFun bipSecondTwinsRaw :=
  ((polyFun_id.pair (polyFun_snd.comp polyFun_snd)).comp
    (polyFun_relationLabRaw polyFun_bipSecondTwinTest)).of_eq (fun _ => rfl)

theorem bipSecondTwinSize_spec (z : RawBipConstituent) (u : Fin z.2.2.length) :
    classSizeRaw (bipSecondTwinsRaw z, u) =
      {v : Fin z.2.2.length |
        TwinOrEq (decBipConstituent z).Aut (Sum.inr u) (Sum.inr v)}.ncard := by
  rw [classSizeRaw_spec_of_length (length_bipSecondTwinsRaw z)]
  congr 1
  ext v
  rw [labSet, Set.mem_setOf_eq, bipSecondTwinsRaw_spec]
  exact ⟨fun h => (twinOrEq_equivalence _).symm h, fun h => (twinOrEq_equivalence _).symm h⟩

/-- Equality of labels as a test for `relationLabRaw`. -/
def splitLabTest (z : RawLab × (ℕ × ℕ)) : Bool :=
  decide (labAt z.1 z.2.1 = labAt z.1 z.2.2)

theorem polyFun_splitLabTest : PolyFun splitLabTest :=
  (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_labAt).pair
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_labAt)).comp polyFun_natEq

/-- Recompute least class names for an arbitrary labelling. -/
def splitNormalizeLab (lab : RawLab) : RawLab := relationLabRaw splitLabTest (lab, lab)

@[simp] theorem length_splitNormalizeLab (lab : RawLab) :
    (splitNormalizeLab lab).length = lab.length := length_relationLabRaw _ _

theorem splitNormalizeLab_spec (lab : RawLab) (u v : Fin lab.length) :
    LabRel (splitNormalizeLab lab) u v ↔ LabRel lab u v :=
  relationLabRaw_spec (r := fun u v : Fin lab.length => LabRel lab u v)
    rfl ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    (fun _ _ => by simp [splitLabTest, LabRel]) u v

theorem polyFun_splitNormalizeLab : PolyFun splitNormalizeLab :=
  ((polyFun_id.pair polyFun_id).comp
    (polyFun_relationLabRaw polyFun_splitLabTest)).of_eq (fun _ => rfl)

/-- Pull labels back through the inverse permutation, then recompute their least names. -/
def splitRelabelLabRaw (z : RawPerm × RawLab) : RawLab :=
  splitNormalizeLab ((List.range z.2.length).map
    (fun u => labAt z.2 (rawApply (rawInv z.1, u))))

@[simp] theorem length_splitRelabelLabRaw (z : RawPerm × RawLab) :
    (splitRelabelLabRaw z).length = z.2.length := by simp [splitRelabelLabRaw]

theorem polyFun_splitRelabelLabRaw : PolyFun splitRelabelLabRaw := by
  have hi : PolyFun (fun z : (RawPerm × RawLab) × ℕ => rawApply (rawInv z.1.1, z.2)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_rawInv).pair polyFun_snd).comp polyFun_rawApply
  have hf := ((polyFun_fst.comp polyFun_snd).pair hi).comp polyFun_labAt
  exact (((polyFun_id.pair (polyFun_snd.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam hf)).comp polyFun_splitNormalizeLab).of_eq (fun _ => rfl)

theorem splitRelabelLabRaw_spec {n : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π)
    {lab : RawLab} (hl : lab.length = n) (u v : Fin n) :
    LabRel (splitRelabelLabRaw (π, lab)) (rawApply (π, u)) (rawApply (π, v)) ↔
      LabRel lab u v := by
  let l := (List.range lab.length).map (fun u => labAt lab (rawApply (rawInv π, u)))
  have hu : rawApply (π, u) < l.length := by simp [l, hl]; exact rawApply_lt hπ u.isLt
  have hv : rawApply (π, v) < l.length := by simp [l, hl]; exact rawApply_lt hπ v.isLt
  change LabRel (splitNormalizeLab l) (rawApply (π, u)) (rawApply (π, v)) ↔ _
  rw [splitNormalizeLab_spec l ⟨_, hu⟩ ⟨_, hv⟩]
  have hi (w : Fin n) : rawApply (rawInv π, rawApply (π, w)) = (w : ℕ) := by
    rw [rawInv_of_wf hπ, rawApply_of_wf hπ w.isLt, rawApply_encPerm _ _ (Fin.isLt _)]
    simp
  simp [LabRel, labAt, l, hl, rawApply_lt hπ u.isLt, rawApply_lt hπ v.isLt, hi]

private theorem splitTwinOrEq_iff_swap {V : Type*} [DecidableEq V]
    (G : Subgroup (Equiv.Perm V)) (u v : V) : TwinOrEq G u v ↔ Equiv.swap u v ∈ G := by
  by_cases h : u = v
  · subst v
    exact ⟨fun _ => by simpa only [Equiv.swap_self] using G.one_mem, fun _ => Or.inl rfl⟩
  · simp [TwinOrEq, IsTwin, h]

/-- Twins are preserved by the given vertex bijection of two digraphs. -/
theorem splitDigraphTwins_congr {V W : Type*} [DecidableEq V] [DecidableEq W]
    (Y : Digraph V) (Z : Digraph W) (e : V ≃ W)
    (he : ∀ a b, (e a, e b) ∈ Z.E ↔ (a, b) ∈ Y.E) (u v : V) :
    TwinOrEq Z.Aut (e u) (e v) ↔ TwinOrEq Y.Aut u v := by
  rw [splitTwinOrEq_iff_swap, splitTwinOrEq_iff_swap, Digraph.mem_aut, Digraph.mem_aut]
  constructor
  · intro h a b
    have hh := h (e a) (e b)
    rwa [← e.injective.map_swap, ← e.injective.map_swap, he, he] at hh
  · intro h a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← e.injective.map_swap, ← e.injective.map_swap, he, he]
    exact h a b

/-- Constituent twin partitions commute with a change of vertex names. -/
theorem constituentTwinsRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (c : ℕ) (u v : Fin n) :
    LabRel (constituentTwinsRaw (relabelWL (π, p), c))
        (rawApply (π, u)) (rawApply (π, v)) ↔ LabRel (constituentTwinsRaw (p, c)) u v := by
  rw [rawApply_of_wf hπ u.isLt, rawApply_of_wf hπ v.isLt,
    constituentTwinsRaw_spec (relabelWL_wf hπ hp), constituentTwinsRaw_spec hp]
  apply splitDigraphTwins_congr _ _ (decPerm n π)
  intro a b
  have he := binColor_relabel hp hπ a.isLt b.isLt
  rw [rawApply_of_wf hπ a.isLt, rawApply_of_wf hπ b.isLt] at he
  change binColor _ = c ↔ binColor _ = c
  rw [he]

/-- Class sizes transport along any given equivalence preserving the label relation. -/
theorem splitClassSize_congr {n m : ℕ} {l k : RawLab} (hl : l.length = n)
    (hk : k.length = m) (e : Fin n ≃ Fin m)
    (he : ∀ u v, LabRel k (e u) (e v) ↔ LabRel l u v) (u : Fin n) :
    classSizeRaw (k, e u) = classSizeRaw (l, u) := by
  rw [classSizeRaw_spec_of_length hk, classSizeRaw_spec_of_length hl]
  have himg : e '' labSet n l u = labSet m k (e u) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (he w u).2 hw
    · intro hv
      exact ⟨e.symm v, (he (e.symm v) u).1 (by simpa using hv), by simp⟩
  rw [← himg, Set.ncard_image_of_injective _ e.injective]

theorem constituentTwinSize_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (c : ℕ) (u : Fin n) :
    classSizeRaw (constituentTwinsRaw (relabelWL (π, p), c), rawApply (π, u)) =
      classSizeRaw (constituentTwinsRaw (p, c), u) := by
  rw [rawApply_of_wf hπ u.isLt]
  apply splitClassSize_congr (by simp [card_eq_length_dom hp])
    (by simp [card_eq_length_dom hp]) (decPerm n π)
  intro a b
  simpa only [rawApply_of_wf hπ a.isLt, rawApply_of_wf hπ b.isLt] using
    constituentTwinsRaw_relabel hp hπ c a b

/-- Transport the ambient vertex names, keeping the positions in both part lists. -/
def splitRelabelBipRaw (z : RawPerm × RawBipConstituent) : RawBipConstituent :=
  ((relabelWL (z.1, z.2.1.1), z.2.1.2), (permList z.1 z.2.2.1, permList z.1 z.2.2.2))

theorem polyFun_splitPermList : PolyFun (fun z : RawPerm × List ℕ => permList z.1 z.2) :=
  (PolyFun.mapParam polyFun_rawApply).of_eq (fun _ => rfl)

theorem polyFun_splitRelabelWL : PolyFun relabelWL := by
  have hi : PolyFun (fun z : RawPerm × (List ℕ × ℕ) => (permList z.1 z.2.1, z.2.2)) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_splitPermList).pair
      (polyFun_snd.comp polyFun_snd))
  have ht : PolyFun (fun z : RawPerm × RawWL =>
      z.2.2.map (fun q => (permList z.1 q.1, q.2))) :=
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp
      (PolyFun.mapParam hi)).of_eq (fun _ => rfl)
  exact (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp
    polyFun_splitPermList).pair ht).of_eq (fun _ => rfl)

theorem polyFun_splitRelabelBipRaw : PolyFun splitRelabelBipRaw := by
  have hp : PolyFun (fun z : RawPerm × RawBipConstituent => relabelWL (z.1, z.2.1.1)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).comp
      polyFun_splitRelabelWL
  have hl : PolyFun (fun z : RawPerm × RawBipConstituent => permList z.1 z.2.2.1) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp
      polyFun_splitPermList
  have hr : PolyFun (fun z : RawPerm × RawBipConstituent => permList z.1 z.2.2.2) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp
      polyFun_splitPermList
  exact ((hp.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_snd)).pair
    (hl.pair hr)).of_eq (fun _ => rfl)

@[simp] theorem splitRelabelBipRaw_left_length (π : RawPerm) (z : RawBipConstituent) :
    (splitRelabelBipRaw (π, z)).2.1.length = z.2.1.length := by simp [splitRelabelBipRaw]

@[simp] theorem splitRelabelBipRaw_right_length (π : RawPerm) (z : RawBipConstituent) :
    (splitRelabelBipRaw (π, z)).2.2.length = z.2.2.length := by simp [splitRelabelBipRaw]

/-- The two part lists name the same adjacency after the ambient names are changed. -/
theorem bipAdjRaw_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n)
    {u v : ℕ} (hu : u < z.2.1.length) (hv : v < z.2.2.length) :
    bipAdjRaw (splitRelabelBipRaw (π, z), (u, v)) = bipAdjRaw (z, (u, v)) := by
  have hread (l : List ℕ) (i : ℕ) (hi : i < l.length) :
      labAt (permList π l) i = rawApply (π, labAt l i) := by simp [labAt, permList, hi]
  have hul : labAt z.2.1 u < n := by
    rw [labAt, List.getD_eq_getElem _ _ hu]; exact hl _ (List.getElem_mem _)
  have hvr : labAt z.2.2 v < n := by
    rw [labAt, List.getD_eq_getElem _ _ hv]; exact hr _ (List.getElem_mem _)
  simp only [bipAdjRaw, splitRelabelBipRaw, hread _ _ hu, hread _ _ hv, constituentAdj,
    binColor_relabel hp hπ hul hvr]

/-- Equal tests on the named positions give equal normalized labels. -/
theorem splitRelationLab_congr {A B : Type*} {f : A × (ℕ × ℕ) → Bool}
    {g : B × (ℕ × ℕ) → Bool} {a : A} {b : B} {dom dom' : List ℕ}
    (hlen : dom.length = dom'.length)
    (he : ∀ u < dom.length, ∀ v < dom.length, f (a, (u, v)) = g (b, (u, v))) :
    relationLabRaw f (a, dom) = relationLabRaw g (b, dom') := by
  unfold relationLabRaw
  rw [← hlen]
  apply List.map_congr_left
  intro u hu
  unfold relationRepRaw relationClassRaw
  rw [← hlen]
  congr 1
  apply List.filter_congr
  intro v hv
  exact he u (List.mem_range.1 hu) v (List.mem_range.1 hv)

theorem bipTwinTest_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n)
    {u v : ℕ} (hu : u < z.2.1.length) (hv : v < z.2.1.length) :
    bipTwinTest (splitRelabelBipRaw (π, z), (u, v)) = bipTwinTest (z, (u, v)) := by
  unfold bipTwinTest
  rw [splitRelabelBipRaw_right_length]
  congr 1
  apply List.filter_congr
  intro w hw
  rw [bipAdjRaw_relabel hp hπ hl hr hu (List.mem_range.1 hw),
    bipAdjRaw_relabel hp hπ hl hr hv (List.mem_range.1 hw)]

theorem bipSecondTwinTest_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n)
    {u v : ℕ} (hu : u < z.2.2.length) (hv : v < z.2.2.length) :
    bipSecondTwinTest (splitRelabelBipRaw (π, z), (u, v)) = bipSecondTwinTest (z, (u, v)) := by
  unfold bipSecondTwinTest
  rw [splitRelabelBipRaw_left_length]
  congr 1
  apply List.filter_congr
  intro w hw
  rw [bipAdjRaw_relabel hp hπ hl hr (List.mem_range.1 hw) hu,
    bipAdjRaw_relabel hp hπ hl hr (List.mem_range.1 hw) hv]

/-- In the transported part lists every first-part label stays at the same position. -/
theorem bipTwinsRaw_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n) :
    bipTwinsRaw (splitRelabelBipRaw (π, z)) = bipTwinsRaw z := by
  apply splitRelationLab_congr (splitRelabelBipRaw_left_length π z)
  intro u hu v hv
  rw [splitRelabelBipRaw_left_length] at hu hv
  exact bipTwinTest_relabel hp hπ hl hr hu hv

/-- The same equality holds for second-part labels. -/
theorem bipSecondTwinsRaw_relabel {n : ℕ} {z : RawBipConstituent} {π : RawPerm}
    (hp : RawWL.WF n 2 z.1.1) (hπ : RawPerm.WF n π)
    (hl : ∀ a ∈ z.2.1, a < n) (hr : ∀ b ∈ z.2.2, b < n) :
    bipSecondTwinsRaw (splitRelabelBipRaw (π, z)) = bipSecondTwinsRaw z := by
  apply splitRelationLab_congr (splitRelabelBipRaw_right_length π z)
  intro u hu v hv
  rw [splitRelabelBipRaw_right_length] at hu hv
  exact bipSecondTwinTest_relabel hp hπ hl hr hu hv

end Algo
