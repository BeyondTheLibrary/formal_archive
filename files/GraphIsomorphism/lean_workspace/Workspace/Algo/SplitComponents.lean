import Workspace.Algo.SplitTwins
import Workspace.Coherent.Constituents
import Workspace.SplitOrJohnson.BlockSystem

/-!
# Components of a constituent

To use `closeLab`, add one fixed point and merge it with a starting vertex.
Swaps along the edges then merge precisely the vertices reachable from that
vertex with the fixed point. The final labels are least members of components.
All loops are bounded by list lengths, also on malformed input.
-/

namespace Algo

open Babai RAM

/-- A transposition on the positions of a supplied domain list. -/
def splitSwapRaw (z : List ℕ × (ℕ × ℕ)) : RawPerm :=
  (List.range z.1.length).map (fun w => swapPointRaw (z.2, w))

theorem splitSwapRaw_enc (dom : List ℕ) (a b : Fin dom.length) :
    splitSwapRaw (dom, ((a : ℕ), (b : ℕ))) = encPerm dom.length (Equiv.swap a b) := by
  apply List.ext_getElem
  · simp [splitSwapRaw, encPerm]
  · intro i hi hi'
    have hi0 : i < dom.length := by simpa [splitSwapRaw] using hi
    simpa [splitSwapRaw, encPerm] using swapPointRaw_spec a b ⟨i, hi0⟩

theorem splitSwapRaw_apply (dom : List ℕ) (a b w : ℕ) (hw : w < dom.length) :
    rawApply (splitSwapRaw (dom, (a, b)), w) = swapPointRaw ((a, b), w) := by
  simp [rawApply, splitSwapRaw, hw]

theorem polyFun_splitSwapRaw : PolyFun splitSwapRaw := by
  have hf : PolyFun (fun z : (List ℕ × (ℕ × ℕ)) × ℕ => swapPointRaw (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_swapPointRaw
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

/-- Edges in position order. Only names below the domain size are used. -/
def splitEdgesRaw (z : RawConfig × ℕ) : List (ℕ × ℕ) :=
  (labPairsList z.1.1).filter (fun q => constituentAdj (z, q))

theorem mem_splitEdgesRaw (z : RawConfig × ℕ) (a b : ℕ) :
    (a, b) ∈ splitEdgesRaw z ↔
      a < z.1.1.length ∧ b < z.1.1.length ∧ binColor (z.1, (a, b)) = z.2 := by
  simp [splitEdgesRaw, mem_labPairsList, constituentAdj, and_assoc]

theorem polyFun_splitEdgesRaw : PolyFun splitEdgesRaw :=
  ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_labPairsList)).comp
    (PolyFun.filterParam polyFun_constituentAdj)).of_eq (fun _ => rfl)

/-- Add a fixed point at position `n`, then swap the endpoints of each edge. -/
def splitEdgeGensRaw (z : RawConfig × ℕ) : RawGens :=
  (splitEdgesRaw z).map (fun q => splitSwapRaw (0 :: z.1.1, q))

theorem splitEdgeGensRaw_wf (z : RawConfig × ℕ) :
    RawGens.WF (z.1.1.length + 1) (splitEdgeGensRaw z) := by
  intro g hg
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hg
  obtain ⟨ha, hb, _⟩ := (mem_splitEdgesRaw z a b).1 hab
  have ha' : a < (0 :: z.1.1).length := by simp; omega
  have hb' : b < (0 :: z.1.1).length := by simp; omega
  rw [splitSwapRaw_enc _ ⟨a, ha'⟩ ⟨b, hb'⟩]
  exact wf_encPerm _ _

theorem polyFun_splitEdgeGensRaw : PolyFun splitEdgeGensRaw := by
  have hd : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × ℕ) => 0 :: z.1.1.1) :=
    ((polyFun_const (0 : ℕ)).pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).comp polyFun_cons
  exact ((polyFun_id.pair polyFun_splitEdgesRaw).comp
    (PolyFun.mapParam ((hd.pair polyFun_snd).comp polyFun_splitSwapRaw))).of_eq (fun _ => rfl)

/-- The class of the extra fixed point is the component of the starting vertex. -/
def splitReachLabRaw (z : (RawConfig × ℕ) × ℕ) : RawLab :=
  closeLab ((splitEdgeGensRaw z.1, 0 :: z.1.1.1),
    mergeLab (List.range (0 :: z.1.1.1).length, (z.2, z.1.1.1.length)))

theorem polyFun_splitReachLabRaw : PolyFun splitReachLabRaw := by
  have hd : PolyFun (fun z : (RawConfig × ℕ) × ℕ => 0 :: z.1.1.1) :=
    ((polyFun_const (0 : ℕ)).pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).comp polyFun_cons
  have hn : PolyFun (fun z : (RawConfig × ℕ) × ℕ => z.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hm := ((hd.comp polyFun_rangeLength).pair (polyFun_snd.pair hn)).comp polyFun_mergeLab
  exact ((((polyFun_fst.comp polyFun_splitEdgeGensRaw).pair hd).pair hm).comp
    polyFun_closeLab).of_eq (fun _ => rfl)

private theorem splitSwap_pred {P : ℕ → Prop} {a b : ℕ} (hab : P a ↔ P b) (w : ℕ) :
    P (swapPointRaw ((a, b), w)) ↔ P w := by
  by_cases hwa : w = a
  · subst w; simpa [swapPointRaw] using hab.symm
  · by_cases hwb : w = b
    · subst w; simpa [swapPointRaw, hwa] using hab
    · simp [swapPointRaw, hwa, hwb]

/-- The closure computes weak accessibility, including isolated vertices. -/
theorem splitReachLabRaw_spec (z : RawConfig × ℕ) (u v : Fin z.1.1.length) :
    LabRel (splitReachLabRaw (z, u)) z.1.1.length v ↔
      (decConstituent z.1.1.length z).WeaklyAccessible u v := by
  let n := z.1.1.length
  let Y := decConstituent n z
  let L := splitReachLabRaw (z, u)
  have hlen : n + 1 ≤ (mergeLab (List.range (0 :: z.1.1).length,
      ((u : ℕ), n))).length := by simp [n]
  have hclosed : LabClosed (n + 1) (splitEdgeGensRaw z) L :=
    closeLab_closed (splitEdgeGensRaw_wf z) rfl hlen
  have hseed : LabRel L u n := closeLab_mono (by simp) (by simp [n])
    (labRel_mergeLab_pair _ (by simp) (by simp))
  have hswap (a b : Fin n) (hab : Y.Adj a b) :
      (LabRel L n a ↔ LabRel L n b) := by
    have hm : splitSwapRaw (0 :: z.1.1, ((a : ℕ), (b : ℕ))) ∈ splitEdgeGensRaw z :=
      List.mem_map.2 ⟨_, (mem_splitEdgesRaw _ _ _).2 ⟨a.isLt, b.isLt, hab⟩, rfl⟩
    have hn : n < (0 :: z.1.1).length := by simp [n]
    have ha : (a : ℕ) < (0 :: z.1.1).length := by simp; omega
    have hb : (b : ℕ) < (0 :: z.1.1).length := by simp; omega
    constructor
    · intro h
      have ht := hclosed _ hm n hn a ha h
      simpa [splitSwapRaw_apply _ _ _ _ hn, splitSwapRaw_apply _ _ _ _ ha,
        swapPointRaw, show n ≠ (a : ℕ) by omega, show n ≠ (b : ℕ) by omega] using ht
    · intro h
      have ht := hclosed _ hm n hn b hb h
      by_cases he : b = a
      · simpa [he] using h
      · simpa [splitSwapRaw_apply _ _ _ _ hn, splitSwapRaw_apply _ _ _ _ hb,
          swapPointRaw, show n ≠ (a : ℕ) by omega, show n ≠ (b : ℕ) by omega,
          show (b : ℕ) ≠ (a : ℕ) from fun h => he (Fin.ext h)] using ht
  constructor
  · intro hv
    let P : ℕ → Prop := fun w => w = n ∨ ∃ t : Fin n, w = (t : ℕ) ∧ Y.WeaklyAccessible u t
    have he (a b : Fin n) (hab : Y.Adj a b) : P a ↔ P b := by
      have hc := Y.symmetrization.accessible_of_adj (Or.inl hab)
      have hcs := Y.symmetrization.accessible_symm Y.symmetrization_adj_symm hc
      have hp (a : Fin n) : P a ↔ Y.WeaklyAccessible u a := by
        simp only [P, show (a : ℕ) ≠ n by omega, false_or]
        constructor
        · rintro ⟨t, ht, h⟩; exact Fin.ext ht ▸ h
        · intro h; exact ⟨a, rfl, h⟩
      rw [hp, hp]
      exact ⟨fun h => Y.symmetrization.accessible_trans h hc,
        fun h => Y.symmetrization.accessible_trans h hcs⟩
    have hc : CongrOn (n + 1) (splitEdgeGensRaw z) (fun a b => P a ↔ P b) := by
      refine ⟨Iff.symm, Iff.trans, ?_⟩
      intro g hg a ha b hb hab
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := List.mem_map.1 hg
      obtain ⟨hs, ht, hedge⟩ := (mem_splitEdgesRaw _ _ _).1 hst
      rw [splitSwapRaw_apply _ _ _ _ ha, splitSwapRaw_apply _ _ _ _ hb]
      have hst' := he ⟨s, hs⟩ ⟨t, ht⟩ hedge
      exact (splitSwap_pred hst' a).trans (hab.trans (splitSwap_pred hst' b).symm)
    have hi : ∀ a < n + 1, ∀ b < n + 1,
        LabRel (List.range (n + 1)) a b → (P a ↔ P b) := by
      intro a ha b hb hab
      rw [LabRel, labAt_range ha, labAt_range hb] at hab
      rw [hab]
    have hp : P u ↔ P n :=
      iff_of_true (Or.inr ⟨u, rfl, Y.symmetrization.accessible_refl u⟩) (Or.inl rfl)
    have hleast := closeLab_least (dom := 0 :: z.1.1) hc (splitEdgeGensRaw_wf z) rfl hlen
      (mergeLab_least hc.symm hc.trans hi hp (by omega) (by omega) (by simp [n]))
    have hpv : P v := (hleast n (by omega) v (by omega) hv).mp (Or.inl rfl)
    rcases hpv with hbad | ⟨t, ht, h⟩
    · exact False.elim (by omega)
    · exact Fin.ext ht ▸ h
  · intro h
    exact (Y.weaklyAccessible_rel (r := fun a b => LabRel L n a ↔ LabRel L n b)
      (fun _ => Iff.rfl) Iff.symm Iff.trans hswap h).mp (Eq.symm hseed)

/-- Test whether two vertices are in the same weak component. -/
def splitComponentTest (z : (RawConfig × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (labAt (splitReachLabRaw (z.1, z.2.1)) z.1.1.1.length =
    labAt (splitReachLabRaw (z.1, z.2.1)) z.2.2)

theorem splitComponentTest_spec (z : RawConfig × ℕ) (u v : Fin z.1.1.length) :
    splitComponentTest (z, ((u : ℕ), (v : ℕ))) = true ↔
      (decConstituent z.1.1.length z).WeaklyAccessible u v := by
  simpa [splitComponentTest, LabRel] using splitReachLabRaw_spec z u v

theorem polyFun_splitComponentTest : PolyFun splitComponentTest := by
  have hl : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × ℕ) =>
      splitReachLabRaw (z.1, z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_splitReachLabRaw
  have hn : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × ℕ) => z.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  exact (((hl.pair hn).comp polyFun_labAt).pair
    ((hl.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_labAt)).comp polyFun_natEq

/-- Definition 2.4.21: component labels, normalized by their least members. -/
def componentsRaw (z : RawConfig × ℕ) : RawLab :=
  relationLabRaw splitComponentTest (z, z.1.1)

@[simp] theorem length_componentsRaw (z : RawConfig × ℕ) :
    (componentsRaw z).length = z.1.1.length := length_relationLabRaw _ _

theorem componentsRaw_spec (z : RawConfig × ℕ) (u v : Fin z.1.1.length) :
    LabRel (componentsRaw z) u v ↔
      (decConstituent z.1.1.length z).WeaklyAccessible u v := by
  let Y := decConstituent z.1.1.length z
  exact relationLabRaw_spec rfl
    ⟨Y.symmetrization.accessible_refl, Y.symmetrization.accessible_symm Y.symmetrization_adj_symm,
      Y.symmetrization.accessible_trans⟩ (splitComponentTest_spec z) u v

theorem polyFun_componentsRaw : PolyFun componentsRaw :=
  ((polyFun_id.pair (polyFun_fst.comp polyFun_fst)).comp
    (polyFun_relationLabRaw polyFun_splitComponentTest)).of_eq (fun _ => rfl)

theorem componentsRaw_spec_of_length {n : ℕ} {z : RawConfig × ℕ}
    (hlen : z.1.1.length = n) (u v : Fin n) :
    LabRel (componentsRaw z) u v ↔ (decConstituent n z).WeaklyAccessible u v := by
  subst n
  exact componentsRaw_spec z u v

/-- Sections 9.4 and 9.6 use weak components of `colorDigraph`. The raw labels
give exactly those components before any renaming of colors by `decConfig`. -/
theorem componentsRaw_color_spec {n : ℕ} {p : RawConfig} (hp : RawWL.WF n 2 p)
    (c : ℕ) (u v : Fin n) :
    LabRel (componentsRaw (p, c)) u v ↔
      v ∈ (colorDigraph (fun a b : Fin n => binColor (p, ((a : ℕ), (b : ℕ)))) c).weakComponent u := by
  rw [componentsRaw_spec_of_length (card_eq_length_dom hp),
    Digraph.weakComponent_eq_weaklyAccessible]
  rfl

/-- Proposition 3.4.1: for a homogeneous constituent these are its strong components,
the notion used by the imprimitive branch of Section 9. -/
theorem componentsRaw_strong_spec {n : ℕ} {p : RawConfig} (hp : RawWL.WF n 2 p)
    (hc : (decConfig n p).IsCoherent) (a b u v : Fin n)
    (hh : (decConfig n p).tailColor ((decConfig n p).color a b) =
      (decConfig n p).headColor ((decConfig n p).color a b)) :
    LabRel (componentsRaw (p, binColor (p, ((a : ℕ), (b : ℕ))))) u v ↔
      v ∈ ((decConfig n p).extConstituent ((decConfig n p).color a b)).strongComponent u := by
  have he : decConstituent n (p, binColor (p, ((a : ℕ), (b : ℕ)))) =
      (decConfig n p).extConstituent ((decConfig n p).color a b) := by
    apply congrArg Digraph.mk
    ext q
    exact decConstituent_spec p a b q.1 q.2
  rw [componentsRaw_spec_of_length (card_eq_length_dom hp), he]
  rw [← (decConfig n p).weak_is_strong hc _ hh u,
    Digraph.weakComponent_eq_weaklyAccessible]
  rfl

/-- A map preserving directed edges carries weak walks to weak walks. -/
theorem splitWeaklyAccessible_map {V W : Type*} {Y : Digraph V} {Z : Digraph W}
    (f : V → W) (hf : ∀ a b, Y.Adj a b → Z.Adj (f a) (f b))
    {u v : V} (h : Y.WeaklyAccessible u v) : Z.WeaklyAccessible (f u) (f v) := by
  obtain ⟨t, w, hw, h0, ht⟩ := h
  refine ⟨t, fun i => f (w i), ?_, congrArg f h0, congrArg f ht⟩
  intro i
  rcases hw i with h | h
  · exact Or.inl (hf _ _ h)
  · exact Or.inr (hf _ _ h)

/-- Component partitions commute with a change of vertex names. Their least labels
are recomputed, so the statement compares label equality. -/
theorem componentsRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (c : ℕ) (u v : Fin n) :
    LabRel (componentsRaw (relabelWL (π, p), c))
        (rawApply (π, u)) (rawApply (π, v)) ↔ LabRel (componentsRaw (p, c)) u v := by
  rw [rawApply_of_wf hπ u.isLt, rawApply_of_wf hπ v.isLt,
    componentsRaw_spec_of_length (card_eq_length_dom (relabelWL_wf hπ hp)),
    componentsRaw_spec_of_length (card_eq_length_dom hp)]
  let e := decPerm n π
  let Y := decConstituent n (p, c)
  let Z := decConstituent n (relabelWL (π, p), c)
  have he (a b : Fin n) : Z.Adj (e a) (e b) ↔ Y.Adj a b := by
    have hh := binColor_relabel hp hπ a.isLt b.isLt
    rw [rawApply_of_wf hπ a.isLt, rawApply_of_wf hπ b.isLt] at hh
    change binColor _ = c ↔ binColor _ = c
    rw [hh]
  constructor
  · intro h
    have hh := splitWeaklyAccessible_map e.symm (Y := Z) (Z := Y)
      (fun a b hab => (he (e.symm a) (e.symm b)).1 (by simpa using hab)) h
    simpa [e, Y] using hh
  · exact splitWeaklyAccessible_map e (fun a b h => (he a b).2 h)

/-- Every component label names its least member. -/
theorem componentsRaw_label_spec (z : RawConfig × ℕ) (u : Fin z.1.1.length) :
    ∃ w : Fin z.1.1.length, labAt (componentsRaw z) u = (w : ℕ) ∧
      (decConstituent z.1.1.length z).WeaklyAccessible u w ∧
      ∀ v : Fin z.1.1.length, (decConstituent z.1.1.length z).WeaklyAccessible u v →
        (w : ℕ) ≤ (v : ℕ) := by
  let Y := decConstituent z.1.1.length z
  exact relationLabRaw_label_spec rfl
    ⟨Y.symmetrization.accessible_refl, Y.symmetrization.accessible_symm Y.symmetrization_adj_symm,
      Y.symmetrization.accessible_trans⟩ (splitComponentTest_spec z) u

end Algo
