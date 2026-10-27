import Workspace.Algo.SplitTwinTransport
import Workspace.Algo.Naming
import Workspace.SplitOrJohnson.Minor

/-!
# Lemma 9.3.1: one individualized vertex on raw data

The threshold is a pair of naturals `(a,b)`, interpreted as `a / b`.
The specification assumes `b > 0`. Every routine is total on raw data.
Vertex lists retain their input order, so filtering a cell commutes with
transport of the names. Color labels are never used as loop bounds.
-/

namespace Algo

open Babai RAM

/-- Section 9.3: the binary table and the numerator and denominator of the threshold. -/
abbrev RawUpcc := RawConfig × (ℕ × ℕ)

/-- Section 9.3: the cell of color `k` at the individualized vertex `x`. -/
def upccCellRaw (z : (RawConfig × ℕ) × ℕ) : List ℕ :=
  z.1.1.1.filter (fun y => decide (binColor (z.1.1, (z.1.2, y)) = z.2))

/-- Section 9.3: cell colors indexed by ambient vertex name. -/
def upccCellsRaw (z : RawConfig × ℕ) : RawLab :=
  (List.range z.1.1.length).map (fun y => binColor (z.1, (z.2, y)))

@[simp] theorem length_upccCellsRaw (z : RawConfig × ℕ) :
    (upccCellsRaw z).length = z.1.1.length := by simp [upccCellsRaw]

theorem upccCellsRaw_get {n : ℕ} {p : RawConfig} (h : RawWL.WF n 2 p)
    (x y : Fin n) :
    labAt (upccCellsRaw (p, x)) y = binColor (p, (x, y)) := by
  simp [labAt, upccCellsRaw, card_eq_length_dom h, y.isLt]

theorem polyFun_upccCellRaw : PolyFun upccCellRaw := by
  have hc : PolyFun (fun z : ((RawConfig × ℕ) × ℕ) × ℕ =>
      binColor (z.1.1.1, (z.1.1.2, z.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd)).comp
        polyFun_binColor
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).comp
    (PolyFun.filterParam ((hc.pair (polyFun_fst.comp polyFun_snd)).comp
      polyFun_natEq))).of_eq (fun _ => rfl)

theorem polyFun_upccCellsRaw : PolyFun upccCellsRaw := by
  have hc : PolyFun (fun z : (RawConfig × ℕ) × ℕ =>
      binColor (z.1.1, (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_binColor
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.mapParam hc)).of_eq (fun _ => rfl)

section Naming

variable {Ω : Type} {s : Set Ω} {n : ℕ} {p : RawConfig}
    {c : ↥s → ↥s → ℕ}

/-- The naming convention of `Algo/Naming.lean`, applied to a binary color table. -/
def UpccNames (e : ↥s ≃ Fin n) (p : RawConfig) (c : ↥s → ↥s → ℕ) : Prop :=
  ∀ u v, binColor (p, (e u, e v)) = c u v

theorem upccCellRaw_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x y : ↥s) (k : ℕ) :
    (e y : ℕ) ∈ upccCellRaw ((p, e x), k) ↔ y ∈ cellOf c x k := by
  simp [upccCellRaw, mem_dom h (e y), he x y, cellOf]

theorem upccCellsRaw_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x y : ↥s) :
    labAt (upccCellsRaw (p, e x)) (e y) = (cellPartition c x).color y := by
  rw [upccCellsRaw_get h, he x y]
  rfl

theorem upccCellsRaw_blocks (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x y z : ↥s) :
    LabRel (upccCellsRaw (p, e x)) (e y) (e z) ↔
      y ∈ (cellPartition c x).block z := by
  rw [LabRel, upccCellsRaw_get h, upccCellsRaw_get h, he x y, he x z]
  rfl

theorem upccNaming_card (e : ↥s ≃ Fin n) : s.ncard = n := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fin]

theorem upccCellRaw_size (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x : ↥s) (k : ℕ) :
    (upccCellRaw ((p, e x), k)).length = (cellOf c x k).ncard := by
  have himg : e '' cellOf c x k =
      {v : Fin n | (v : ℕ) ∈ p.1 ∧
        decide (binColor (p, (e x, v)) = k) = true} := by
    ext v
    simp only [Equiv.image_eq_preimage_symm, Set.mem_preimage, cellOf,
      Set.mem_setOf_eq, decide_eq_true_eq, mem_dom h v, true_and]
    rw [← he x (e.symm v), e.apply_symm_apply]
  rw [← Set.ncard_image_of_injective (cellOf c x k) e.injective, himg]
  exact (ncard_eq_length_filter p.1 h.domNodup (fun a ha => (h.domMem a).1 ha)
    (fun v => decide (binColor (p, (e x, v)) = k))).symm

end Naming

/-- The exact integer form of the strict big-cell test. -/
def upccCellBig (z : (RawUpcc × ℕ) × ℕ) : Bool :=
  decide (z.1.1.2.1 * z.1.1.1.1.length + 1 ≤
    z.1.1.2.2 * (upccCellRaw ((z.1.1.1, z.1.2), z.2)).length)

theorem polyFun_upccCellBig : PolyFun upccCellBig := by
  have hp : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have ha : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hb : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.2.2) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd
  have hd := (((hp.pair (polyFun_fst.comp polyFun_snd)).pair polyFun_snd).comp
    polyFun_upccCellRaw).comp polyFun_length
  exact ((ha.mul ((hp.comp polyFun_fst).comp polyFun_length)).add
    (polyFun_const 1)).le (hb.mul hd)

/-- All realized colors passing the big-cell test, in vertex-list order.
Repeated colors are retained. When the threshold is at least one half, all
entries are the same color. -/
def upccBigColors (z : RawUpcc × ℕ) : List ℕ :=
  (z.1.1.1.map (fun y => binColor (z.1.1, (z.2, y)))).filter
    (fun k => upccCellBig (z, k))

/-- Section 9.3: all cells are small exactly when no realized color passes the test. -/
def upccCellSmall (z : RawUpcc × ℕ) : Bool := (upccBigColors z).isEmpty

/-- Section 9.3: the big color, or `none` when all cells are small. -/
def upccBigColor (z : RawUpcc × ℕ) : Option ℕ := (upccBigColors z)[0]?

theorem polyFun_upccBigColors : PolyFun upccBigColors := by
  have hc : PolyFun (fun z : (RawUpcc × ℕ) × ℕ =>
      binColor (z.1.1.1, (z.1.2, z.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_binColor
  have hm := (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).comp
    (PolyFun.mapParam hc)
  exact ((polyFun_id.pair hm).comp (PolyFun.filterParam polyFun_upccCellBig)).of_eq
    (fun _ => rfl)

theorem polyFun_upccCellSmall : PolyFun upccCellSmall :=
  polyFun_upccBigColors.comp polyFun_isEmpty

theorem polyFun_upccBigColor : PolyFun upccBigColor :=
  (polyFun_upccBigColors.pair (polyFun_const 0)).comp polyFun_getElem?

section BigSpec

variable {Ω : Type} [Fintype Ω] {s : Set Ω} {n a b : ℕ} {p : RawConfig}
    {c : ↥s → ↥s → ℕ}

omit [Fintype Ω] in
theorem upccCellBig_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (hb : 0 < b) (x : ↥s) (k : ℕ) :
    upccCellBig (((p, (a,b)), e x), k) = true ↔
      (a : ℝ) / b * s.ncard < ((cellOf c x k).ncard : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [upccCellBig, decide_eq_true_eq, Nat.succ_le_iff,
    upccCellRaw_size h e he, card_eq_length_dom h, upccNaming_card e]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hbR]
  norm_cast
  rw [Nat.mul_comm b]

theorem upccBigColors_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (hb : 0 < b) (x : ↥s) (k : ℕ) :
    k ∈ upccBigColors ((p, (a,b)), e x) ↔
      (a : ℝ) / b * s.ncard < ((cellOf c x k).ncard : ℝ) := by
  simp only [upccBigColors, List.mem_filter, upccCellBig_spec h e he hb]
  constructor
  · exact And.right
  · intro hk
    have hpos : 0 < (cellOf c x k).ncard := by
      have : (0 : ℝ) ≤ (a : ℝ) / b * s.ncard := by positivity
      have : (0 : ℝ) < (cellOf c x k).ncard := lt_of_le_of_lt this hk
      exact_mod_cast this
    obtain ⟨y, hy⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    exact ⟨List.mem_map.2 ⟨e y, mem_dom h (e y), (he x y).trans hy⟩, hk⟩

theorem upccCellSmall_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (hb : 0 < b) (x : ↥s) :
    upccCellSmall ((p, (a,b)), e x) = true ↔
      ∀ k, ((cellOf c x k).ncard : ℝ) ≤ (a : ℝ) / b * s.ncard := by
  simp only [upccCellSmall, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
    upccBigColors_spec h e he hb, not_lt]

/-- The selected color passes the paper's strict test. No equality to a
`Classical.choose` witness is required. -/
theorem upccBigColor_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (hb : 0 < b) (x : ↥s) {k : ℕ}
    (hk : upccBigColor ((p, (a,b)), e x) = some k) :
    (a : ℝ) / b * s.ncard < ((cellOf c x k).ncard : ℝ) :=
  (upccBigColors_spec h e he hb x k).1 (List.mem_of_getElem? hk)

end BigSpec

theorem upccCellRaw_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k : ℕ) :
    upccCellRaw ((relabelWL (π,p), rawApply (π,x)), k) =
      permList π (upccCellRaw ((p,x), k)) := by
  unfold upccCellRaw
  rw [relabelWL_fst]
  simp only [permList, List.filter_map]
  congr 1
  apply List.filter_congr
  intro y hy
  dsimp only [Function.comp_def]
  rw [binColor_relabel h hπ x.isLt ((h.domMem y).1 hy)]

theorem upccCellBig_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (k a b : ℕ) :
    upccCellBig (((relabelWL (π,p), (a,b)), rawApply (π,x)), k) =
      upccCellBig (((p,(a,b)), x), k) := by
  simp only [upccCellBig, upccCellRaw_relabel h hπ x k, relabelWL_fst,
    permList, List.length_map]

theorem upccBigColors_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (a b : ℕ) :
    upccBigColors ((relabelWL (π,p), (a,b)), rawApply (π,x)) =
      upccBigColors ((p,(a,b)), x) := by
  unfold upccBigColors
  have hm : (relabelWL (π,p)).1.map (fun y =>
      binColor (relabelWL (π,p), (rawApply (π,x),y))) =
      p.1.map (fun y => binColor (p,(x,y))) := by
    rw [relabelWL_fst]
    simp only [permList, List.map_map]
    apply List.map_congr_left
    intro y hy
    exact binColor_relabel h hπ x.isLt ((h.domMem y).1 hy)
  rw [hm]
  apply List.filter_congr
  intro k _
  exact upccCellBig_relabel h hπ x k a b

theorem upccBigColor_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (h : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (x : Fin n) (a b : ℕ) :
    upccBigColor ((relabelWL (π,p), (a,b)), rawApply (π,x)) =
      upccBigColor ((p,(a,b)), x) := by
  simp only [upccBigColor, upccBigColors_relabel h hπ]

/-! The diameter-two step minimizes a code of two colors. We keep the pair
itself in the accumulator, so the routine never needs to unpair a number. -/

theorem polyFun_upccNatPair : PolyFun (fun z : ℕ × ℕ => Nat.pair z.1 z.2) := by
  have hlt : PolyFun (fun z : ℕ × ℕ => decide (z.1 < z.2)) :=
    ((polyFun_fst.add (polyFun_const 1)).le polyFun_snd).of_eq
      (fun z => by simp)
  exact (PolyFun.ite hlt ((polyFun_snd.mul polyFun_snd).add polyFun_fst)
    (((polyFun_fst.mul polyFun_fst).add polyFun_fst).add polyFun_snd)).of_eq
      (fun z => by simp [Nat.pair])

/-- Keep the smaller color-pair code. -/
def upccMinPairStep (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  if Nat.pair z.1.1 z.1.2 ≤ Nat.pair z.2.1 z.2.2 then z.1 else z.2

theorem polyFun_upccMinPairStep : PolyFun upccMinPairStep :=
  (PolyFun.ite ((polyFun_fst.comp polyFun_upccNatPair).le
    (polyFun_snd.comp polyFun_upccNatPair)) polyFun_fst polyFun_snd).of_eq
      (fun z => by simp [upccMinPairStep])

private theorem upccMinPairFold_mem (l : List (ℕ × ℕ)) (a : ℕ × ℕ) :
    l.foldl (fun a b => upccMinPairStep (a,b)) a = a ∨
      l.foldl (fun a b => upccMinPairStep (a,b)) a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons b l ih =>
      rcases ih (upccMinPairStep (a,b)) with he | hm
      · rw [List.foldl_cons, he]
        unfold upccMinPairStep
        split
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ hm)

private theorem upccMinPairFold_le (l : List (ℕ × ℕ)) (a : ℕ × ℕ) :
    let v := l.foldl (fun a b => upccMinPairStep (a,b)) a
    Nat.pair v.1 v.2 ≤ Nat.pair a.1 a.2 ∧
      ∀ b ∈ l, Nat.pair v.1 v.2 ≤ Nat.pair b.1 b.2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      have hstep : Nat.pair (upccMinPairStep (a,b)).1 (upccMinPairStep (a,b)).2 =
          min (Nat.pair a.1 a.2) (Nat.pair b.1 b.2) := by
        simp only [upccMinPairStep]
        split <;> simp_all [Nat.le_of_lt]
      obtain ⟨ha, hl⟩ := ih (upccMinPairStep (a,b))
      rw [hstep] at ha
      exact ⟨ha.trans (min_le_left ..), fun v hv => by
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ha.trans (min_le_right ..)
        · exact hl v hv⟩

/-- The least pair code in a finite list, or `(0,0)` for an empty list. -/
def upccLeastPair (l : List (ℕ × ℕ)) : ℕ × ℕ :=
  l.foldl (fun a b => upccMinPairStep (a,b)) (l.getD 0 (0,0))

theorem upccLeastPair_spec (l : List (ℕ × ℕ)) (hne : l ≠ []) :
    upccLeastPair l ∈ l ∧
      ∀ b ∈ l, Nat.pair (upccLeastPair l).1 (upccLeastPair l).2 ≤ Nat.pair b.1 b.2 := by
  have hhead : l.getD 0 (0,0) ∈ l := by
    cases l with
    | nil => contradiction
    | cons a l => simp
  refine ⟨?_, (upccMinPairFold_le l (l.getD 0 (0,0))).2⟩
  rcases upccMinPairFold_mem l (l.getD 0 (0,0)) with he | hm
  · change l.foldl (fun a b => upccMinPairStep (a,b)) (l.getD 0 (0,0)) ∈ l
    rw [he]
    exact hhead
  · exact hm

theorem polyFun_upccLeastPair : PolyFun upccLeastPair := by
  have hacc : ∀ (a : ℕ × ℕ) (l : List (ℕ × ℕ)) (j : ℕ),
      Enc.size ((l.take j).foldl (fun a b => upccMinPairStep (a,b)) a) ≤
        Enc.size (a,l) := by
    intro a l j
    rcases upccMinPairFold_mem (l.take j) a with he | hm
    · rw [he]; exact Combine.size_fst_le _ _
    · exact (size_mem_le (List.mem_of_mem_take hm)).trans (Combine.size_snd_le _ _)
  have hh : PolyFun (fun l : List (ℕ × ℕ) => l.getD 0 (0,0)) :=
    ((polyFun_id.pair (polyFun_const 0)).pair (polyFun_const (0,0))).comp polyFun_getD
  exact ((hh.pair polyFun_id).comp
    (PolyFun.foldl polyFun_upccMinPairStep polyBound_id hacc)).of_eq (fun _ => rfl)

/-- Ordered pairs of vertices, in the order supplied by the input. -/
def upccPairs (l : List ℕ) : List (ℕ × ℕ) :=
  l.flatMap (fun u => l.map (fun v => (u,v)))

@[simp] theorem mem_upccPairs (l : List ℕ) (q : ℕ × ℕ) :
    q ∈ upccPairs l ↔ q.1 ∈ l ∧ q.2 ∈ l := by
  rcases q with ⟨u,v⟩
  simp [upccPairs]

theorem polyFun_upccPairs : PolyFun upccPairs := by
  have hm : PolyFun (fun z : List ℕ × ℕ => z.1.map (fun v => (z.2,v))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam polyFun_id)
  exact ((polyFun_id.pair polyFun_id).comp (PolyFun.flatMapParam hm)).of_eq (fun _ => rfl)

theorem polyFun_upccBoolAnd : PolyFun (fun z : Bool × Bool => z.1 && z.2) :=
  (PolyFun.ite polyFun_fst polyFun_snd (polyFun_const false)).of_eq
    (fun z => by cases z.1 <;> rfl)

theorem polyFun_upccNatNe : PolyFun (fun z : ℕ × ℕ => decide (z.1 ≠ z.2)) :=
  (PolyFun.ite polyFun_natEq (polyFun_const false) (polyFun_const true)).of_eq
    (fun z => by by_cases h : z.1 = z.2 <;> simp [h])

/-- The colors of the second cell and of an edge through a witness pair `(z,y)`. -/
def upccWitnessColors (z : (RawConfig × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (binColor (z.1.1, (z.1.2,z.2.2)), binColor (z.1.1,z.2))

theorem polyFun_upccWitnessColors : PolyFun upccWitnessColors :=
  (((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd))).comp
      polyFun_binColor).pair
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_binColor)

/-- Section 9.3: test the witness for the two non-diagonal, non-big colors. -/
def upccMidWitness (z : ((RawConfig × ℕ) × ℕ) × (ℕ × ℕ)) : Bool :=
  let ij := upccWitnessColors (z.1.1,z.2)
  let d := binColor (z.1.1.1,(z.1.1.2,z.1.1.2))
  decide (binColor (z.1.1.1,(z.1.1.2,z.2.1)) = z.1.2) &&
    (decide (ij.1 ≠ d) && (decide (ij.1 ≠ z.1.2) &&
      (decide (ij.2 ≠ d) && decide (ij.2 ≠ z.1.2))))

theorem polyFun_upccMidWitness : PolyFun upccMidWitness := by
  let T := ((RawConfig × ℕ) × ℕ) × (ℕ × ℕ)
  have hp : PolyFun (fun z : T => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : T => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hk : PolyFun (fun z : T => z.1.2) := polyFun_fst.comp polyFun_snd
  have hij : PolyFun (fun z : T => upccWitnessColors (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_upccWitnessColors
  have hi := hij.comp polyFun_fst
  have hj := hij.comp polyFun_snd
  have hd := (hp.pair (hx.pair hx)).comp polyFun_binColor
  have hz := (hp.pair (hx.pair (polyFun_snd.comp polyFun_fst))).comp polyFun_binColor
  have h₁ := (hz.pair hk).comp polyFun_natEq
  have h₂ := (hi.pair hd).comp polyFun_upccNatNe
  have h₃ := (hi.pair hk).comp polyFun_upccNatNe
  have h₄ := (hj.pair hd).comp polyFun_upccNatNe
  have h₅ := (hj.pair hk).comp polyFun_upccNatNe
  exact (h₁.pair ((h₂.pair ((h₃.pair ((h₄.pair h₅).comp polyFun_upccBoolAnd)).comp
    polyFun_upccBoolAnd)).comp polyFun_upccBoolAnd)).comp polyFun_upccBoolAnd

/-- Scan witness vertices, retaining the color pair of every valid witness. -/
def upccMidCandidates (z : (RawConfig × ℕ) × ℕ) : List (ℕ × ℕ) :=
  ((upccPairs z.1.1.1).filter (fun q => upccMidWitness (z,q))).map
    (fun q => upccWitnessColors (z.1,q))

theorem polyFun_upccMidCandidates : PolyFun upccMidCandidates := by
  have hl := (polyFun_id.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp
    polyFun_upccPairs)).comp (PolyFun.filterParam polyFun_upccMidWitness)
  have hm : PolyFun (fun z : ((RawConfig × ℕ) × ℕ) × (ℕ × ℕ) =>
      upccWitnessColors (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_upccWitnessColors
  exact ((polyFun_id.pair hl).comp (PolyFun.mapParam hm)).of_eq (fun _ => rfl)

/-- Section 9.3: minimize `Nat.pair`, exactly as the mathematical `midIdx` does. -/
def upccMidIJRaw (z : (RawConfig × ℕ) × ℕ) : ℕ × ℕ :=
  upccLeastPair (upccMidCandidates z)

theorem polyFun_upccMidIJRaw : PolyFun upccMidIJRaw :=
  polyFun_upccMidCandidates.comp polyFun_upccLeastPair

section MidSpec

variable {Ω : Type} {s : Set Ω} {n : ℕ} {p : RawConfig}
    {c : ↥s → ↥s → ℕ}

theorem upccMidCandidates_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x : ↥s) (k : ℕ) (ij : ℕ × ℕ) :
    ij ∈ upccMidCandidates ((p,e x),k) ↔ MidPair c x k (Nat.pair ij.1 ij.2) := by
  simp only [upccMidCandidates, List.mem_map, List.mem_filter, mem_upccPairs,
    MidPair, Nat.unpair_pair]
  constructor
  · rintro ⟨⟨z,y⟩, ⟨⟨hz,hy⟩,hw⟩,hij⟩
    let z' := e.symm ⟨z,(h.domMem z).1 hz⟩
    let y' := e.symm ⟨y,(h.domMem y).1 hy⟩
    have hz' : (e z' : ℕ) = z := by simp [z']
    have hy' : (e y' : ℕ) = y := by simp [y']
    have hi : binColor (p,(e x,y)) = ij.1 := congrArg Prod.fst hij
    have hj : binColor (p,(z,y)) = ij.2 := congrArg Prod.snd hij
    simp only [upccMidWitness, upccWitnessColors, Bool.and_eq_true,
      decide_eq_true_eq] at hw
    refine ⟨z',y',?_,?_,?_,?_,?_,?_,?_⟩
    · rw [← he x z', hz']; exact hw.1
    · rw [← he x y', hy']; exact hi
    · rw [← he z' y', hz', hy']; exact hj
    · rw [← hi, ← he x x]; exact hw.2.1
    · rw [← hi]; exact hw.2.2.1
    · rw [← hj, ← he x x]; exact hw.2.2.2.1
    · rw [← hj]; exact hw.2.2.2.2
  · rintro ⟨z,y,hz,hy,hzy,hid,hik,hjd,hjk⟩
    refine ⟨(e z,e y),⟨⟨mem_dom h (e z),mem_dom h (e y)⟩,?_⟩,?_⟩
    · simp only [upccMidWitness, upccWitnessColors, he x z, he x y, he z y,
        he x x, hz, hy, hzy, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨True.intro,hid,hik,hjd,hjk⟩
    · exact Prod.ext ((he x y).trans hy) ((he z y).trans hzy)

/-- The bounded scan computes the same least pair as `Nat.find`.
This does not enumerate the natural numbers below that code. -/
theorem upccMidIJRaw_spec (h : RawWL.WF n 2 p) (e : ↥s ≃ Fin n)
    (he : UpccNames e p c) (x : ↥s) (k : ℕ) :
    upccMidIJRaw ((p,e x),k) = (midI c x k,midJ c x k) := by
  classical
  by_cases hex : ∃ m, MidPair c x k m
  · have hmem : (Nat.find hex).unpair ∈ upccMidCandidates ((p,e x),k) := by
      rw [upccMidCandidates_spec h e he, Nat.pair_unpair]
      exact Nat.find_spec hex
    have hne : upccMidCandidates ((p,e x),k) ≠ [] := List.ne_nil_of_mem hmem
    obtain ⟨hsel,hle⟩ := upccLeastPair_spec _ hne
    have hsel' := (upccMidCandidates_spec h e he x k _).1 hsel
    have hlow := Nat.find_min' hex hsel'
    have hupp := hle _ hmem
    rw [Nat.pair_unpair] at hupp
    have heq := le_antisymm hupp hlow
    apply Nat.pairEquiv.injective
    change Nat.pair (upccMidIJRaw ((p,e x),k)).1 (upccMidIJRaw ((p,e x),k)).2 =
      Nat.pair (midI c x k) (midJ c x k)
    rw [midI, midJ, Nat.pair_unpair, midIdx, dif_pos hex]
    exact heq
  · have hnil : upccMidCandidates ((p,e x),k) = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro ij hij
      exact hex ⟨Nat.pair ij.1 ij.2,(upccMidCandidates_spec h e he x k ij).1 hij⟩
    simp [upccMidIJRaw, hnil, upccLeastPair, midI, midJ, midIdx, hex, Nat.unpair]

end MidSpec

/-- Section 9: two ordered lists of ambient vertex names and a rectangular
matrix of zeroes and ones, as in the A10 session-1 encoding. -/
abbrev RawUpccBip := List ℕ × List ℕ × List (List ℕ)

/-- Read a row of the adjacency matrix, in the supplied second-part order. -/
def upccBipRow (z : RawBipConstituent × ℕ) : List ℕ :=
  z.1.2.2.map (fun v => if binColor (z.1.1.1,(z.2,v)) = z.1.1.2 then 1 else 0)

def upccBipRows (z : RawBipConstituent) : List (List ℕ) :=
  z.2.1.map (fun u => upccBipRow (z,u))

theorem polyFun_upccBipRow : PolyFun upccBipRow := by
  have hc : PolyFun (fun z : (RawBipConstituent × ℕ) × ℕ =>
      binColor (z.1.1.1.1,(z.1.2,z.2))) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_binColor
  have hk : PolyFun (fun z : (RawBipConstituent × ℕ) × ℕ => z.1.1.1.2) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
  have hm := PolyFun.ite ((hc.pair hk).comp polyFun_natEq)
    (polyFun_const (1 : ℕ)) (polyFun_const (0 : ℕ))
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp
    (PolyFun.mapParam hm)).of_eq (fun z => by simp [upccBipRow])

theorem polyFun_upccBipRows : PolyFun upccBipRows :=
  ((polyFun_id.pair (polyFun_snd.comp polyFun_fst)).comp
    (PolyFun.mapParam polyFun_upccBipRow)).of_eq (fun _ => rfl)

/-- Lemma 9.3.1: form `(C_k,C_i;(C_k × C_i) ∩ R_j)` from the three colors. -/
def upccBipRaw (z : (RawConfig × ℕ) × (ℕ × (ℕ × ℕ))) : RawUpccBip :=
  let left := upccCellRaw (z.1,z.2.1)
  let right := upccCellRaw (z.1,z.2.2.1)
  (left,right,upccBipRows ((z.1.1,z.2.2.2),(left,right)))

theorem polyFun_upccBipRaw : PolyFun upccBipRaw := by
  have hl : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × (ℕ × ℕ)) =>
      upccCellRaw (z.1,z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_upccCellRaw
  have hr : PolyFun (fun z : (RawConfig × ℕ) × (ℕ × (ℕ × ℕ)) =>
      upccCellRaw (z.1,z.2.2.1)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp
      polyFun_upccCellRaw
  have hg := ((((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).pair (hl.pair hr)).comp
      polyFun_upccBipRows)
  exact hl.pair (hr.pair hg)

/-- A tagged outcome. The labellings are indexed by ambient vertex name.
`none` means a colored partition. `some` carries the new threshold and graph.
In the graph case the first labelling also supplies its vertex colors. -/
abbrev RawUpccOutcome := (RawLab × RawLab) × Option ((ℕ × ℕ) × RawUpccBip)

/-- The graph branch with a supplied big color. -/
def upccBipBranch (z : (RawUpcc × ℕ) × ℕ) : (ℕ × ℕ) × RawUpccBip :=
  let p := z.1.1.1
  let x := z.1.2
  let ij := upccMidIJRaw ((p,x),z.2)
  ((z.1.1.2.1 * p.1.length,
      z.1.1.2.2 * (upccCellRaw ((p,x),z.2)).length),
    upccBipRaw ((p,x),(z.2,ij)))

theorem polyFun_upccBipBranch : PolyFun upccBipBranch := by
  have hp : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have ht := (hp.pair hx).pair polyFun_snd
  have ha : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hb : PolyFun (fun z : (RawUpcc × ℕ) × ℕ => z.1.1.2.2) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd
  have hn := (hp.comp polyFun_fst).comp polyFun_length
  have hd := (ht.comp polyFun_upccCellRaw).comp polyFun_length
  have hg := ((hp.pair hx).pair (polyFun_snd.pair (ht.comp polyFun_upccMidIJRaw))).comp
    polyFun_upccBipRaw
  exact ((ha.mul hn).pair (hb.mul hd)).pair hg

namespace Upcc

/-- Lemma 9.3.1: one version for each vertex. -/
def widthF (r : RawUpcc) : ℕ := r.1.1.length

/-- Lemma 9.3.1: return one outcome at the named individualized vertex.
An out-of-range index still takes polynomial time, but has no outcome spec. -/
def versionF (z : RawUpcc × ℕ) : RawUpccOutcome :=
  let cells := upccCellsRaw (z.1.1,z.2)
  ((cells,cells), (upccBigColor z).elim none (fun k => some (upccBipBranch (z,k))))

theorem widthF_spec {n : ℕ} {r : RawUpcc} (h : RawWL.WF n 2 r.1) : widthF r = n :=
  card_eq_length_dom h

theorem polyFun_widthF : PolyFun widthF :=
  (polyFun_fst.comp polyFun_fst).comp polyFun_length

theorem polyFun_versionF : PolyFun versionF := by
  have hl : PolyFun (fun z : RawUpcc × ℕ => upccCellsRaw (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_upccCellsRaw
  have hs : PolyFun (fun z : ℕ × (RawUpcc × ℕ) => some (upccBipBranch (z.2,z.1))) :=
    ((polyFun_snd.pair polyFun_fst).comp polyFun_upccBipBranch).comp polyFun_some
  have ho := (polyFun_upccBigColor.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hs)
  exact (hl.pair hl).pair ho

end Upcc

end Algo
