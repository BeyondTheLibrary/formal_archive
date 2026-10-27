/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 4 — the coloring of `Γ` that a raw
outcome of Theorem 9.2.3 carries.
-/
import Workspace.Algo.AlignVersionsShape

/-!
# Line 4: the coloring of `Γ` carried by a raw outcome

> 4. (: Each of our structures has an underlying coloring – possibly trivial :)
>    Let `(Δ₁, …, Δ_k)` be the coloring of `X(x)` (the `Δ_j` are the color classes).

On the Master side the coloring is `Babai.alignColor` (`Workspace/Master/AlignOutcome.lean`):
for a colored partition it is the refined coloring of Prop. 7.1.3 (the color together with the
size of the block, `Babai.ColoredPartition.equipartRefine`), and for a Johnson scheme on
`W ⊆ Γ` it is the two-coloring `(W, Γ ∖ W)`.

`Algo.alignOutcomeLab` computes one label per point of `Γ` for a raw outcome, and
`Algo.alignOutcomeLab_eq_iff` proves that two points get the same label exactly when they get
the same color under `Babai.alignColor`. The windows of lines 5 and 6
(`Algo.alignRWindows`) depend only on which points have the same label, so they are the color
classes of `Ω` that the Master side uses.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Prop. 7.1.3: the size of the block of the point `u` of `Γ` in a raw colored partition,
the number of points of `Γ` in the same cell. -/
def cpBlockSize (p : (List ℕ × RawColPart) × ℕ) : ℕ :=
  ((rawOne p.1.1).filter (fun v => decide (cellOf p.1.2 v = cellOf p.1.2 p.2))).length

/-- §14.1, **line 4**: the label of each point of `Γ` (given by its domain list) under the
coloring of a raw outcome. A colored partition gives the pair (color, size of the block),
Prop. 7.1.3; a Johnson scheme on `W` gives `1` on `W` and `0` off it. -/
def alignOutcomeLab (p : List ℕ × RawAlignOutcome) : RawLab :=
  p.2.1.elim
    (p.2.2.elim ((rawOne p.1).map fun _ => 0)
      fun J => (rawOne p.1).map fun u => if u ∈ J.1 then 1 else 0)
    fun P => (rawOne p.1).map fun u => Nat.pair (labAt P.1 u) (cpBlockSize ((p.1, P), u))

/-! ## The labels are the colors of `Babai.alignColor` -/

section Spec

variable {m : ℕ} {dom : List ℕ}

theorem labAt_rawOne_map (hd : dom.length = m) (f : ℕ → ℕ) (γ : Fin m) :
    labAt ((rawOne dom).map f) γ = f γ := by
  have hγ : (γ : ℕ) < ((rawOne dom).map f).length := by
    simp [rawOne, hd]
  rw [labAt, List.getD_eq_getElem _ _ hγ, List.getElem_map]
  simp [rawOne]

/-- The block size, read on `Fin m`. -/
theorem cpBlockSize_eq (hd : dom.length = m) (P : RawColPart) (γ : Fin m) :
    cpBlockSize ((dom, P), γ) = {v : Fin m | cellOf P v = cellOf P γ}.ncard := by
  unfold cpBlockSize
  rw [rawOne, hd]
  have himg : {v : Fin m | cellOf P v = cellOf P γ} =
      Fin.val ⁻¹' {v : ℕ | v ∈ (List.range m).filter (fun v => decide (cellOf P v = cellOf P γ))} := by
    ext v
    simp [v.isLt]
  have hnd : ((List.range m).filter (fun v => decide (cellOf P v = cellOf P γ))).Nodup :=
    (List.nodup_range).filter _
  rw [himg, Set.ncard_preimage_of_injective_subset_range Fin.val_injective]
  · rw [← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  · intro v hv
    simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_range] at hv
    exact ⟨⟨v, hv.1⟩, rfl⟩

open scoped Classical in
/-- §14.1, **line 4**, colored-partition case: the color of `γ` under `Babai.alignColor` is
the raw color together with the block size. -/
theorem alignColor_decAlignPartition (hd : dom.length = m) (P : RawColPart) (γ : Fin m) :
    alignColor (decAlignPartition m P) γ =
      Sum.inl (labAt P.1 γ, cpBlockSize ((dom, P), γ)) := by
  rw [decAlignPartition, alignColor_inl _ _ (Set.mem_univ γ), cpBlockSize_eq hd]
  refine congrArg Sum.inl (Prod.ext rfl ?_)
  change ({v : ↥(Set.univ : Set (Fin m)) | cellOf P (v : Fin m) = cellOf P γ}).ncard = _
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext v
  simp

/-- §14.1, **line 4**: **two points of `Γ` get the same raw label exactly when they get the
same color under `Babai.alignColor`**, for every raw outcome that decodes. -/
theorem alignOutcomeLab_eq_iff (hd : dom.length = m) {o : RawAlignOutcome}
    {Z : Pt (SplitOutcomes (Fin m))} (hz : decAlignOutcome m o = some Z) (γ γ' : Fin m) :
    labAt (alignOutcomeLab (dom, o)) γ = labAt (alignOutcomeLab (dom, o)) γ' ↔
      alignColor Z γ = alignColor Z γ' := by
  classical
  rcases o with ⟨_ | P, _ | J⟩
  · simp [decAlignOutcome] at hz
  · -- a Johnson scheme on `W`
    simp only [decAlignOutcome] at hz
    split_ifs at hz with hJ
    cases hz
    simp only [alignOutcomeLab, Option.elim, labAt_rawOne_map hd]
    rw [decAlignJohnson, alignColor_inr, alignColor_inr]
    simp only [RawJohnson.carrier, Set.mem_setOf_eq, Sum.inr.injEq]
    by_cases h1 : (γ : ℕ) ∈ J.1 <;> by_cases h2 : (γ' : ℕ) ∈ J.1 <;> simp [h1, h2]
  · -- a colored partition
    simp only [decAlignOutcome, Option.some.injEq] at hz
    subst hz
    simp only [alignOutcomeLab, Option.elim, labAt_rawOne_map hd]
    rw [alignColor_decAlignPartition hd, alignColor_decAlignPartition hd, Sum.inl.injEq,
      Nat.pair_eq_pair, Prod.mk.injEq]
  · simp [decAlignOutcome] at hz

end Spec

/-! ## The labels are computed in polynomial time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem polyFun_natPair : PolyFun (fun z : ℕ × ℕ => Nat.pair z.1 z.2) := by
  have hlt : PolyFun (fun z : ℕ × ℕ => decide (z.1 < z.2)) :=
    ((polyFun_fst.add (polyFun_const 1)).le polyFun_snd).of_eq (fun z => by simp)
  exact (PolyFun.ite hlt ((polyFun_snd.mul polyFun_snd).add polyFun_fst)
    (((polyFun_fst.mul polyFun_fst).add polyFun_fst).add polyFun_snd)).of_eq
      (fun z => by simp [Nat.pair])

theorem polyFun_cpBlockSize : PolyFun cpBlockSize := by
  have i : PolyFun (fun p : (List ℕ × RawColPart) × ℕ => p) := polyFun_id
  have hq : PolyFun (fun r : ((List ℕ × RawColPart) × ℕ) × ℕ =>
      decide (cellOf r.1.1.2 r.2 = cellOf r.1.1.2 r.1.2)) := by
    have j : PolyFun (fun r : ((List ℕ × RawColPart) × ℕ) × ℕ => r) := polyFun_id
    exact (((psnd (pfst (pfst j))).pair (psnd j)).comp polyFun_cellOfPair).pair
      (((psnd (pfst (pfst j))).pair (psnd (pfst j))).comp polyFun_cellOfPair) |>.comp
      polyFun_pairNatEq
  exact ((i.pair ((pfst (pfst i)).comp polyFun_rawOne)).comp (PolyFun.filterParam hq)).comp
    polyFun_length

theorem polyFun_alignOutcomeLab : PolyFun alignOutcomeLab := by
  have i : PolyFun (fun p : List ℕ × RawAlignOutcome => p) := polyFun_id
  have hone := (pfst i).comp polyFun_rawOne
  -- the trivial coloring
  have hzero : PolyFun (fun p : List ℕ × RawAlignOutcome => (rawOne p.1).map fun _ => 0) :=
    ((polyFun_const (0 : ℕ)).pair hone).comp (PolyFun.mapParam (f := fun _ : ℕ × ℕ => 0)
      (polyFun_const 0)) |>.of_eq (fun _ => rfl)
  -- the two-coloring of a Johnson scheme
  have hJ : PolyFun (fun q : RawJohnson × (List ℕ × RawAlignOutcome) =>
      (rawOne q.2.1).map fun u => if u ∈ q.1.1 then 1 else 0) := by
    have j : PolyFun (fun q : RawJohnson × (List ℕ × RawAlignOutcome) => q) := polyFun_id
    have hf : PolyFun (fun r : List ℕ × ℕ => if r.2 ∈ r.1 then 1 else 0) :=
      (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp (polyFun_listMem (α := ℕ) polyFun_natEq))
        (polyFun_const 1) (polyFun_const 0)).of_eq (fun r => by
          by_cases h : r.2 ∈ r.1 <;> simp [h])
    exact ((pfst (pfst j)).pair ((pfst (psnd j)).comp polyFun_rawOne)).comp
      (PolyFun.mapParam hf) |>.of_eq (fun _ => rfl)
  -- the refined coloring of a colored partition
  have hP : PolyFun (fun q : RawColPart × (List ℕ × RawAlignOutcome) =>
      (rawOne q.2.1).map fun u => Nat.pair (labAt q.1.1 u) (cpBlockSize ((q.2.1, q.1), u))) := by
    have j : PolyFun (fun q : RawColPart × (List ℕ × RawAlignOutcome) => q) := polyFun_id
    have hf : PolyFun (fun r : (List ℕ × RawColPart) × ℕ =>
        Nat.pair (labAt r.1.2.1 r.2) (cpBlockSize ((r.1.1, r.1.2), r.2))) := by
      have k : PolyFun (fun r : (List ℕ × RawColPart) × ℕ => r) := polyFun_id
      exact ((((pfst (psnd (pfst k))).pair (psnd k)).comp polyFun_labAtPair).pair
        polyFun_cpBlockSize).comp polyFun_natPair
    exact (((pfst (psnd j)).pair (pfst j)).pair ((pfst (psnd j)).comp polyFun_rawOne)).comp
      (PolyFun.mapParam hf) |>.of_eq (fun _ => rfl)
  have hnone : PolyFun (fun p : List ℕ × RawAlignOutcome =>
      p.2.2.elim ((rawOne p.1).map fun _ => 0)
        fun J => (rawOne p.1).map fun u => if u ∈ J.1 then 1 else 0) :=
    ((psnd (psnd i)).pair i).comp (PolyFun.optionElim hzero hJ) |>.of_eq (fun _ => rfl)
  exact ((pfst (psnd i)).pair i).comp (PolyFun.optionElim hnone hP) |>.of_eq (fun _ => rfl)

end Algo
