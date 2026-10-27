/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 8–11 (§14.1), case 3 of the
repair — the action of `G*` on `Γ*` on the machine, and the Johnson hint of line 11.
-/
import Workspace.Algo.PrimitiveLine4dDomFacts
import Workspace.Algo.AlignJohnsonIso

/-!
# `ϕ* : G* → S(Γ*)` on the machine, and the hint of line 11

Line 8 of Procedure Align takes `ψ : H → S(Γ*)`, *"the natural epimorphism"*, and line 10
takes `ϕ* = ψ ∘ ϕ|_{G*}`.  In case 3 of the repair the round hands `ϕ*` down
with the Chain Rule call on the dominant orbit `Δ₁` of `G*` (line 11, *"for recursive
processing of the corresponding window"*).  On the machine a hint is a raw pair
`((Γ*, rows), t)` (`Algo.RawMasterHint`): the rows are the images under `ϕ*` of the
generators of the group induced on the window, in their order, and `t` is the label size of
Theorem 10.5.1 at the first point of the window.  This file computes it.

**The points of `Γ*`** (`Algo.alignDomKeys`) are numbered `0, …, m* - 1`:

* case (A), an equipartition of the dominant class `Δ_j`: `Γ*` is the set of blocks inside
  `Δ_j`; the machine lists one point of each block, its least dominant point
  (`Algo.alignDomRepsA`), and the block of the `i`-th listed point is the `i`-th point of
  `Γ*`;
* case (B), a Johnson scheme on `Δ_j`: `Γ* = [0, m*)` is already numbered by the rows of the
  raw scheme; the list is the set of their entries (`Algo.rawJDeg` is its length).

**A point `i` of `Γ*` is marked on `Γ`** by the points of `Γ` that "carry" it
(`Algo.alignDomMark`): in case (A) the dominant points of its block, in case (B) the points of
`Δ_j` whose `t*`-subset contains `i`.  An automorphism `σ` of `X'` moves the marked sets
among themselves, and `ψ(σ)(i)` is the point `a` of `Γ*` whose marked set contains the image
of the marked set of `i` (`Algo.alignDomPsiAt`; `Algo.markFirstExpr_eq` is the reason this
is `ψ(σ)(i)`: two different points of `Γ*` have marked sets neither of which contains the
other).

**The hint** (`Algo.alignDomHint`) is then read off: the rows are `ψ(ϕ(g))` for the
generators `g` of the call (`Algo.rawImgOf` computes `ϕ(g)`), and `t` is the length of the
label of the first point of the window (`Algo.rawTpoint`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## The points of `Γ*` -/

/-- Case (A): the dominant points of `Γ` (the list `z.1.2`) in the block of the point `z.2`,
that is with the cell of `z.2` in the colored partition `z.1.1`. -/
def alignDomBlockOf (z : (RawColPart × List ℕ) × ℕ) : List ℕ :=
  z.1.2.filter (fun δ => decide (cellOf z.1.1 δ = cellOf z.1.1 z.2))

/-- Case (A): the point `z.2` is the first dominant point of its block. -/
def alignDomIsRep (z : (RawColPart × List ℕ) × ℕ) : Bool :=
  decide (rawGet (alignDomBlockOf z, 0) = z.2)

/-- Case (A): one point of each block inside the dominant class, its first one. -/
def alignDomRepsA (z : RawColPart × List ℕ) : List ℕ :=
  z.2.filter (fun γ => alignDomIsRep (z, γ))

/-- §14.1, line 7: **the points of `Γ*`, as a list** of length `m*`.  Case (A): one point of
each block inside the dominant class; case (B): the entries of the rows of the Johnson
scheme. -/
def alignDomKeys (p : RawAction × RawAlignOutcome) : List ℕ :=
  p.2.1.elim (p.2.2.elim [] (fun J => dedupG (([] : List ℕ), J.2.2.flatten)))
    (fun P => alignDomRepsA (P, alignRDomPoints (alignRColorOf p)))

/-- §14.1, lines 7–8: **the point `w` of `Γ` carries the point `i` of `Γ*`**.  Case (A): `w`
is a dominant point of the `i`-th block; case (B): `w` is a vertex of the Johnson scheme whose
`t*`-subset contains `i`. -/
def alignDomMark (z : (RawAction × RawAlignOutcome) × ℕ × ℕ) : Bool :=
  z.1.2.1.elim
    (z.1.2.2.elim false
      (fun J => decide (z.2.2 ∈ J.1) && decide (z.2.1 ∈ rawJRow (J, z.2.2))))
    (fun P => decide (labAt (alignRColorOf z.1).2 z.2.2 = alignRDomColor (alignRColorOf z.1)) &&
      decide (cellOf P z.2.2 = cellOf P (rawGet (alignDomKeys z.1, z.2.1))))

/-! ## `ψ` on the machine -/

/-- The test of `Algo.alignDomPsiOk`: the point `w` of `Γ` carries `i`, and its image under
`σ` does not carry `a`. -/
def alignDomPsiBad (z : (((RawAction × RawAlignOutcome) × RawPerm) × ℕ × ℕ) × ℕ) : Bool :=
  alignDomMark (z.1.1.1, z.1.2.1, z.2) && !alignDomMark (z.1.1.1, z.1.2.2, rawApply (z.1.1.2, z.2))

/-- `σ` carries the points of `Γ` that carry `i` to points that carry `a`. -/
def alignDomPsiOk (z : ((RawAction × RawAlignOutcome) × RawPerm) × ℕ × ℕ) : Bool :=
  decide (((List.range z.1.1.1.2.1.length).filter (fun w => alignDomPsiBad (z, w))).length = 0)

/-- §14.1, line 8: **`ψ(σ)(i)`**, the first point `a` of `Γ*` such that `σ` carries the points
of `Γ` that carry `i` to points that carry `a`. -/
def alignDomPsiAt (z : ((RawAction × RawAlignOutcome) × RawPerm) × ℕ) : ℕ :=
  rawGet (((List.range (alignDomKeys z.1.1).length).filter
    (fun a => alignDomPsiOk (z.1, z.2, a))), 0)

/-- §14.1, line 8: **`ψ(σ)`**, *"the natural epimorphism"* `ψ : H → S(Γ*)`, at the raw
permutation `σ` of `Γ`. -/
def alignDomPsi (z : (RawAction × RawAlignOutcome) × RawPerm) : RawPerm :=
  (List.range (alignDomKeys z.1).length).map (fun i => alignDomPsiAt (z, i))

/-! ## The hint of line 11 -/

/-- §14.1, line 10: **the images under `ϕ* = ψ ∘ ϕ` of a list of permutations of `Ω`** in
`G*`. -/
def alignDomHintRows (z : (RawAction × RawAlignOutcome) × RawGens) : RawGens :=
  z.2.map (fun r => alignDomPsi (z.1, rawImgOf (z.1.1, r)))

/-- §14.1, line 11: **the action of `G*` on `Γ*`, read on the window of a call**: the group
induced on the window with its generators (`Algo.primitiveWindowInput`), and the images under
`ϕ*` of the generators of the call. -/
def alignDomHintAction (z : (RawAction × RawAlignOutcome) × RawWinSI) : RawAction :=
  ((z.2.1, (primitiveWindowInput z.2).1), (alignDomKeys z.1, alignDomHintRows (z.1, z.2.2.1)))

/-- §14.1, line 11: **the hint of case 3**, *"`ϕ*` … for recursive processing of the
corresponding window"*, in the raw format of the Master Algorithm (`Algo.RawMasterHint`): the
points of `Γ*` with the rows of `ϕ*`, and the label size `t` of Theorem 10.5.1 at the first
point of the window. -/
def alignDomHint (z : (RawAction × RawAlignOutcome) × RawWinSI) : RawMasterHint :=
  ((alignDomHintAction z).2, (rawTpoint (alignDomHintAction z, 0)).length)

/-- The top action the Master Algorithm reads off a node carrying this hint is the action of
`Algo.alignDomHintAction`. -/
theorem masterHintTop_alignDomHint (z : (RawAction × RawAlignOutcome) × RawWinSI) :
    (masterHintTop (z.2, alignDomHint z)).1 = alignDomHintAction z := rfl

/-! ## Running time -/

section Poly

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem pelim {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → Option β}
    {g : α → γ} {h : β × α → γ} (hf : PolyFun f) (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun a => (f a).elim (g a) (fun b => h (b, a))) :=
  (hf.pair polyFun_id).comp (PolyFun.optionElim hg hh)
private theorem pnot {α : Type*} [Enc α] {f : α → Bool} (hf : PolyFun f) :
    PolyFun (fun a => !f a) :=
  (PolyFun.ite hf (polyFun_const false) (polyFun_const true)).of_eq (fun a => by
    cases f a <;> rfl)

theorem polyFun_alignDomBlockOf : PolyFun alignDomBlockOf := by
  have i : PolyFun (fun w : ((RawColPart × List ℕ) × ℕ) × ℕ => w) := polyFun_id
  have h1 : PolyFun (fun w : ((RawColPart × List ℕ) × ℕ) × ℕ => cellOf w.1.1.1 w.2) :=
    ((pfst (pfst (pfst i))).pair (psnd i)).comp polyFun_cellOfPair
  have h2 : PolyFun (fun w : ((RawColPart × List ℕ) × ℕ) × ℕ => cellOf w.1.1.1 w.1.2) :=
    ((pfst (pfst (pfst i))).pair (psnd (pfst i))).comp polyFun_cellOfPair
  exact ((polyFun_id.pair (psnd (pfst (polyFun_id (α := (RawColPart × List ℕ) × ℕ))))).comp
    (PolyFun.filterParam ((h1.pair h2).comp polyFun_pairNatEq))).of_eq (fun _ => rfl)

theorem polyFun_alignDomIsRep : PolyFun alignDomIsRep :=
  (((polyFun_alignDomBlockOf.pair (polyFun_const 0)).comp polyFun_rawGet).natEq
    polyFun_snd).of_eq (fun _ => rfl)

theorem polyFun_alignDomRepsA : PolyFun alignDomRepsA :=
  ((polyFun_id.pair polyFun_snd).comp (PolyFun.filterParam polyFun_alignDomIsRep)).of_eq
    (fun _ => rfl)

theorem polyFun_alignDomKeys : PolyFun alignDomKeys := by
  let T := RawAction × RawAlignOutcome
  have i : PolyFun (fun p : T => p) := polyFun_id
  have hJ : PolyFun (fun p : T => p.2.2.elim [] (fun J => dedupG (([] : List ℕ), J.2.2.flatten))) :=
    (pelim (psnd (psnd i)) (polyFun_const [])
      ((((polyFun_const ([] : List ℕ)).pair ((psnd (psnd (pfst polyFun_id))).comp
        polyFun_flatten)).comp (polyFun_dedupG polyFun_natEq)))).of_eq
      (fun p => by cases p.2.2 <;> rfl)
  have hA : PolyFun (fun r : RawColPart × T =>
      alignDomRepsA (r.1, alignRDomPoints (alignRColorOf r.2))) :=
    ((pfst polyFun_id).pair (((psnd polyFun_id).comp polyFun_alignRColorOf).comp
      polyFun_alignRDomPoints)).comp polyFun_alignDomRepsA
  exact pelim (pfst (psnd i)) hJ hA

set_option maxHeartbeats 1000000 in
theorem polyFun_alignDomMark : PolyFun alignDomMark := by
  let Z := (RawAction × RawAlignOutcome) × ℕ × ℕ
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have hB : PolyFun (fun z : Z => z.1.2.2.elim false
      (fun J => decide (z.2.2 ∈ J.1) && decide (z.2.1 ∈ rawJRow (J, z.2.2)))) := by
    have j : PolyFun (fun r : RawJohnson × Z => r) := polyFun_id
    have h1 : PolyFun (fun r : RawJohnson × Z => decide (r.2.2.2 ∈ r.1.1)) :=
      ((psnd (psnd (psnd j))).pair (pfst (pfst j))).comp (polyFun_listMem polyFun_natEq)
    have h2 : PolyFun (fun r : RawJohnson × Z => decide (r.2.2.1 ∈ rawJRow (r.1, r.2.2.2))) :=
      ((pfst (psnd (psnd j))).pair (((pfst j).pair (psnd (psnd (psnd j)))).comp
        polyFun_rawJRow)).comp (polyFun_listMem polyFun_natEq)
    exact (pelim (psnd (psnd (pfst i))) (polyFun_const false) (polyFun_and h1 h2)).of_eq
      (fun z => by cases z.1.2.2 <;> rfl)
  have hA : PolyFun (fun r : RawColPart × Z =>
      decide (labAt (alignRColorOf r.2.1).2 r.2.2.2 = alignRDomColor (alignRColorOf r.2.1)) &&
        decide (cellOf r.1 r.2.2.2 = cellOf r.1 (rawGet (alignDomKeys r.2.1, r.2.2.1)))) := by
    have j : PolyFun (fun r : RawColPart × Z => r) := polyFun_id
    have hc : PolyFun (fun r : RawColPart × Z => alignRColorOf r.2.1) :=
      (pfst (psnd j)).comp polyFun_alignRColorOf
    have h1 : PolyFun (fun r : RawColPart × Z =>
        decide (labAt (alignRColorOf r.2.1).2 r.2.2.2 = alignRDomColor (alignRColorOf r.2.1))) :=
      (((psnd hc).pair (psnd (psnd (psnd j)))).comp polyFun_labAt).natEq
        (hc.comp polyFun_alignRDomColor)
    have hk : PolyFun (fun r : RawColPart × Z => rawGet (alignDomKeys r.2.1, r.2.2.1)) :=
      ((((pfst (psnd j)).comp polyFun_alignDomKeys).pair (pfst (psnd (psnd j))))).comp
        polyFun_rawGet
    have h2 : PolyFun (fun r : RawColPart × Z =>
        decide (cellOf r.1 r.2.2.2 = cellOf r.1 (rawGet (alignDomKeys r.2.1, r.2.2.1)))) :=
      ((((pfst j).pair (psnd (psnd (psnd j)))).comp polyFun_cellOfPair).pair
        (((pfst j).pair hk).comp polyFun_cellOfPair)).comp polyFun_pairNatEq
    exact polyFun_and h1 h2
  exact (pelim (pfst (psnd (pfst i))) hB hA).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignDomPsiBad : PolyFun alignDomPsiBad := by
  let Z := (((RawAction × RawAlignOutcome) × RawPerm) × ℕ × ℕ) × ℕ
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have h1 : PolyFun (fun z : Z => alignDomMark (z.1.1.1, z.1.2.1, z.2)) :=
    ((pfst (pfst (pfst i))).pair ((pfst (psnd (pfst i))).pair (psnd i))).comp
      polyFun_alignDomMark
  have h2 : PolyFun (fun z : Z => alignDomMark (z.1.1.1, z.1.2.2, rawApply (z.1.1.2, z.2))) :=
    ((pfst (pfst (pfst i))).pair ((psnd (psnd (pfst i))).pair
      (((psnd (pfst (pfst i))).pair (psnd i)).comp polyFun_rawApply))).comp
      polyFun_alignDomMark
  exact (polyFun_and h1 (pnot h2)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignDomPsiOk : PolyFun alignDomPsiOk := by
  let Z := ((RawAction × RawAlignOutcome) × RawPerm) × ℕ × ℕ
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have hr : PolyFun (fun z : Z => List.range z.1.1.1.2.1.length) :=
    (pfst (psnd (pfst (pfst (pfst i))))).comp polyFun_rangeLength
  have hf : PolyFun (fun z : Z => ((List.range z.1.1.1.2.1.length).filter
      (fun w => alignDomPsiBad (z, w))).length) :=
    ((i.pair hr).comp (PolyFun.filterParam polyFun_alignDomPsiBad)).comp polyFun_length
  exact (hf.natEq (polyFun_const 0)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignDomPsiAt : PolyFun alignDomPsiAt := by
  let Z := ((RawAction × RawAlignOutcome) × RawPerm) × ℕ
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have hr : PolyFun (fun z : Z => List.range (alignDomKeys z.1.1).length) :=
    ((pfst (pfst i)).comp polyFun_alignDomKeys).comp polyFun_rangeLength
  have hok : PolyFun (fun w : Z × ℕ => alignDomPsiOk (w.1.1, w.1.2, w.2)) :=
    ((pfst (pfst polyFun_id)).pair ((psnd (pfst polyFun_id)).pair (psnd polyFun_id))).comp
      polyFun_alignDomPsiOk
  exact ((((i.pair hr).comp (PolyFun.filterParam hok)).pair (polyFun_const 0)).comp
    polyFun_rawGet).of_eq (fun _ => rfl)

theorem polyFun_alignDomPsi : PolyFun alignDomPsi := by
  have hr : PolyFun (fun z : (RawAction × RawAlignOutcome) × RawPerm =>
      List.range (alignDomKeys z.1).length) :=
    (polyFun_fst.comp polyFun_alignDomKeys).comp polyFun_rangeLength
  exact ((polyFun_id.pair hr).comp (PolyFun.mapParam polyFun_alignDomPsiAt)).of_eq
    (fun _ => rfl)

theorem polyFun_alignDomHintRows : PolyFun alignDomHintRows := by
  have hrow : PolyFun (fun w : (RawAction × RawAlignOutcome) × RawPerm =>
      alignDomPsi (w.1, rawImgOf (w.1.1, w.2))) :=
    (polyFun_fst.pair (((pfst polyFun_fst).pair polyFun_snd).comp polyFun_rawImgOf)).comp
      polyFun_alignDomPsi
  exact ((polyFun_fst.pair polyFun_snd).comp (PolyFun.mapParam hrow)).of_eq (fun _ => rfl)

theorem polyFun_alignDomHintAction : PolyFun alignDomHintAction := by
  let Z := (RawAction × RawAlignOutcome) × RawWinSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  exact ((pfst (psnd i)).pair (pfst ((psnd i).comp polyFun_primitiveWindowInput))).pair
    (((pfst i).comp polyFun_alignDomKeys).pair
      (((pfst i).pair (pfst (psnd (psnd i)))).comp polyFun_alignDomHintRows))

theorem polyFun_alignDomHint : PolyFun alignDomHint :=
  (psnd polyFun_alignDomHintAction).pair
    (((polyFun_alignDomHintAction.pair (polyFun_const 0)).comp polyFun_rawTpoint).comp
      polyFun_length)

end Poly

/-! ## Why the first match is `ψ(σ)(i)` -/

/-- The expression of `Algo.alignDomPsiAt`, for an arbitrary marking `M` of `Γ` by the points
of `Γ*`, `N = |Γ*|` and `m = |Γ|`. -/
def markFirstExpr (M : ℕ → ℕ → Bool) (N m : ℕ) (s : RawPerm) (i : ℕ) : ℕ :=
  rawGet ((List.range N).filter (fun a => decide (((List.range m).filter
    (fun w => M i w && !M a (rawApply (s, w)))).length = 0)), 0)

theorem alignDomPsiAt_eq (z : ((RawAction × RawAlignOutcome) × RawPerm) × ℕ) :
    alignDomPsiAt z = markFirstExpr (fun i w => alignDomMark (z.1.1, i, w))
      (alignDomKeys z.1.1).length z.1.1.1.2.1.length z.1.2 z.2 := rfl

/-- A list without repetition whose only member is `k` is `[k]`. -/
theorem eq_singleton_of_nodup {l : List ℕ} {k : ℕ} (hl : l.Nodup) (h : ∀ a, a ∈ l ↔ a = k) :
    l = [k] := by
  have hp : l.Perm [k] :=
    (List.perm_ext_iff_of_nodup hl (List.nodup_singleton k)).2 (fun a => by
      rw [h a, List.mem_singleton])
  exact List.perm_singleton.1 hp

/-- **The first match is `π(i)`.**  Let `σ` permute `Γ = [0, m)` and `π` permute
`Γ* = [0, N)` so that `w` carries `i` exactly when `σ(w)` carries `π(i)`.  If no two points of
`Γ*` have nested marked sets, then the first `a` such that `σ` carries the points that carry
`i` into the points that carry `a` is `π(i)`. -/
theorem markFirstExpr_eq {N m : ℕ} (M : ℕ → ℕ → Bool) (σ : Perm (Fin m)) (π : Perm (Fin N))
    (heq : ∀ (i : Fin N) (w : Fin m), M i w = M (π i) (σ w))
    (hsep : ∀ a b : Fin N, (∀ w : Fin m, M b w = true → M a w = true) → a = b) (i : Fin N) :
    markFirstExpr M N m (encPerm m σ) i = π i := by
  have hkey : ∀ a < N, decide (((List.range m).filter
      (fun w => M i w && !M a (rawApply (encPerm m σ, w)))).length = 0) = true ↔
      a = π i := by
    intro a ha
    rw [decide_eq_true_iff, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    constructor
    · intro h
      have := hsep ⟨a, ha⟩ (π i) (fun w' hw' => by
        have hw := h (σ.symm w') (List.mem_range.2 (σ.symm w').isLt)
        rw [rawApply_encPerm m σ (σ.symm w').isLt] at hw
        have e1 : M i (σ.symm w') = M (π i) w' := by
          rw [heq i (σ.symm w')]; simp
        have e2 : (⟨((σ ⟨(σ.symm w' : ℕ), (σ.symm w').isLt⟩ : Fin m) : ℕ), by omega⟩ : Fin m) = w' := by
          apply Fin.ext; simp
        by_contra hc
        apply hw
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        refine ⟨by rw [e1]; exact hw', ?_⟩
        have : ((σ ⟨(σ.symm w' : ℕ), (σ.symm w').isLt⟩ : Fin m) : ℕ) = (w' : ℕ) := by
          simp
        rw [this]
        simpa using hc)
      exact congrArg Fin.val this
    · rintro rfl w hw
      have hwm : w < m := List.mem_range.1 hw
      rw [rawApply_encPerm m σ hwm]
      have := heq i ⟨w, hwm⟩
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and,
        Bool.not_eq_false]
      intro h1
      rw [← this]
      exact h1
  have hl : (List.range N).filter (fun a => decide (((List.range m).filter
      (fun w => M i w && !M a (rawApply (encPerm m σ, w)))).length = 0)) = [(π i : ℕ)] := by
    refine eq_singleton_of_nodup (List.Nodup.filter _ List.nodup_range) (fun a => ?_)
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      exact (hkey a ha).1 h
    · rintro rfl
      exact ⟨(π i).isLt, (hkey _ (π i).isLt).2 rfl⟩
  rw [markFirstExpr, hl]
  rfl

/-- **`ψ(σ)` is `π`**, read as a raw permutation, when the marking has the two properties of
`Algo.markFirstExpr_eq` and `Γ*` has `N` points. -/
theorem alignDomPsi_eq_encPerm {p : RawAction × RawAlignOutcome} {N m : ℕ}
    (hN : (alignDomKeys p).length = N) (hm : p.1.2.1.length = m)
    (σ : Perm (Fin m)) (π : Perm (Fin N))
    (heq : ∀ (i : Fin N) (w : Fin m), alignDomMark (p, i, w) = alignDomMark (p, π i, σ w))
    (hsep : ∀ a b : Fin N, (∀ w : Fin m, alignDomMark (p, b, w) = true →
      alignDomMark (p, a, w) = true) → a = b) :
    alignDomPsi (p, encPerm m σ) = encPerm N π := by
  apply List.ext_getElem
  · simp [alignDomPsi, hN]
  · intro k hk hk'
    have hkN : k < N := by simpa using hk'
    simp only [alignDomPsi, List.getElem_map, List.getElem_range]
    rw [getElem_encPerm N π k hkN, alignDomPsiAt_eq]
    simp only
    rw [hN, hm]
    exact markFirstExpr_eq (fun i w => alignDomMark (p, i, w)) σ π heq hsep ⟨k, hkN⟩

end Algo
