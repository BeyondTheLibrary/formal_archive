/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, line 11 (§14.1), at a node of the Master Algorithm —
the hint routine of the round of lines 5–7 (Section 15).
-/
import Workspace.Algo.AlignDomHintSpec
import Workspace.Algo.TopMasterLine57Lift

/-!
# The hint routine of lines 5–7

In the round of lines 5–7 of the Master Algorithm, Procedure Align runs on the window `Δ` of
the node.  In case 3 of the repair of its lines 7–11, the call on the dominant orbit of `G*`
carries the Johnson hint of line 11 (the action of `G*` on `Γ*` through `ϕ*`).  The node
carrier asks a hint routine for the hint of each call it makes, after lifting the call to the
node's domain (`Algo.masterLiftHinted`).  This file gives that routine:

* `Algo.alignDomHintAt` — the hint of `Algo.alignDomHint` for a call given on the node's
  domain: each generator of the call is first restricted to `Δ` (`Algo.rawRestrictPerm`), where
  `ϕ` and `ψ` of Procedure Align are defined;
* `Algo.masterL57HintTest` — the test for the hinted call: the round is in stretch 3 (Procedure
  Align, not the two phases of AggregateCertificates and not the giant branch of outcome (2a)),
  Procedure Align is in case 3 (a dominant class, `m*` large: `Algo.alignRLarge`), and the call
  has more than `2|Δ|/3` points.  In case 3 only the dominant orbit of `G*` is that large (the
  other color classes have at most `2|Δ|/3` points,
  `Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`, and the other orbits in the dominant
  window fewer than `|Δ|/3`, `Babai.AlignDominant.other_orbit_small`; the round's form is
  `Babai.AlignShape.large_call_spec`);
* `Algo.masterL57Hint` — the routine, `H5` of `Algo.masterNodeHOps`, with
  `Algo.quasiFun_masterL57Hint`.
-/
set_option synthInstance.maxSize 2048

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- §14.1, line 11, **the rows of the hint for a call on the node's domain**: for each
generator `r` of the call, `ψ(ϕ(r|_Δ))`. -/
def alignDomHintAtRows (z : ((RawAction × RawAlignOutcome) × List ℕ) × RawGens) : RawGens :=
  z.2.map (fun r => alignDomPsi (z.1.1, rawImgOf (z.1.1.1, rawRestrictPerm (z.1.2, r))))

/-- §14.1, line 11: **the action of the hint for a call on the node's domain**: the group the
call induces on its window, with the rows of `Algo.alignDomHintAtRows`. -/
def alignDomHintAtAction (z : ((RawAction × RawAlignOutcome) × List ℕ) × RawWinSI) :
    RawAction :=
  ((z.2.1, (primitiveWindowInput z.2).1),
    (alignDomKeys z.1.1, alignDomHintAtRows (z.1, z.2.2.1)))

/-- §14.1, line 11: **the hint of case 3 for a call on the node's domain**, in the raw format
of the Master Algorithm: the points of `Γ*` with the rows, and the label size `t` of
Theorem 10.5.1 at the first point of the call's window. -/
def alignDomHintAt (z : ((RawAction × RawAlignOutcome) × List ℕ) × RawWinSI) :
    RawMasterHint :=
  ((alignDomHintAtAction z).2, (rawTpoint (alignDomHintAtAction z, 0)).length)

theorem masterHintTop_alignDomHintAt (z : ((RawAction × RawAlignOutcome) × List ℕ) × RawWinSI) :
    (masterHintTop (z.2, alignDomHintAt z)).1 = alignDomHintAtAction z := rfl

/-- The header of Procedure Align the round of lines 5–7 reads at a fold state. -/
def masterL57HintHdr (c b t d dc dp : ℕ) (z : RawMasterSI × ℕ × AggnL57GState) : AVHdr :=
  aggnL57Hdr c b t d dc dp (masterL57Ctx z.1, z.2.2.1.1)

/-- §14.1, line 11, **the test for the hinted call** of the round of lines 5–7: stretch 3 of
the round (Procedure Align), case 3 of the repair of lines 7–11, and a call on more than
`2|Δ|/3` points. -/
def masterL57HintTest (c b t d dc dp u v e f : ℕ)
    (z : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI) : Bool :=
  !aggnL57GActive c b t d dc dp u v e f (masterL57Enter z.1.1, z.1.2.1, z.1.2.2) &&
    (aggnAggregateChild c (masterL57Enter z.1.1, z.1.2.1, z.1.2.2.1.1)).isNone &&
    alignRLarge ((masterL57HintHdr c b t d dc dp z.1).1,
      (masterL57HintHdr c b t d dc dp z.1).2.1) &&
    decide (2 * z.1.1.1.1.length < 3 * z.2.1.1.length)

/-- §14.1, line 11, on the Master's node: **the hint routine of the round of lines 5–7**
(`H5` of `Algo.masterNodeHOps`).  At the hinted call it returns the hint of
`Algo.alignDomHintAt` for the action and outcome of Procedure Align on the node's window;
at every other call, none. -/
def masterL57Hint (c b t d dc dp u v e f : ℕ)
    (z : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI) : Option RawMasterHint :=
  if masterL57HintTest c b t d dc dp u v e f z then
    some (alignDomHintAt ((((masterL57HintHdr c b t d dc dp z.1).1,
      (masterL57HintHdr c b t d dc dp z.1).2.1), z.1.1.1.1), z.2.1))
  else none

/-! ## Running time -/

section Poly

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem polyFun_isNone' {α : Type*} [Enc α] : PolyFun (fun o : Option α => o.isNone) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) (polyFun_const false))).of_eq
    (fun o => by cases o <;> rfl)

theorem polyFun_alignDomHintAtRows : PolyFun alignDomHintAtRows := by
  have hrow : PolyFun (fun w : ((RawAction × RawAlignOutcome) × List ℕ) × RawPerm =>
      alignDomPsi (w.1.1, rawImgOf (w.1.1.1, rawRestrictPerm (w.1.2, w.2)))) :=
    (pfst polyFun_fst |>.pair (((pfst (pfst polyFun_fst)).pair
      (((psnd polyFun_fst).pair polyFun_snd).comp polyFun_rawRestrictPerm)).comp
        polyFun_rawImgOf)).comp polyFun_alignDomPsi
  exact ((polyFun_fst.pair polyFun_snd).comp (PolyFun.mapParam hrow)).of_eq (fun _ => rfl)

theorem polyFun_alignDomHintAtAction : PolyFun alignDomHintAtAction := by
  let Z := ((RawAction × RawAlignOutcome) × List ℕ) × RawWinSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  exact ((pfst (psnd i)).pair (pfst ((psnd i).comp polyFun_primitiveWindowInput))).pair
    (((pfst (pfst i)).comp polyFun_alignDomKeys).pair
      (((pfst i).pair (pfst (psnd (psnd i)))).comp polyFun_alignDomHintAtRows))

theorem polyFun_alignDomHintAt : PolyFun alignDomHintAt :=
  (psnd polyFun_alignDomHintAtAction).pair
    (((polyFun_alignDomHintAtAction.pair (polyFun_const 0)).comp polyFun_rawTpoint).comp
      polyFun_length)

theorem quasiFun_masterL57HintHdr (c b t d dc dp : ℕ) :
    QuasiFun (masterL57HintHdr c b t d dc dp) := by
  let Z := RawMasterSI × ℕ × AggnL57GState
  have i : PolyFun (fun z : Z => z) := polyFun_id
  exact (((pfst i).comp polyFun_masterL57Ctx).pair (pfst (pfst (psnd (psnd i))))).comp_quasiFun
    (quasiFun_aggnL57Hdr c b t d dc dp)

theorem quasiFun_masterL57HintTest (c b t d dc dp u v e f : ℕ) :
    QuasiFun (masterL57HintTest c b t d dc dp u v e f) := by
  let Z := (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have h1 : QuasiFun (fun z : Z =>
      !aggnL57GActive c b t d dc dp u v e f (masterL57Enter z.1.1, z.1.2.1, z.1.2.2)) :=
    ((((pfst (pfst i)).comp polyFun_masterL57Enter).pair ((pfst (psnd (pfst i))).pair
      (psnd (psnd (pfst i))))).comp_quasiFun
      (quasiFun_aggnL57GActive (c := c) (b := b) (t := t) (d := d) (dc := dc) (dp := dp)
        (u := u) (v := v) (e := e) (f := f))).comp_poly
      ((PolyFun.ite polyFun_id (polyFun_const false) (polyFun_const true)).of_eq
        (fun x => by cases x <;> rfl))
  have h2 : QuasiFun (fun z : Z =>
      (aggnAggregateChild c (masterL57Enter z.1.1, z.1.2.1, z.1.2.2.1.1)).isNone) :=
    ((((pfst (pfst i)).comp polyFun_masterL57Enter).pair ((pfst (psnd (pfst i))).pair
      (pfst (pfst (psnd (psnd (pfst i))))))).comp_quasiFun
      (aggnQuasiFun_aggregateChild c)).comp_poly polyFun_isNone'
  have h3 : QuasiFun (fun z : Z => alignRLarge ((masterL57HintHdr c b t d dc dp z.1).1,
      (masterL57HintHdr c b t d dc dp z.1).2.1)) :=
    ((pfst i).comp_quasiFun (quasiFun_masterL57HintHdr c b t d dc dp)).comp_poly
      ((polyFun_fst.pair (pfst polyFun_snd)).comp polyFun_alignRLarge)
  have h4 : PolyFun (fun z : Z => decide (2 * z.1.1.1.1.length < 3 * z.2.1.1.length)) :=
    ((((pfst (pfst (pfst (pfst i)))).comp polyFun_length).comp
      ((polyFun_const 2).mul polyFun_id)).pair
      (((pfst (pfst (psnd i))).comp polyFun_length).comp
        ((polyFun_const 3).mul polyFun_id))).comp polyFun_natLt
  exact ((((h1.pair h2).comp_poly (polyFun_and polyFun_fst polyFun_snd)).pair h3).comp_poly
    (polyFun_and polyFun_fst polyFun_snd) |>.pair h4.quasiFun).comp_poly
    (polyFun_and polyFun_fst polyFun_snd) |>.of_eq (fun _ => rfl)

/-- **The hint routine of lines 5–7 runs in quasipolynomial time.** -/
theorem quasiFun_masterL57Hint (c b t d dc dp u v e f : ℕ) :
    QuasiFun (masterL57Hint c b t d dc dp u v e f) := by
  let Z := (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have harg : QuasiFun (fun z : Z => (((masterL57HintHdr c b t d dc dp z.1).1,
      (masterL57HintHdr c b t d dc dp z.1).2.1), z.1.1.1.1)) :=
    (((pfst i).comp_quasiFun (quasiFun_masterL57HintHdr c b t d dc dp)).comp_poly
      (polyFun_fst.pair (pfst polyFun_snd))).pair
      (pfst (pfst (pfst (pfst i)))).quasiFun
  have hall : QuasiFun (fun z : Z => (masterL57HintTest c b t d dc dp u v e f z,
      ((((masterL57HintHdr c b t d dc dp z.1).1, (masterL57HintHdr c b t d dc dp z.1).2.1),
        z.1.1.1.1), z.2.1))) :=
    (quasiFun_masterL57HintTest c b t d dc dp u v e f).pair (harg.pair (pfst (psnd i)).quasiFun)
  exact (hall.comp_poly (PolyFun.ite polyFun_fst
    ((psnd polyFun_id).comp (polyFun_alignDomHintAt.comp polyFun_some))
    (polyFun_const none))).of_eq (fun z => by
      unfold masterL57Hint
      cases masterL57HintTest c b t d dc dp u v e f z <;> rfl)

end Poly

/-! ## The hint of a call on the node's domain has its meaning -/

section NodeSpec

open MulAction
open scoped Pointwise

/-- The points of `Γ*` the machine lists are points of `Γ`, in both cases of line 7. -/
theorem lt_of_mem_alignDomKeys {m : ℕ} {A : RawAction} (hg : A.2.1.length = m)
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true)
    (hB : ∀ J : RawJohnson, o = rawAlignJohnson J → (alignDomKeys (A, o)).length ≤ m)
    {i : ℕ} (hi : i ∈ alignDomKeys (A, o)) : i < m := by
  rcases decAlignOutcome_cases hX with ⟨P, rfl, -⟩ | ⟨J, hJ, rfl, -⟩
  · exact (lt_and_in_of_mem_alignDomKeys hg P hhd hi).1
  · have h1 : i ∈ J.2.2.flatten := (mem_dedupG_nil _ i).1 hi
    obtain ⟨row, hrow, hir⟩ := List.mem_flatten.1 h1
    have h2 := hJ.rowLt row hrow i hir
    have h3 := hB J rfl
    rw [length_alignDomKeys_johnson hJ] at h3
    omega

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- §14.1, lines 7–11, item 3 of the repair, at a node of the Master Algorithm: **the hint the
routine `Algo.masterL57Hint` attaches to the dominant-orbit call is good.**

The node has degree `n`, window `Δ` and group `G_N` (with `Δ` invariant); Procedure Align runs
on `Δ` with the action `A`, whose group is the group `G_N` induces on `Δ`.  Let line 6 find a
dominant class with nontrivial structure, `m*` above the threshold of Theorem 10.5.1 (case 3),
and let the call `W` be given on the node's domain: its group is the full preimage in `G_N` of
`G*` (the group of the machine's generators `Algo.alignPairG1`), and its window is the image in
the node's domain of an orbit `u^{G*}` of `G*` with `u` in the dominant window, of more than
`2|Δ|/3` points.  Then the hint `Algo.alignDomHintAt` has the meaning `Algo.MasterHintGood`
for `W`; its Johnson parameter is the machine's `m*`, `2m* ≤ m` (Eq. (73)), and its labels
are below `m`.

The representation is `ϕ*` composed with the restriction to `Δ`, read on the group the call
induces on its window (`Babai.restrictFactor`: the pointwise stabilizer of the window in the
call's group restricts into the pointwise stabilizer of `u^{G*}` in `G*`, which lies in
`ker ϕ*`), with `Γ*` numbered by the machine's list of its points. -/
theorem alignDomHintAt_good_alpha {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) {gN : RawGens}
    (hinvN : IsInvariant (decGroup n gN) (winSet n Δ))
    {A : RawAction} {ϕ : decGroup Δ.length A.1.2 →* Perm (Fin m)}
    (hAgrp : decGroup Δ.length A.1.2 = (winRestrictHom n Δ hnd hlt (decGroup n gN) hinvN).range)
    (hA : RawAction.WF Δ.length m A ϕ) (hG : IsTransitive (decGroup Δ.length A.1.2))
    (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup Δ.length A.1.2)))
    {t : ℕ} (ht : ∀ u : Fin Δ.length, tPoint ϕ u = t) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    {α : ℝ} (hα : 1 / 2 < α)
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m)
    (hmn : m ≤ Δ.length)
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hnt : 2 ≤ alignRMs (A, o))
    (hLP : VeryLargeK (alignRMs (A, o))
      (maxOrbitLength (decGroup Δ.length (alignPairG1 (A, o)))))
    {W : RawWinSI} (hndW : W.1.Nodup) (hltW : ∀ x ∈ W.1, x < n) (hwfW : RawGens.WF n W.2.1)
    (hKW : ∀ g, g ∈ decGroup n W.2.1 ↔ ∃ h : g ∈ decGroup n gN,
      winRestrictHom n Δ hnd hlt (decGroup n gN) hinvN ⟨g, h⟩ ∈
        decGroup Δ.length (alignPairG1 (A, o)))
    {u : Fin Δ.length}
    (hu : u ∈ winSet Δ.length (alignRDomWindow (alignRColorOf (A, o),
      alignRDomColor (alignRColorOf (A, o)))))
    (hwinW : ∀ x : Fin n, x ∈ winSet n W.1 ↔
      ∃ k ∈ orbit (decGroup Δ.length (alignPairG1 (A, o))) u,
        ((winEquiv n Δ hnd hlt k : ↥(winSet n Δ)) : Fin n) = x)
    (hbig : 2 * Δ.length < 3 * W.1.length) :
    MasterHintGood (W, alignDomHintAt (((A, o), Δ), W)) ∧
      (alignDomHintAt (((A, o), Δ), W)).1.1.length = alignRMs (A, o) ∧
      2 * alignRMs (A, o) ≤ m ∧ ∀ i ∈ (alignDomHintAt (((A, o), Δ), W)).1.1, i < m := by
  obtain ⟨Dd, hDm, hDGs, hDwin, hDms, -, f, hf⟩ :=
    exists_domRoundData_alpha hA hG hϕ hvl ht hK hX hα hZ hm hmn hhd hnt
  have hGs : decGroup Δ.length (alignPairG1 (A, o)) = Dd.toAlignDominant.Gs :=
    (decGroup_alignPairG1 hA hϕ hK hX).trans hDGs.symm
  have hGA : ∀ τ ∈ Dd.toAlignDominant.Gs, τ ∈ decGroup Δ.length A.1.2 := fun τ hτ => by
    rw [hDGs] at hτ
    exact (mem_preimageSubgroup.1 hτ).1
  have hMs : (alignDomKeys (A, o)).length = Dd.toAlignDominant.ms := by
    simpa using Fintype.card_congr f
  let e := winEquiv n Δ hnd hlt
  let GN := decGroup n gN
  let ρ := winRestrictHom n Δ hnd hlt GN hinvN
  have hρ : ∀ (g : GN) (k : Fin Δ.length), ((e (ρ g k) : ↥(winSet n Δ)) : Fin n) =
      (g : Perm (Fin n)) (e k : Fin n) := by
    intro g k
    show ((e (e.symm _) : ↥(winSet n Δ)) : Fin n) = _
    rw [Equiv.apply_symm_apply]
    rfl
  have he_inj : Function.Injective (fun k : Fin Δ.length => ((e k : ↥(winSet n Δ)) : Fin n)) :=
    Subtype.val_injective.comp e.injective
  let K'' := decGroup n W.2.1
  have hle : K'' ≤ GN := fun g hg => ((hKW g).1 hg).1
  have hρG : ∀ g (hg : g ∈ K''), ρ ⟨g, hle hg⟩ ∈ Dd.toAlignDominant.Gs := by
    intro g hg
    obtain ⟨_, hh⟩ := (hKW g).1 hg
    rw [← hGs]
    exact hh
  let σ : K'' →* Dd.toAlignDominant.Gs :=
    (ρ.comp (Subgroup.inclusion hle)).codRestrict Dd.toAlignDominant.Gs
      (fun g => hρG g.1 g.2)
  have hσ : ∀ g : K'', ((σ g : Dd.toAlignDominant.Gs) : Perm (Fin Δ.length)) =
      ρ ⟨g.1, hle g.2⟩ := fun g => rfl
  let ψ₀ : K'' →* Perm (Fin (alignDomKeys (A, o)).length) :=
    (permCongrHom f.symm).toMonoidHom.comp (Dd.toAlignDominant.phis.comp σ)
  -- the window of the call is the image of the orbit
  set O := orbit Dd.toAlignDominant.Gs u with hO
  have hWO : ∀ x : Fin n, x ∈ winSet n W.1 ↔ ∃ k ∈ O, ((e k : ↥(winSet n Δ)) : Fin n) = x := by
    intro x
    rw [hwinW, hGs]
  have hOinv : ∀ τ ∈ Dd.toAlignDominant.Gs, ∀ k, k ∈ O ↔ τ k ∈ O :=
    (isInvariant_iff_mem _ _).1 (isInvariant_orbit' _ u)
  have fwd : ∀ g ∈ K'', ∀ x, x ∈ winSet n W.1 → g x ∈ winSet n W.1 := by
    intro g hg x hx
    obtain ⟨k, hk, rfl⟩ := (hWO x).1 hx
    refine (hWO _).2 ⟨ρ ⟨g, hle hg⟩ k, (hOinv _ (hρG g hg) k).1 hk, ?_⟩
    exact hρ ⟨g, hle hg⟩ k
  have hinv'' : IsInvariant K'' (winSet n W.1) := by
    refine (isInvariant_iff_mem _ _).2 fun g hg x => ⟨fwd g hg x, fun hx => ?_⟩
    have := fwd g⁻¹ (K''.inv_mem hg) _ hx
    simpa using this
  have hOW : O.ncard = W.1.length := by
    rw [← ncard_winSet W.1 hndW hltW]
    have : winSet n W.1 = (fun k : Fin Δ.length => ((e k : ↥(winSet n Δ)) : Fin n)) '' O := by
      ext x; rw [hWO]; simp [Set.mem_image]
    rw [this, Set.ncard_image_of_injective _ he_inj]
  have hbig' : 2 * Fintype.card (Fin Δ.length) < 3 * O.ncard := by
    rw [Fintype.card_fin, hOW]; exact hbig
  have hLP' : Dd.LargeParam := by
    show VeryLargeK Dd.toAlignDominant.ms (maxOrbitLength Dd.toAlignDominant.Gs)
    rw [hDms, ← hGs]; exact hLP
  have hu' : u ∈ Dd.toAlignDominant.window := by rw [hDwin]; exact hu
  let c := Dd.dominantOrbit hLP' hu' hbig'
  -- the pointwise stabilizer of the window lies in the kernel
  have hstab : pointwiseStab K'' (winSet n W.1) ≤ ψ₀.ker := by
    intro g hg
    rw [mem_pointwiseStab] at hg
    have hs : σ g ∈ pointwiseStab Dd.toAlignDominant.Gs O := by
      rw [mem_pointwiseStab]
      intro k hk
      apply he_inj
      show ((e (((σ g : Dd.toAlignDominant.Gs) : Perm (Fin Δ.length)) k) : ↥(winSet n Δ)) :
        Fin n) = _
      rw [hσ, hρ]
      exact hg _ ((hWO _).2 ⟨k, hk, rfl⟩)
    have hk := c.stab_le hs
    rw [MonoidHom.mem_ker] at hk ⊢
    show (permCongrHom f.symm) (Dd.toAlignDominant.phis (σ g)) = 1
    rw [hk, map_one]
  -- the representation of the call's window group
  let K := restrictTo K'' (winSet n W.1) hinv''
  let ψ : K →* Perm (Fin (alignDomKeys (A, o)).length) := restrictFactor hinv'' ψ₀ hstab
  let e'' := winEquiv n W.1 hndW hltW
  have hH : decGroup W.1.length (primitiveWindowInput W).1 =
      K.map (e''.symm.permCongrHom).toMonoidHom := by
    have h1 := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hwfW hndW hltW hinv''
    rw [range_winRestrictHom] at h1
    exact h1
  obtain ⟨ϕ', hϕ'1, hϕ'2, hϕ'3, hϕ'4⟩ := exists_transportRep e'' K ψ _ hH
  have hψ : ∀ g : K'', ψ (restrictOnto hinv'' g) =
      Equiv.permCongr f.symm (Dd.toAlignDominant.phis (σ g)) := fun g => by
    show restrictFactor hinv'' ψ₀ hstab (restrictOnto hinv'' g) = _
    rw [restrictFactor_restrictOnto]
    rfl
  -- the generators of the call
  have hg0 : ∀ r ∈ W.2.1, decPerm n r ∈ K'' := fun r hr =>
    Subgroup.subset_closure (List.mem_map_of_mem hr)
  have hrow : ∀ r (hr : r ∈ W.2.1),
      alignDomPsi ((A, o), rawImgOf (A, rawRestrictPerm (Δ, r))) =
        encPerm _ (Equiv.permCongr f.symm
          (Dd.toAlignDominant.phis (σ ⟨decPerm n r, hg0 r hr⟩))) := fun r hr => by
    have h1 := rawRestrictPerm_spec hnd hlt hinvN (hle (hg0 r hr))
    rw [encPerm_decPerm (hwfW r hr)] at h1
    rw [h1]
    set τ := ρ ⟨decPerm n r, hle (hg0 r hr)⟩ with hτ
    have hτGs : τ ∈ Dd.toAlignDominant.Gs := hρG _ (hg0 r hr)
    have hmem : decPerm Δ.length (encPerm Δ.length τ) ∈ decGroup Δ.length A.1.2 := by
      rw [decPerm_encPerm]; exact hGA τ hτGs
    rw [aggnRawImgOf_spec hA (wf_encPerm _ _) hmem]
    have e3 : (⟨decPerm Δ.length (encPerm Δ.length τ), hmem⟩ : decGroup Δ.length A.1.2) =
        ⟨τ, hGA τ hτGs⟩ := Subtype.ext (decPerm_encPerm _ _)
    rw [e3, hf τ hτGs (hGA τ hτGs)]
    rfl
  have hres : ∀ r (hr : r ∈ W.2.1), rawRestrictPerm (W.1, r) = encPerm W.1.length
      (e''.symm.permCongr ((restrictOnto hinv'' ⟨decPerm n r, hg0 r hr⟩ : K) :
        Perm ↥(winSet n W.1))) := fun r hr => by
    have h := rawRestrictPerm_spec hndW hltW hinv'' (hg0 r hr)
    rw [encPerm_decPerm (hwfW r hr)] at h
    exact h
  have key : ∀ r (hr : r ∈ W.2.1)
      (hmem : decPerm W.1.length (rawRestrictPerm (W.1, r)) ∈
        decGroup W.1.length (primitiveWindowInput W).1),
      decPerm (alignDomKeys (A, o)).length
        (alignDomPsi ((A, o), rawImgOf (A, rawRestrictPerm (Δ, r)))) = ϕ' ⟨_, hmem⟩ := by
    intro r hr hmem
    rw [hrow r hr, decPerm_encPerm]
    have e1 : decPerm W.1.length (rawRestrictPerm (W.1, r)) =
        e''.symm.permCongr ((restrictOnto hinv'' ⟨decPerm n r, hg0 r hr⟩ : K) :
          Perm ↥(winSet n W.1)) := by
      rw [hres r hr, decPerm_encPerm]
    have e2 : (⟨_, hmem⟩ : decGroup W.1.length (primitiveWindowInput W).1) =
        ⟨_, e1 ▸ hmem⟩ := Subtype.ext e1
    rw [e2, hϕ'1, hψ]
  -- the action of the hint is well formed
  have hrg : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hwfW hndW hltW hinv''
  have hrows : RawGens.WF (alignDomKeys (A, o)).length
      (alignDomHintAtRows (((A, o), Δ), W.2.1)) := by
    intro r' hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    rw [hrow r hr]
    exact wf_encPerm _ _
  have hI : ImgsOf (((primitiveWindowInput W).1).map (decPerm W.1.length))
      ((alignDomHintAtRows (((A, o), Δ), W.2.1)).map (decPerm (alignDomKeys (A, o)).length))
      ϕ' := by
    refine ⟨by simp [primitiveWindowInput, rawRestrictGens, alignDomHintAtRows], ?_⟩
    intro i hi hi'
    have hiW : i < W.2.1.length := by
      simpa [primitiveWindowInput, rawRestrictGens] using hi
    simp only [primitiveWindowInput, rawRestrictGens, alignDomHintAtRows, List.getElem_map]
    exact key _ (List.getElem_mem hiW) _
  have hwf : RawAction.WF W.1.length (alignDomKeys (A, o)).length
      (alignDomHintAtAction (((A, o), Δ), W)) ϕ' := ⟨rfl, rfl, hrg, hrows, hI⟩
  -- the numeric facts
  have hgiant : IsGiantRep ϕ' := hϕ'2 (isGiantRep_restrictFactor hinv'' _ hstab
    (isGiantRep_permCongr f.symm _ (by
      intro a ha
      obtain ⟨τ, hτ⟩ := Dd.toAlignDominant.isGiantRep_phis ha
      have hτA : (τ : Perm (Fin Δ.length)) ∈ ρ.range := by rw [← hAgrp]; exact hGA _ τ.2
      obtain ⟨g, hg⟩ := hτA
      have hgK : (g : Perm (Fin n)) ∈ K'' := (hKW g).2 ⟨g.2, by
        rw [hGs]; convert τ.2 using 1⟩
      refine ⟨⟨g, hgK⟩, ?_⟩
      rw [MonoidHom.comp_apply]
      have : σ ⟨g, hgK⟩ = τ := Subtype.ext (by rw [hσ]; exact hg)
      rw [this, hτ])))
  have hOK : winSet n W.1 = orbit K'' ((e u : ↥(winSet n Δ)) : Fin n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, rfl⟩ := (hWO x).1 hx
      obtain ⟨τ, hτ⟩ := mem_orbit_iff.1 hk
      have hτA : (τ : Perm (Fin Δ.length)) ∈ ρ.range := by rw [← hAgrp]; exact hGA _ τ.2
      obtain ⟨g, hg⟩ := hτA
      have hgK : (g : Perm (Fin n)) ∈ K'' := (hKW g).2 ⟨g.2, by
        rw [hGs]; convert τ.2 using 1⟩
      refine mem_orbit_iff.2 ⟨⟨g, hgK⟩, ?_⟩
      show (g : Perm (Fin n)) _ = _
      rw [← hρ g u, hg]
      rw [← hτ]
      rfl
    · intro hx
      obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hx
      exact fwd g g.2 _ ((hWO _).2 ⟨u, mem_orbit_self u, rfl⟩)
  have htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) :=
    hϕ'4 (isTransitive_restrictTo_of_eq_orbit hOK hinv'')
  have hvl' : VeryLargeK (alignDomKeys (A, o)).length
      (maxOrbitLength (decGroup W.1.length (primitiveWindowInput W).1)) := by
    rw [hMs]
    refine VeryLargeK.mono hLP' (maxOrbitLength_le fun x => ?_)
    refine (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← hOW, ← Nat.card_coe_set_eq]
    exact card_orbit_le_maxOrbitLength _ u
  have hpos : 0 < W.1.length := by omega
  let x0 : Fin W.1.length := ⟨0, hpos⟩
  have haff : Affected ϕ' x0 := by
    apply hϕ'3 x0
    rw [affected_restrictFactor, affected_permCongr]
    obtain ⟨k, hk, hkx⟩ := (hWO _).1 (e'' x0).2
    intro hle'
    apply c.affected k hk
    refine hle'.trans ?_
    rw [← Subgroup.map_map]
    refine Subgroup.map_mono ?_
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ stabilizer K'' ((e'' x0 : ↥(winSet n W.1)) : Fin n) := hg
    rw [mem_stabilizer_iff] at hg'
    show σ g ∈ stabilizer Dd.toAlignDominant.Gs k
    rw [mem_stabilizer_iff]
    apply he_inj
    show ((e (((σ g : Dd.toAlignDominant.Gs) : Perm (Fin Δ.length)) k) : ↥(winSet n Δ)) :
      Fin n) = _
    rw [hσ, hρ, hkx]
    show _ = ((e k : ↥(winSet n Δ)) : Fin n)
    rw [hkx]
    exact hg'
  have h64 : 64 ≤ W.1.length := by omega
  have hgood := masterHintGoodAt_of_giant (A := alignDomHintAtAction (((A, o), Δ), W)) ϕ' hwf
    htr hgiant hvl' x0 haff h64
  -- the parameter the machine computes is `t(x₀)`
  have htx : (alignDomHintAt (((A, o), Δ), W)).2 = tPoint ϕ' x0 := by
    have h := length_filter_rawTpoint (dom := W.1) (gdom := alignDomKeys (A, o)) rfl rfl hI
      hgiant hvl' x0 (fun _ => true)
    rw [map_encPerm_decPerm hrg, map_encPerm_decPerm hrows, List.filter_true] at h
    show (rawTpoint (alignDomHintAtAction (((A, o), Δ), W), 0)).length = _
    rw [tPoint]
    convert h using 2
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
    exact Iff.rfl
  have hhalf : 2 * alignRMs (A, o) ≤ m := by
    rw [← hDms, ← hDm]
    exact Dd.toAlignDominant.param_halved
  refine ⟨?_, hMs.trans hDms, hhalf, fun i hi => ?_⟩
  · show MasterHintGoodAt (alignDomHintAtAction (((A, o), Δ), W))
      (alignDomHintAt (((A, o), Δ), W)).2
    rw [htx]
    exact hgood
  · exact lt_of_mem_alignDomKeys hA.2.1 hX hhd (fun _ _ => by
      rw [hMs, hDms]; omega) hi


/-- `Algo.alignDomHintAt_good_alpha` at `α = 3/4`, the threshold of line 4c. -/
theorem alignDomHintAt_good {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) {gN : RawGens}
    (hinvN : IsInvariant (decGroup n gN) (winSet n Δ))
    {A : RawAction} {ϕ : decGroup Δ.length A.1.2 →* Perm (Fin m)}
    (hAgrp : decGroup Δ.length A.1.2 = (winRestrictHom n Δ hnd hlt (decGroup n gN) hinvN).range)
    (hA : RawAction.WF Δ.length m A ϕ) (hG : IsTransitive (decGroup Δ.length A.1.2))
    (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup Δ.length A.1.2)))
    {t : ℕ} (ht : ∀ u : Fin Δ.length, tPoint ϕ u = t) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    (hZ : IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m)
    (hmn : m ≤ Δ.length)
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hnt : 2 ≤ alignRMs (A, o))
    (hLP : VeryLargeK (alignRMs (A, o))
      (maxOrbitLength (decGroup Δ.length (alignPairG1 (A, o)))))
    {W : RawWinSI} (hndW : W.1.Nodup) (hltW : ∀ x ∈ W.1, x < n) (hwfW : RawGens.WF n W.2.1)
    (hKW : ∀ g, g ∈ decGroup n W.2.1 ↔ ∃ h : g ∈ decGroup n gN,
      winRestrictHom n Δ hnd hlt (decGroup n gN) hinvN ⟨g, h⟩ ∈
        decGroup Δ.length (alignPairG1 (A, o)))
    {u : Fin Δ.length}
    (hu : u ∈ winSet Δ.length (alignRDomWindow (alignRColorOf (A, o),
      alignRDomColor (alignRColorOf (A, o)))))
    (hwinW : ∀ x : Fin n, x ∈ winSet n W.1 ↔
      ∃ k ∈ orbit (decGroup Δ.length (alignPairG1 (A, o))) u,
        ((winEquiv n Δ hnd hlt k : ↥(winSet n Δ)) : Fin n) = x)
    (hbig : 2 * Δ.length < 3 * W.1.length) :
    MasterHintGood (W, alignDomHintAt (((A, o), Δ), W)) ∧
      (alignDomHintAt (((A, o), Δ), W)).1.1.length = alignRMs (A, o) ∧
      2 * alignRMs (A, o) ≤ m ∧ ∀ i ∈ (alignDomHintAt (((A, o), Δ), W)).1.1, i < m :=
  alignDomHintAt_good_alpha hnd hlt hinvN hAgrp hA hG hϕ hvl ht hK hX (by norm_num) hZ hm hmn hhd hnt
    hLP hndW hltW hwfW hKW hu hwinW hbig

end NodeSpec

end Algo
