import Workspace.Algo.TopMasterHintedL57
import Workspace.Algo.TopMasterRoute4

/-! # Theorem 1.1.1 on the RAM from the open route obligations of the hinted carrier

Section 15, the Master Algorithm, on the RAM with the hinted children of line 11 of Procedure
Align. `Algo.siWorkspaceRoutine_of_hintedSupply` proves the workspace routine
of Theorem 1.1.1 from a list of hypotheses, several of which are proved elsewhere. This file
discharges those:

* the Cameron routine of line 4a (`Algo.exists_polyFun_cameronSpec`),
* the caps of the window rounds (`Algo.topwpCap_exists`, `Algo.top4wCap_exists`),
* the bounds of the Extended Design Lemma of line 4c (`Algo.exists_line4cBounds`),
* the reserve exponent of the round of lines 5–7 (`Algo.exists_masterL57EOK`),
* the carrier `GD = Algo.line4dDomOps` of line 4d with a dominant class, its costs
  (`Algo.line4dDomOps_cost`) and the well-formedness of its answers
  (`Algo.line4dDomOps_finish_wf`),
* route 4 at nodes where line 6 of Procedure Align finds no dominant class
  (`Algo.masterRoute4_noDom_treeOK`, carried over to the hinted carrier, whose children agree
  there with those of the full node carrier).

What is left in `Algo.siWorkspaceRoutine_of_openRoutes` is exactly:

* the two hint routines `H4`, `H5` of line 11 and their running time (`QuasiFun`),
* a quasipolynomial, monotone bound `q45` on the calls of routes 4 and 5,
* route 4 with a dominant class (`Algo.MasterRoute4Dom` for the hinted carrier), and
* route 5 (`Algo.MasterL57SupplyH`, the hinted call of line 11 allowed).
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ### Route 4 of the hinted carrier without a dominant class -/

section Route4

variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    {n : ℕ}

/-- **Section 15, lines 4c–4d: route `4` of the hinted node carrier.** Where line 6 of
Procedure Align finds no dominant color class, the hinted carrier proposes the children of the
full node carrier (`Algo.masterNodeH_child_eq`), so the tree of
`Algo.masterRoute4_noDom_treeOK` serves (loop of Eq. (71), every call on at most `4|Δ|/5`
points, Eq. (72)). Where it finds one, the tree is the obligation `Algo.MasterRoute4Dom` of
the hinted carrier, whose children may carry the hint of line 11. -/
theorem masterParamRoute4H {a b : ℕ} (hb : Line4cBounds c tt dd)
    {q : ℕ → ℕ} (hq : ∀ k, masterRoute4Cost c tt dd k ≤ q k)
    (hD : MasterRoute4Dom (masterAdmittedRound a b
      (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n q
      c tt dd) :
    MasterParamRoute (masterAdmittedRound a b
      (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n q 4 := by
  intro W h hg hwf hr
  cases hd : masterHasDom c tt dd ((W, some h) : RawMasterSI)
  · obtain ⟨T, hT⟩ := masterRoute4_noDom_treeOK (a := a) (b := b) (B := B) (C₀ := C₀)
      (cameron := cameron) (e := e) (f := f) (u := u) (v := v) (GD := GD) (dD := dD)
      (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) hb hg hr hd
    have hr' : masterRoute ((W, some h) : RawMasterSI) = masterHintRoute (W, h) := rfl
    refine ⟨T, (MasterNodeTreeOK.toH (H4 := H4) (H5 := H5) ?_ (fun _ => hd) hT).mono_q hq⟩
    rw [hr', hr]
    decide
  · exact hD W h hg hwf hr hd

end Route4

/-! ### The constants chosen by the existence lemmas -/

/-- A Cameron routine for line 4a: polynomial time with the specification of Theorem 11.2.3
(`Algo.exists_polyFun_cameronSpec`). -/
noncomputable def masterCameron : RawGens × List ℕ → Option RawCameron :=
  Classical.choose exists_polyFun_cameronSpec

theorem masterCameron_spec : PolyFun masterCameron ∧ CameronSpec masterCameron :=
  Classical.choose_spec exists_polyFun_cameronSpec

/-- The caps `e f` of the window rounds (`Algo.topwpCap_exists`). -/
noncomputable def masterTopE : ℕ := Classical.choose topwpCap_exists

/-- The caps `e f` of the window rounds (`Algo.topwpCap_exists`). -/
noncomputable def masterTopF : ℕ := Classical.choose (Classical.choose_spec topwpCap_exists)

theorem masterTopEF_spec : TopwpCap masterTopE masterTopF :=
  Classical.choose_spec (Classical.choose_spec topwpCap_exists)

/-- The caps `u v` of the round of line 4 on the window (`Algo.top4wCap_exists`). -/
noncomputable def masterTopU : ℕ := Classical.choose (top4wCap_exists masterTopE masterTopF)

/-- The caps `u v` of the round of line 4 on the window (`Algo.top4wCap_exists`). -/
noncomputable def masterTopV : ℕ :=
  Classical.choose (Classical.choose_spec (top4wCap_exists masterTopE masterTopF))

theorem masterTopUV_spec : Top4wCap masterTopE masterTopF masterTopU masterTopV :=
  Classical.choose_spec (Classical.choose_spec (top4wCap_exists masterTopE masterTopF))

/-- The bounds `tt dd` of the Extended Design Lemma of line 4c for the constant `c`
(`Algo.exists_line4cBounds`). -/
noncomputable def masterLine4TT (c : ℕ) : ℕ := Classical.choose (exists_line4cBounds c)

/-- The bounds `tt dd` of the Extended Design Lemma of line 4c for the constant `c`
(`Algo.exists_line4cBounds`). -/
noncomputable def masterLine4DD (c : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_line4cBounds c))

theorem masterLine4_spec (c : ℕ) : Line4cBounds c (masterLine4TT c) (masterLine4DD c) :=
  Classical.choose_spec (Classical.choose_spec (exists_line4cBounds c))

/-- The reserve exponent of the round of lines 5–7 (`Algo.exists_masterL57EOK`). -/
noncomputable def masterL57E (c' b' t d dc dp : ℕ) : ℕ :=
  Classical.choose (exists_masterL57EOK c' b' t d dc dp masterTopE masterTopF)

theorem masterL57E_spec (c' b' t d dc dp : ℕ) :
    MasterL57EOK c' b' t d dc dp masterTopE masterTopF (masterL57E c' b' t d dc dp) :=
  Classical.choose_spec (exists_masterL57EOK c' b' t d dc dp masterTopE masterTopF)

/-- **The node carrier of the Master Algorithm on the RAM with the hinted children of line
11**, at the constants chosen above: `Algo.masterNodeHOps` with `GD = Algo.line4dDomOps` for
line 4d with a dominant class, the hint routine `H4` on its children and `H5` on the children
of the round of lines 5–7. The constant `c` is that of line 4c, and `c' b' t d dc dp` those of
lines 5–7. -/
noncomputable abbrev masterFinalOps (c c' b' t d dc dp : ℕ)
    (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint) :=
  masterNodeHOps masterLine1B masterLine1C₀ masterCameron masterTopE masterTopF masterTopU
    masterTopV c (masterLine4TT c) (masterLine4DD c)
    (line4dDomOps c (masterLine4TT c) (masterLine4DD c)) default c' b' t d dc dp
    (masterL57E c' b' t d dc dp) H4 H5

set_option synthInstance.maxSize 4096 in
/-- **Theorem 1.1.1 on the RAM, from the open obligations of routes 4 and 5 only.** The Master
Algorithm (Section 15) with the hinted children of line 11 of Procedure Align
solves String Isomorphism in quasipolynomial time, given

* hint routines `H4` (line 4d) and `H5` (lines 5–7) that run in quasipolynomial time,
* a monotone quasipolynomial bound `q45`,
* route 4 with a dominant class (`Algo.MasterRoute4Dom`): at every good admitted node of
  route 4 where line 6 of Align finds a dominant class, a tree the hinted carrier walks with
  good children that make progress (Sec. 11.4: window at most `4/5`, or window kept and
  parameter at most halved, Eq. (73)), correct, with at most `q45` calls, and
* route 5 (`Algo.MasterL57SupplyH`): at every such node of route 5, a window tree of the round
  of lines 5–7 with the same properties, whose calls either have at most `4/5` of the window
  or carry a hint of `H5` with its meaning and a halved parameter.

Everything else (the Cameron routine, the caps, the bounds of line 4c, the reserve exponent of
lines 5–7, route 4 without a dominant class) is proved. -/
theorem siWorkspaceRoutine_of_openRoutes {c c' b' t d dc dp : ℕ}
    {H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    (hH4 : QuasiFun H4) (hH5 : QuasiFun H5) {q45 : ℕ → ℕ} (hq45 : Monotone q45)
    (hq : QuasiPolyBound q45)
    (h4 : ∀ n, MasterRoute4Dom (masterAdmittedRound masterCapA masterCapB
      (masterFinalOps c c' b' t d dc dp H4 H5)) n q45 c (masterLine4TT c) (masterLine4DD c))
    (h5 : ∀ n, MasterL57SupplyH c' b' t d dc dp masterTopE masterTopF n q45 H5) :
    SIWorkspaceRoutine := by
  obtain ⟨CD⟩ := line4dDomOps_cost (c := c) (tt := masterLine4TT c) (dd := masterLine4DD c)
    masterCapA masterCapB
  let q : ℕ → ℕ := fun k => masterRoute4Cost c (masterLine4TT c) (masterLine4DD c) k + q45 k
  have hqm : Monotone q := (masterRoute4Cost_mono _ _ _).add hq45
  have hqq : QuasiPolyBound q := (quasiPolyBound_masterRoute4Cost _ _ _).add hq
  refine siWorkspaceRoutine_of_hintedRoutes (c := c) (tt := masterLine4TT c)
    (dd := masterLine4DD c) (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp)
    (E := masterL57E c' b' t d dc dp) masterCameron_spec.1 masterCameron_spec.2
    masterTopEF_spec masterTopUV_spec default CD hH4 hH5 hqm hqq
    (fun n P s hP => line4dDomOps_finish_wf P s hP) (fun n => ?_) (fun n => ?_)
  · refine masterParamRoute4H (masterLine4_spec c) (fun k => Nat.le_add_right _ _) ?_
    intro W h hg hwf hr hd
    obtain ⟨T, hT⟩ := h4 n W h hg hwf hr hd
    exact ⟨T, hT.mono_q fun k => Nat.le_add_left _ _⟩
  · intro W h hg hwf hr
    obtain ⟨T, hT⟩ := masterParamRoute5H_of_supply (cameron := masterCameron) (u := masterTopU)
      (v := masterTopV) (c := c) (tt := masterLine4TT c) (dd := masterLine4DD c)
      (GD := line4dDomOps c (masterLine4TT c) (masterLine4DD c)) (dD := default) (H4 := H4)
      (masterCap_spec n) (masterL57E_spec c' b' t d dc dp) (h5 n) W h hg hwf hr
    exact ⟨T, hT.mono_q fun k => Nat.le_add_left _ _⟩

end Algo
