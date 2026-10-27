/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4d with a dominant color class: the hint routine `H4` of Procedure Align,
line 11 (§14.1, as repaired in the corrected paper).
-/
import Workspace.Algo.TopMasterHintedFinal
import Workspace.Algo.AlignDomHintL57
import Workspace.Algo.PrimitiveLine4dDomData

/-!
# The hint routine of line 4d

At a node of route `4` where line 6 of Procedure Align finds a dominant color class, the
carrier `Algo.line4dDomOps` runs lines 7–11 of Procedure Align on the window `Δ`. In case 3 of
the repair of lines 7–11 (a dominant class and `m*` large: the header's test `Algo.l57Small`
fails), the first call of the Chain Rule over the orbits of `G*` is on the dominant orbit of
`G*` and carries the Johnson hint of line 11: the action of `G*` on `Γ*` through `ϕ*`
.

The node carrier asks a hint routine for the hint of each call, after lifting the call to the
node's domain (`Algo.MasterOps.withHint`). This file gives that routine for line 4d, as
`Algo.masterL57Hint` does for lines 5–7:

* `Algo.line4dDomHintTest`: case 3 of the repair (`Algo.l57Small` fails on the header of
  line 4d) and a call on more than `2|Δ|/3` points;
* `Algo.line4dDomHint`: the routine, `H4` of `Algo.masterNodeHOps`: at the hinted call, the
  hint of `Algo.alignDomHintAt` for the action and the fixed outcome of Procedure Align on the
  node's window; at every other call, none;
* `Algo.quasiFun_line4dDomHint`: it runs in quasipolynomial time.
-/
set_option synthInstance.maxSize 2048

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- §14.1, line 11, **the test for the hinted call of line 4d**: case 3 of the repair of
lines 7–11 (the header of line 4d is not in case 1, `Algo.l57Small`) and a call on more than
`2|Δ|/3` points. -/
def line4dDomHintTest (c tt dd : ℕ) (z : (RawMasterSI × ℕ × ADState) × RawMasterSI) : Bool :=
  !l57Small (line4dDomHdr c tt dd (line4dHint z.1.1)) &&
    decide (2 * z.1.1.1.1.length < 3 * z.2.1.1.length)

/-- §14.1, line 11, on the Master's node: **the hint routine of line 4d** (`H4` of
`Algo.masterNodeHOps`). At the hinted call it returns the hint of `Algo.alignDomHintAt` for the
action and the fixed outcome of Procedure Align on the node's window; at every other call,
none. -/
def line4dDomHint (c tt dd : ℕ) (z : (RawMasterSI × ℕ × ADState) × RawMasterSI) :
    Option RawMasterHint :=
  if line4dDomHintTest c tt dd z then
    some (alignDomHintAt ((((line4dDomHdr c tt dd (line4dHint z.1.1)).1,
      (line4dDomHdr c tt dd (line4dHint z.1.1)).2.1), z.1.1.1.1), z.2.1))
  else none

section Poly

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem quasiFun_line4dDomHintHdr (c tt dd : ℕ) :
    QuasiFun (fun z : (RawMasterSI × ℕ × ADState) × RawMasterSI =>
      line4dDomHdr c tt dd (line4dHint z.1.1)) :=
  (pfst (pfst polyFun_id)).comp_quasiFun (quasiFun_line4dDomHdrAt (c := c) (tt := tt) (dd := dd))

theorem quasiFun_line4dDomHintTest (c tt dd : ℕ) :
    QuasiFun (line4dDomHintTest c tt dd) := by
  let Z := (RawMasterSI × ℕ × ADState) × RawMasterSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have h1 : QuasiFun (fun z : Z => !l57Small (line4dDomHdr c tt dd (line4dHint z.1.1))) :=
    (quasiFun_line4dDomHintHdr c tt dd).comp_poly
      (polyFun_l57Small.comp ((PolyFun.ite polyFun_id (polyFun_const false)
        (polyFun_const true)).of_eq (fun x => by cases x <;> rfl)))
  have h2 : PolyFun (fun z : Z => decide (2 * z.1.1.1.1.length < 3 * z.2.1.1.length)) :=
    ((((pfst (pfst (pfst (pfst i)))).comp polyFun_length).comp
      ((polyFun_const 2).mul polyFun_id)).pair
      (((pfst (pfst (psnd i))).comp polyFun_length).comp
        ((polyFun_const 3).mul polyFun_id))).comp polyFun_natLt
  exact ((h1.pair h2.quasiFun).comp_poly (polyFun_and polyFun_fst polyFun_snd)).of_eq
    (fun _ => rfl)

/-- **The hint routine of line 4d runs in quasipolynomial time.** -/
theorem quasiFun_line4dDomHint (c tt dd : ℕ) : QuasiFun (line4dDomHint c tt dd) := by
  let Z := (RawMasterSI × ℕ × ADState) × RawMasterSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have harg : QuasiFun (fun z : Z => ((((line4dDomHdr c tt dd (line4dHint z.1.1)).1,
      (line4dDomHdr c tt dd (line4dHint z.1.1)).2.1), z.1.1.1.1), z.2.1)) :=
    ((((quasiFun_line4dDomHintHdr c tt dd).comp_poly
      (polyFun_fst.pair (pfst polyFun_snd))).pair
      (pfst (pfst (pfst (pfst i)))).quasiFun)).pair (pfst (psnd i)).quasiFun
  have hall : QuasiFun (fun z : Z => (line4dDomHintTest c tt dd z,
      ((((line4dDomHdr c tt dd (line4dHint z.1.1)).1,
        (line4dDomHdr c tt dd (line4dHint z.1.1)).2.1), z.1.1.1.1), z.2.1))) :=
    (quasiFun_line4dDomHintTest c tt dd).pair harg
  exact (hall.comp_poly (PolyFun.ite polyFun_fst
    ((psnd polyFun_id).comp (polyFun_alignDomHintAt.comp polyFun_some))
    (polyFun_const none))).of_eq (fun z => by
      unfold line4dDomHint
      cases line4dDomHintTest c tt dd z <;> rfl)

end Poly

end Algo
