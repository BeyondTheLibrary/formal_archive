/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Sec. 15, lines 5–7 as one round — the two phases of Procedure
AggregateCertificates (Sec. 13.2), then the dispatch on the outcome of Theorem 13.2.1, then
Procedure Align over the versions (Eq. (71), §14.1).
-/
import Workspace.Algo.AggNodeAggregateRAM
import Workspace.Algo.AggNodeContinuation
import Workspace.Algo.AlignOutcomeLab
import Workspace.Algo.AlignVersionsCost
import Workspace.Algo.AlignColorRaw
import Workspace.Algo.AlignDomWindows
import Workspace.Algo.AlignDescentCost

/-!
# Sec. 15, lines 5–7, as one round

The round runs in three stretches, all on the node `(C, none)` of the aggregate carrier:

1. the two phases of Procedure AggregateCertificates, exactly as `Algo.aggnAggregateRound`
   runs them (its child and its combine are used unchanged while it still has a child);
2. the dispatch of Theorem 13.2.1 (`Algo.aggnContinuation`), read off the completed stores:
   it gives the versions of `X(x)` and of `X(y)` (tags `1`, `3`, `4`), or no versions at all
   (the reject exits, tags `0`, `5`, `6`, and the giant branch (2a), tag `2`, which the round
   of Cor. 12.0.10 handles, `top4AggregateEnter`);
3. Procedure Align over the versions of `X(y)` (`Workspace/Algo/AlignVersions.lean`), with
   the first version of `X(x)` as the fixed version `X'`, and as windows the color classes of
   `Ω` of line 4 (`Algo.alignRWindows` for the coloring `Algo.alignOutcomeLab` of `X'`), where
   in cases 2 and 3 of the repair of lines 7–11 the dominant window is
   replaced by the orbits of `G*` inside it (`Algo.alignL57Windows`). In case 1 of the repair
   (a dominant class with `m*` small, `Algo.alignRSmall`), stretch 3 runs instead the loop of
   `Workspace/Algo/AlignDescentLoop.lean`: for each version, the strong descent to `ker ϕ*`
   on the dominant window, then the Chain Rule over the other classes (`Algo.l57Child`,
   `Algo.l57Step`).

The header of stretch 3 is recomputed from the stores at every step (`Algo.aggnL57Hdr`); the
state keeps only the stores and the position of the loop. The stores are read through the
caps of the aggregate carrier (`Algo.aggnAggregatePack`), which change nothing on the states
the carrier reaches and keep every header small; that is what makes the number of children
bounded by a function of the node (`Algo.aggnL57Cap`).

The answer is the gathered coset of stretch 3, with its generators and its representative
normalized (`Algo.rawCosetNorm`), and the empty coset when stretch 3 made no call.
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The state: the state of the aggregate carrier and, once stretch 3 has made a call, the
state of the loop over the versions. The loop of case 1 uses the whole of `Algo.ADState`;
the plain loop of Eq. (71) uses its first component and keeps the rest at `(0, none)`. -/
abbrev AggnL57State := AggnAggregateState × Option ADState

/-- The dispatch of Theorem 13.2.1, read off the stores. -/
def aggnL57Cont (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AggnContOut :=
  aggnContinuation c b t d z

/-- The fixed version `X'` of `X(x)`: the first one listed. -/
def aggnL57Fixed (o : AggnContOut) : RawAlignOutcome := o.2.1.headD (none, none)

/-- The header of Eq. (71) for a node and a state of the aggregate carrier (before the caps):
the action, `X'`, the versions of `X(y)`, the windows of lines 5 and 6, and the two strings. -/
def aggnL57HdrCore (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AVHdr :=
  (z.1.1, aggnL57Fixed (aggnL57Cont c b t d z), (aggnL57Cont c b t d z).2.2,
    alignL57Windows (z.1.1, aggnL57Fixed (aggnL57Cont c b t d z)),
    z.1.2.1, z.1.2.2.1)

/-- The header of Eq. (71), read through the caps of the aggregate carrier. -/
def aggnL57Hdr (c b t d dc dp : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AVHdr :=
  aggnL57HdrCore c b t d (z.1, aggnAggregatePack c dc dp z.1 z.2)

/-- The number of calls Eq. (71) may make: versions times windows. -/
def avCalls (h : AVHdr) : ℕ := h.2.2.1.length * h.2.2.2.1.length

/-- §14.1, lines 7–11: does stretch 3 run case 1 of the repair (a dominant class carrying a
nontrivial structure, `m*` small)?  Line 7 goes on only when the structure on the dominant
class `Δ_j` is nontrivial (*"a nontrivial equipartition of `Δ_j`"*, or a Johnson scheme), that
is when `m* ≥ 2`; with `m* < 2` the class is a single block and the Chain Rule of lines 5–6
runs with the window `Ω(Δ_j)` as it is (as in `Algo.line4dHasDom` for line 4d). -/
def l57Small (h : AVHdr) : Bool :=
  alignRSmall (h.1, h.2.1) && decide (2 ≤ alignRMs (h.1, h.2.1))

theorem alignRSmall_of_l57Small {h : AVHdr} (hs : l57Small h = true) :
    alignRSmall (h.1, h.2.1) = true := (Bool.and_eq_true_iff.1 hs).1

theorem two_le_alignRMs_of_l57Small {h : AVHdr} (hs : l57Small h = true) :
    2 ≤ alignRMs (h.1, h.2.1) := of_decide_eq_true (Bool.and_eq_true_iff.1 hs).2

theorem l57Small_eq_of_two_le {h : AVHdr} (h2 : 2 ≤ alignRMs (h.1, h.2.1)) :
    l57Small h = alignRSmall (h.1, h.2.1) := by
  unfold l57Small
  rw [decide_eq_true h2, Bool.and_true]

/-- The number of calls stretch 3 may make. -/
def l57Calls (h : AVHdr) : ℕ := if l57Small h then adCalls h else avCalls h

/-- The state before the first version. -/
def l57Init (h : AVHdr) : ADState := if l57Small h then adInit h else (avInit h, 0, none)

/-- The next call of stretch 3. -/
def l57Child (p : AVHdr × ADState) : Option RawWinSI :=
  if l57Small p.1 then adChild p else avChild (p.1, p.2.1)

/-- One step of stretch 3 after the answer of a call. -/
def l57Step (p : AVHdr × ADState × RawCoset) : ADState :=
  if l57Small p.1 then adCombine p else (avCombine (p.1, p.2.1.1, p.2.2), 0, none)

/-- A window instance of stretch 3 as a child node of the carrier, normalized as the
aggregate carrier normalizes its children. -/
def avEmb (p : AggnPhaseCtx × RawWinSI) : AggnPhaseNode :=
  (p.1, some (aggnCheckedWindow (p.1.2.1, p.2)))

/-- The child of stretch 3. -/
def aggnL57AlignChild (c b t d dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnL57State) :
    Option AggnPhaseNode :=
  z.1.2.elim
    (if z.2.1 < aggnAggregateWidth c z.1.1 + l57Calls (aggnL57Hdr c b t d dc dp (z.1.1, z.2.2.1))
    then
      (l57Child (aggnL57Hdr c b t d dc dp (z.1.1, z.2.2.1),
        z.2.2.2.getD (l57Init (aggnL57Hdr c b t d dc dp (z.1.1, z.2.2.1))))).map
        (fun J => avEmb (z.1.1, J))
    else none)
    (fun _ => none)

/-- §15, lines 5–7: **the child**. While the aggregate carrier has a child, it is that child;
afterwards it is the child of stretch 3. -/
def aggnL57Child (c b t d dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnL57State) :
    Option AggnPhaseNode :=
  (aggnAggregateChild c (z.1, z.2.1, z.2.2.1)).elim (aggnL57AlignChild c b t d dc dp z) some

/-- §15, lines 5–7: **the combine**, following the same split as the child. In stretch 3 the
stores are kept through the caps of the carrier, which change nothing on the states the
two phases end in; so the state stays small whatever it was. -/
def aggnL57Combine (c b t d dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnL57State × RawCoset) :
    AggnL57State :=
  (aggnAggregateChild c (z.1, z.2.1, z.2.2.1.1)).elim
    (aggnAggregatePack c dc dp z.1.1 z.2.2.1.1, some (l57Step (aggnL57Hdr c b t d dc dp (z.1.1, z.2.2.1.1),
      z.2.2.1.2.getD (l57Init (aggnL57Hdr c b t d dc dp (z.1.1, z.2.2.1.1))), z.2.2.2)))
    (fun _ => (aggnAggregateCombine c dc dp (z.1, z.2.1, z.2.2.1.1, z.2.2.2), none))

/-- §15, lines 5–7: **the answer**, the gathered coset of stretch 3. -/
def aggnL57Finish (z : AggnPhaseNode × AggnL57State) : RawCoset :=
  rawCosetNorm (z.1.1.2.1, z.2.2.elim none (fun st => st.1.2.2.2))

/-- The size of a capped state of the aggregate carrier, bounded by the node alone. -/
theorem aggnAggregatePack_size (c dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    Enc.size (aggnAggregatePack c dc dp C s) ≤
      16 * (aggnStateCap dc C.2.1.length + aggnCompareStateCap dp C.2.1.length +
        aggnCompareWidth c C + 2) :=
  aggnAggregateState_size (aggnCapState_size dc _ _) (Nat.min_le_right _ _)
    (aggnCompareCapState_size dp _ _)

/-- The header routine before the caps is quasipolynomial. -/
theorem quasiFun_aggnL57HdrCore (c b t d : ℕ) : QuasiFun (aggnL57HdrCore c b t d) := by
  have i : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z) := polyFun_id
  have hA := (i.comp polyFun_fst).comp polyFun_fst
  have hx := ((i.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hy := (((i.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have ho : QuasiFun (aggnL57Cont c b t d) := aggnQuasiFun_continuation c b t d
  have hfix : PolyFun aggnL57Fixed :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_headOption).pair
      (polyFun_const ((none, none) : RawAlignOutcome))).comp polyFun_optionGetD).of_eq
      (fun o => by unfold aggnL57Fixed; cases o.2.1 <;> rfl)
  have hX : QuasiFun (fun z => aggnL57Fixed (aggnL57Cont c b t d z)) := ho.comp_poly hfix
  have hvers : QuasiFun (fun z => (aggnL57Cont c b t d z).2.2) :=
    ho.comp_poly (polyFun_snd.comp polyFun_snd)
  have hwin : QuasiFun (fun z : AggnPhaseCtx × AggnAggregateState =>
      alignL57Windows (z.1.1, aggnL57Fixed (aggnL57Cont c b t d z))) :=
    (hA.quasiFun.pair hX).comp_poly polyFun_alignL57Windows
  exact hA.quasiFun.pair (hX.pair (hvers.pair (hwin.pair (hx.quasiFun.pair hy.quasiFun))))

theorem quasiFun_aggnL57Hdr (c b t d dc dp : ℕ) : QuasiFun (aggnL57Hdr c b t d dc dp) :=
  (polyFun_fst.quasiFun.pair (aggnQuasiFun_aggregatePack c dc dp)).comp
    (quasiFun_aggnL57HdrCore c b t d)

/-- The calls of stretch 3 for one header are at most a quasipolynomial function of its
size: the versions and the classes are listed in the header, and the orbits of `ker ϕ*` and
its cosets are computed from it by `RAM.QuasiFun` routines. -/
theorem l57Calls_bdd : ∃ K : ℕ → ℕ, QuasiPolyBound K ∧ Monotone K ∧
    ∀ h, l57Calls h ≤ K (Enc.size h) := by
  obtain ⟨cK, hK⟩ := polyFun_adKO.quasiFun.size
  obtain ⟨cR, hR⟩ := ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp_quasiFun
    quasiFun_adRightReps : QuasiFun (fun h : AVHdr => adRightReps (h.1, h.2.1))).size
  let W := fun c N : ℕ => 2 ^ ((Nat.log 2 N + 2) ^ c)
  refine ⟨fun N => N * (W cR N * W cK N + N), ?_, ?_, ?_⟩
  · exact polyBound_id.quasiPoly.mul (((quasiPolyBound_witness cR).mul
      (quasiPolyBound_witness cK)).add polyBound_id.quasiPoly)
  · intro a b hab
    have h1 := quasiPolyBound_witness_mono cR hab
    have h2 := quasiPolyBound_witness_mono cK hab
    exact Nat.mul_le_mul hab (Nat.add_le_add (Nat.mul_le_mul h1 h2) hab)
  intro h
  have hL : h.2.2.1.length ≤ Enc.size h :=
    (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans (size_snd_le' _)))
  have hWs : h.2.2.2.1.length ≤ Enc.size h :=
    (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans
      ((size_snd_le' _).trans (size_snd_le' _))))
  have hTW : (adTW h).length ≤ Enc.size h := by
    have : (adTW h).length ≤ h.2.2.2.1.length := by
      unfold adTW; rw [List.length_tail]; omega
    omega
  have hKO : (adKO h).length ≤ W cK (Enc.size h) := (length_le_size _).trans (hK h)
  have hRN : adRN h ≤ W cR (Enc.size h) := (length_le_size _).trans (hR h)
  unfold l57Calls
  split_ifs
  · unfold adCalls
    exact Nat.mul_le_mul hL (Nat.add_le_add (Nat.mul_le_mul hRN hKO) hTW)
  · unfold avCalls
    exact Nat.mul_le_mul hL (hWs.trans (Nat.le_add_left _ _))

/-- **The number of calls of stretch 3 is bounded by a function of the node.** The header is
a quasipolynomial function of the node and a capped state, whose size is bounded by the node
alone. -/
theorem aggnL57Calls_bdd (c b t d dc dp : ℕ) : ∃ K : ℕ → ℕ, QuasiPolyBound K ∧ Monotone K ∧
    ∀ C s, l57Calls (aggnL57Hdr c b t d dc dp (C, s)) ≤
      K (2 * Enc.size C + 2 * (16 * (aggnStateCap dc C.2.1.length +
        aggnCompareStateCap dp C.2.1.length + aggnCompareWidth c C + 2))) := by
  obtain ⟨e, he⟩ := (quasiFun_aggnL57HdrCore c b t d).size
  obtain ⟨K0, hK0, hK0m, hK0c⟩ := l57Calls_bdd
  refine ⟨fun X => K0 (2 ^ ((Nat.log 2 X + 2) ^ e)), hK0.comp (quasiPolyBound_witness e),
    fun a b hab => hK0m (quasiPolyBound_witness_mono e hab), fun C s => ?_⟩
  set h := aggnL57Hdr c b t d dc dp (C, s)
  have hsz : Enc.size h ≤ 2 ^ ((Nat.log 2 (Enc.size (C, aggnAggregatePack c dc dp C s)) + 2) ^ e) :=
    he (C, aggnAggregatePack c dc dp C s)
  have hin : Enc.size (C, aggnAggregatePack c dc dp C s) ≤
      2 * Enc.size C + 2 * (16 * (aggnStateCap dc C.2.1.length +
        aggnCompareStateCap dp C.2.1.length + aggnCompareWidth c C + 2)) := by
    have := Combine.size_pair_le C (aggnAggregatePack c dc dp C s)
    have := aggnAggregatePack_size c dc dp C s
    omega
  exact (hK0c h).trans (hK0m (hsz.trans (quasiPolyBound_witness_mono e hin)))

/-- The width reserved for stretch 3: the largest number of calls a header of the node may
ask for. It is used only in the analysis. -/
noncomputable def aggnL57Cap (c b t d dc dp : ℕ) (C : AggnPhaseCtx) : ℕ :=
  sSup (Set.range fun s : AggnAggregateState => l57Calls (aggnL57Hdr c b t d dc dp (C, s)))

theorem l57Calls_le_cap (c b t d dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    l57Calls (aggnL57Hdr c b t d dc dp (C, s)) ≤ aggnL57Cap c b t d dc dp C := by
  obtain ⟨K, -, -, he⟩ := aggnL57Calls_bdd c b t d dc dp
  exact le_csSup ⟨_, by rintro _ ⟨s', rfl⟩; exact he C s'⟩ ⟨s, rfl⟩

theorem aggnL57Cap_le (c b t d dc dp : ℕ) : ∃ K : ℕ → ℕ, QuasiPolyBound K ∧ Monotone K ∧ ∀ C,
    aggnL57Cap c b t d dc dp C ≤
      K (2 * Enc.size C + 2 * (16 * (aggnStateCap dc C.2.1.length +
        aggnCompareStateCap dp C.2.1.length + aggnCompareWidth c C + 2))) := by
  obtain ⟨K, hK, hKm, he⟩ := aggnL57Calls_bdd c b t d dc dp
  refine ⟨K, hK, hKm, fun C => csSup_le ⟨_, ⟨default, rfl⟩⟩ ?_⟩
  rintro _ ⟨s, rfl⟩
  exact he C s

theorem aggnL57AlignChild_some {c b t d dc dp : ℕ} {z : AggnPhaseNode × ℕ × AggnL57State}
    {J : AggnPhaseNode} (h : aggnL57AlignChild c b t d dc dp z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  cases ho : z.1.2 with
  | some W => simp [aggnL57AlignChild, ho] at h
  | none =>
    simp only [aggnL57AlignChild, ho, Option.elim_none] at h
    split at h
    · obtain ⟨W, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨rfl, W, rfl⟩
    · simp at h

theorem aggnL57Child_some {c b t d dc dp : ℕ} {z : AggnPhaseNode × ℕ × AggnL57State}
    {J : AggnPhaseNode} (h : aggnL57Child c b t d dc dp z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  unfold aggnL57Child at h
  cases ha : aggnAggregateChild c (z.1, z.2.1, z.2.2.1) with
  | none =>
    rw [ha, Option.elim_none] at h
    exact aggnL57AlignChild_some h
  | some J' =>
    rw [ha, Option.elim_some] at h
    cases h
    exact aggnAggregateChild_some ha

/-- §15, lines 5–7: **the round.** The node is that of the aggregate carrier; the children are
the window instances of the two phases and then those of the Chain Rule of line 5. -/
noncomputable def aggnL57Round (c b t d dc dp : ℕ) :
    Round AggnPhaseNode AggnL57State RawCoset where
  WF := fun I => AggnCheckedWF I.1.2.1.length I
  ground := fun I => I.1.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnAggregateWidth c I.1 + aggnL57Cap c b t d dc dp I.1) (fun _ => 0)
  child := aggnL57Child c b t d dc dp
  init := fun I => (aggnAggregateInit c dc dp I, none)
  combine := aggnL57Combine c b t d dc dp
  finish := aggnL57Finish
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold aggnL57Child
    cases ho : I.2 with
    | some W =>
      have h1 : aggnAggregateChild c (I, j, s.1) = none := by
        simp [aggnAggregateChild, ho]
      rw [h1, Option.elim_none]
      simp [aggnL57AlignChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      have h1 : aggnAggregateChild c (I, j, s.1) = none :=
        (aggnAggregateRound c dc dp).child_eq_none I j s.1 (by
          show I.2.elim (aggnAggregateWidth c I.1) (fun _ => 0) ≤ j
          rw [ho]; exact le_trans (Nat.le_add_right _ _) hj)
      rw [h1, Option.elim_none]
      simp only [aggnL57AlignChild, ho, Option.elim_none]
      rw [if_neg]
      have := l57Calls_le_cap c b t d dc dp I.1 s.1
      omega
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnL57Child_some hJ
    refine ⟨rfl, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    exact aggnCheckedWindow_wf _ _
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnL57Child_some hJ
    show (some _ : Option RawWinSI).elim 1 (fun _ => 0) < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnL57Child_some hJ
    exact le_rfl

end Algo
