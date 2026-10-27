/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 4c–4d as one carrier of the Master Algorithm's node on the RAM.
-/
import Workspace.Algo.PrimitiveLine4d
import Workspace.Algo.TopMasterFourOpenCost
import Workspace.Algo.AggNodeLine57RAM
import Workspace.Algo.PrimitiveLine4cCount
import Workspace.Master.Sec15Value

/-!
# Section 15, lines 4c–4d: one carrier on the Master's fold state

> 4c. apply Theorem 9.2.3 to `H(x)` and to `H(y)`
> 4d. apply Procedure Align to `X` (Sec. 14.1)

`Workspace/Algo/PrimitiveLine4d.lean` runs the loop of Eq. (71) on the window `Δ` of the node
and matches it with the Master's round `Babai.AlignShape.red` (`Algo.line4dInner_loopMatch`).
This file puts that loop on the node itself, in the form the Section 15 dispatcher takes for
its hinted nodes (`Algo.masterTopOps`, parameter `H`):

* every call of the loop is an instance on `Δ`; it is lifted to the node's domain
  (`Algo.topwRawInstance`), and its answer is restricted back to `Δ` before the loop goes on
  (`Algo.topwCosetImage`), as for line 4b (`Workspace/Algo/TopFourAmbientMatch.lean`);
* the loop's answer is lifted to the node's domain and shifted by the node's representative,
  Eq. (59), as for line 4b (`Workspace/Algo/TopMasterFourCoset.lean`).

`Algo.line4dOps` is the carrier, `Algo.line4dOps_cost` its local cost data
(`Algo.MasterOpsCost`), and `Algo.line4dOps_match` says that at a node of route `4` (lines
4c–4d) without a dominant color class it walks the lift of the Master's round
`Babai.AlignShape.red` of a `Babai.Line4cdData` call for call; this lift is the one of line 4b,
`Algo.top4wTree` followed by the shift.

The dominant case (lines 7–11 of Procedure Align) is not covered, for the reason given in
`Workspace/Algo/PrimitiveLine4d.lean`.
-/

set_option synthInstance.maxSize 4096

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ## The loop on the node -/

section Loop

variable (c tt dd : ℕ)

/-- The window context of a node: its domain (read off its first string), its group, its
window, and its first string, as for line 4b (`Algo.masterLine4bInput`). -/
def line4dCtx (q : MasterHintInput) : TopwContext :=
  ((q.1.2.2.2.1, q.1.2.1), q.1.1, q.1.2.2.2.1)

/-- A node of the lifted loop: the node, and the lifted call when the instance is one. -/
abbrev Line4dNode := MasterHintInput × Option RawWinSI

/-- The call a node of the lifted loop stands for. -/
def line4dNodeRead (J : Line4dNode) : RawWinSI := J.2.getD ([], [], [], [], [])

/-- The instance a node of the lifted loop stands for. -/
noncomputable def line4dDecode (n : ℕ) (J : Line4dNode) : SIInstance (Fin n) ℕ :=
  decWinSI n (line4dNodeRead J)

/-- Line 4d: the next call of the loop of Eq. (71), lifted to the node's domain. -/
def line4dChild (z : Line4dNode × ℕ × AVState) : Option Line4dNode :=
  z.1.2.elim
    (if z.2.1 < avCalls (line4dHdr c tt dd z.1.1) then
      (avChild (line4dHdr c tt dd z.1.1, z.2.2)).bind fun W =>
        (topwRawInstance (line4dCtx z.1.1, W)).map fun V => (z.1.1, some V)
    else none)
    (fun _ => none)

/-- Line 4d: the loop takes the answer of a lifted call, restricted to the window. -/
def line4dCombine (z : MasterHintInput × ℕ × AVState × RawCoset) : AVState :=
  avCombine (line4dHdr c tt dd z.1, z.2.2.1, topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2))

/-- Line 4d: the answer of the loop, lifted to the node's domain and shifted by the node's
representative (Eq. (59)). -/
def line4dFinish (z : MasterHintInput × AVState) : RawCoset :=
  top3Shift (z.1.1.2.2.2.1, normPerm (z.1.1.2.2.2.1, z.1.1.2.2.1),
    top2NormC z.1.1.2.2.2.1
      (topwCosetPreimage ((z.1.1.2.2.2.1, z.1.1.2.1), z.1.1.1, z.2.2.2.2)))

/-- The lifted loop as a round.  It is a device of the proofs only (`WF` is `False`): the
carrier `Algo.line4dOps` runs these steps. -/
def line4dRound : Round Line4dNode AVState RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := I.2.elim (avCalls (line4dHdr c tt dd I.1)) (fun _ => 0)
  child := line4dChild c tt dd
  init I := avInit (line4dHdr c tt dd I.1)
  combine z := line4dCombine c tt dd (z.1.1, z.2)
  finish z := line4dFinish (z.1.1, z.2)
  bot := none
  child_eq_none := by
    rintro ⟨q, _ | W⟩ j s hj
    · exact if_neg (Nat.not_lt.2 hj)
    · rfl
  child_wf := by
    intro _ _ _ _ h
    exact h.elim
  child_measure := by
    intro _ _ _ _ h
    exact h.elim
  child_ground := by
    intro _ _ _ _ h
    exact h.elim

/-- **The lifted loop walks the lift of the loop on the window.**  Every call of the loop on
the window is asked on the node's domain, every answer is restricted back to the window, and
the answer of the loop is lifted and shifted. -/
theorem line4dRound_lift {n : ℕ} {q : MasterHintInput} {gens : List (Perm (Fin n))}
    (hg : q.1.2.1 = gens.map (encPerm n)) (hd : q.1.2.2.2.1.length = n)
    (hnd : q.1.1.Nodup) (hlt : ∀ i ∈ q.1.1, i < n)
    (hinv : IsInvariant (genGroup gens) (winSet n q.1.1)) :
    ∀ {w j : ℕ} {s : AVState}
      {T : SIReduction (Fin q.1.1.length) ℕ (Set (Perm (Fin q.1.1.length)))},
      LoopMatch line4dInnerRound (line4dInnerDecode q.1.1.length) (decCoset q.1.1.length)
        (line4dHdr c tt dd q, none) w j s T →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n q.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin q.1.1.length)))) →
      T.run ⊆ ((winRestrictHom n q.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin q.1.1.length))) →
      LoopMatch (line4dRound c tt dd) (line4dDecode n) (decCoset n) (q, none) w j s
        ((top4wTree q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1) T).bind
          (fun A => .done (decPerm n q.1.2.2.1 • A))) := by
  have hctx : line4dCtx q = (((q.1.2.2.2.1, gens.map (encPerm n)), q.1.1, q.1.2.2.2.1) :
      TopwContext) := by
    rw [line4dCtx, hg]
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    intro _ hA
    refine .done w j s _ ?_ ?_
    · change line4dChild c tt dd ((q, none), j, s) = none
      change (if j < avCalls (line4dHdr c tt dd q) then
        (avChild (line4dHdr c tt dd q, s)).map (fun J => (line4dHdr c tt dd q, some J))
        else none) = none at hc
      change (if j < avCalls (line4dHdr c tt dd q) then _ else none) = none
      split_ifs at hc ⊢ with hj
      · rw [Option.map_eq_none_iff] at hc
        rw [hc]
        rfl
      · rfl
    · change decCoset q.1.1.length s.2.2.2 = A at ha
      change decCoset n (top3Shift (q.1.2.2.2.1, normPerm (q.1.2.2.2.1, q.1.2.2.1),
        top2NormC q.1.2.2.2.1 (topwCosetPreimage ((q.1.2.2.2.1, q.1.2.1), q.1.1, s.2.2.2)))) = _
      rw [decCoset_top3Shift hd, decPerm_normPerm hd, decCoset_top2NormC hd, hg,
        topwCosetPreimage_spec hd hnd hlt hinv _ (ha.symm ▸ hA), ha]
  | call w j s J k hc hn ih =>
    intro hT hR
    have hJ := hT (line4dInnerDecode q.1.1.length J) (by simp [SIReduction.calls])
    change (if j < avCalls (line4dHdr c tt dd q) then
      (avChild (line4dHdr c tt dd q, s)).map (fun J => (line4dHdr c tt dd q, some J))
      else none) = some J at hc
    split_ifs at hc with hj
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec hd hd hnd hlt hinv W hJ
    have hchild : line4dChild c tt dd ((q, none), j, s) = some (q, some V) := by
      change (if j < avCalls (line4dHdr c tt dd q) then
        (avChild (line4dHdr c tt dd q, s)).bind (fun W =>
          (topwRawInstance (line4dCtx q, W)).map fun V => (q, some V)) else none) = _
      rw [if_pos hj, hW, Option.bind_some, hctx, hV]
      rfl
    have hDV : line4dDecode n (q, some V) =
        topwInstance q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
          (line4dInnerDecode q.1.1.length (line4dHdr c tt dd q, some W)) := hdec
    change LoopMatch _ _ _ _ (w + 1) j s (.call
      (topwInstance q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
        (line4dInnerDecode q.1.1.length (line4dHdr c tt dd q, some W))) _)
    rw [← hDV]
    refine .call w j s (q, some V) _ hchild ?_
    intro z hz
    have hzsub : decCoset n z ⊆ (genGroup gens : Set (Perm (Fin n))) := by
      rw [hz, hDV, topwInstance_answer]
      rintro g ⟨hg, _⟩
      exact hg
    have hanswer : decCoset q.1.1.length (topwCosetImage (q.1.2.2.2.1, q.1.1, z)) =
        (line4dInnerDecode q.1.1.length (line4dHdr c tt dd q, some W)).answer := by
      rw [topwCosetImage_spec hd hnd hlt hinv z hzsub, hz, hDV,
        topwImage_answer hnd hlt hinv (decStrN n q.1.2.2.2.1) _ hJ]
    have htail := ih (topwCosetImage (q.1.2.2.2.1, q.1.1, z)) hanswer
      (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ'])) hR
    change LoopMatch _ _ _ _ w (j + 1)
      (avCombine (line4dHdr c tt dd q, s, topwCosetImage (q.1.2.2.2.1, q.1.1, z)))
      ((top4wTree q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
        (k (topwImageSet q.1.1 hnd hlt (genGroup gens) hinv
          (line4dDecode n (q, some V)).answer))).bind
        (fun A => .done (decPerm n q.1.2.2.1 • A)))
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n q.1.2.2.2.1) _ hJ]
    exact htail

end Loop

/-! ## The carrier -/

section Carrier

variable (c tt dd : ℕ)

/-- The hinted input of a node of the Master Algorithm.  At a node without hint the carrier
is never taken (`Algo.masterTopOps` runs line 1 there); it reads an empty hint. -/
def line4dHint (p : RawMasterSI) : MasterHintInput := (p.1, p.2.getD (([], []), 0))

theorem polyFun_line4dHint : PolyFun line4dHint :=
  (polyFun_fst.pair ((polyFun_snd.pair (polyFun_const ((([], []), 0) : RawMasterHint))).comp
    polyFun_optionGetD)).of_eq (fun _ => rfl)

/-- **Section 15, lines 4c–4d: the carrier of the Master's node.**  It runs the loop of
Eq. (71) on the versions line 4c found, with every call lifted to the node's domain. -/
def line4dOps : MasterOps AggnRecomputeState where
  width p := avCalls (line4dHdr c tt dd (line4dHint p))
  child z := (line4dChild c tt dd ((line4dHint z.1, none), z.2)).map
    (fun J => masterCheckedCall (z.1.1.2.2.2.1, line4dNodeRead J))
  init p := avInit (line4dHdr c tt dd (line4dHint p))
  combine z := line4dCombine c tt dd (line4dHint z.1, z.2)
  finish z := line4dFinish (line4dHint z.1, z.2)

/-! ### Running time -/

theorem quasiFun_line4dHdrAt : QuasiFun (fun p : RawMasterSI => line4dHdr c tt dd (line4dHint p)) :=
  polyFun_line4dHint.comp_quasiFun (quasiFun_line4dHdr c tt dd)

theorem polyFun_line4dCtx : PolyFun line4dCtx := by
  have i : PolyFun (fun q : MasterHintInput => q) := polyFun_id
  have hx := pfst (psnd (psnd (psnd (pfst i))))
  exact ((hx.pair (pfst (psnd (pfst i)))).pair ((pfst (pfst i)).pair hx)).of_eq (fun _ => rfl)

/-- The child of the carrier, once the header is computed. -/
def line4dChildBody (w : AVHdr × (RawMasterSI × ℕ × AVState)) : Option RawMasterSI :=
  if w.2.2.1 < avCalls w.1 then
    ((avChild (w.1, w.2.2.2)).bind fun W => topwRawInstance (line4dCtx (line4dHint w.2.1), W)).map
      fun V => masterCheckedCall (w.2.1.1.2.2.2.1, V)
  else none

theorem polyFun_line4dChildBody : PolyFun line4dChildBody := by
  let Z := AVHdr × (RawMasterSI × ℕ × AVState)
  have z : PolyFun (fun w : Z => w) := polyFun_id
  have hh := pfst z
  have hj := pfst (psnd (psnd z))
  have hs := psnd (psnd (psnd z))
  have hp := pfst (psnd z)
  have hlt : PolyFun (fun w : Z => decide (w.2.2.1 < avCalls w.1)) :=
    (hj.add (polyFun_const 1)).le (hh.comp polyFun_avCalls)
  have hctx : PolyFun (fun w : Z => line4dCtx (line4dHint w.2.1)) :=
    (hp.comp polyFun_line4dHint).comp polyFun_line4dCtx
  have hx : PolyFun (fun w : Z => w.2.1.1.2.2.2.1) := pfst (psnd (psnd (psnd (pfst hp))))
  -- the lifted call, from the call on the window
  have hlift : PolyFun (fun u : RawWinSI × Z => topwRawInstance (line4dCtx (line4dHint u.2.2.1), u.1)) :=
    (((psnd polyFun_id).comp hctx).pair polyFun_fst).comp polyFun_topwRawInstance
  have hbind : PolyFun (fun w : Z =>
      (avChild (w.1, w.2.2.2)).bind fun W => topwRawInstance (line4dCtx (line4dHint w.2.1), W)) :=
    ((((hh.pair hs).comp polyFun_avChild).pair z).comp
      (PolyFun.optionElim (polyFun_const none) hlift)).of_eq (fun w => by
        cases avChild (w.1, w.2.2.2) <;> rfl)
  have hmk : PolyFun (fun u : RawWinSI × Z => some (masterCheckedCall (u.2.2.1.1.2.2.2.1, u.1))) :=
    (((psnd polyFun_id).comp hx).pair polyFun_fst).comp polyFun_masterCheckedCall |>.comp polyFun_some
  have hmap : PolyFun (fun w : Z => ((avChild (w.1, w.2.2.2)).bind fun W =>
      topwRawInstance (line4dCtx (line4dHint w.2.1), W)).map
        fun V => masterCheckedCall (w.2.1.1.2.2.2.1, V)) :=
    ((hbind.pair z).comp (PolyFun.optionElim (polyFun_const none) hmk)).of_eq (fun w => by
      cases ((avChild (w.1, w.2.2.2)).bind fun W =>
        topwRawInstance (line4dCtx (line4dHint w.2.1), W)) <;> rfl)
  exact (PolyFun.ite hlt hmap (polyFun_const none)).of_eq (fun w => by
    unfold line4dChildBody
    by_cases h : w.2.2.1 < avCalls w.1 <;> simp [h])

theorem line4dOps_child_eq (z : RawMasterSI × ℕ × AVState) :
    (line4dOps c tt dd).child z = line4dChildBody (line4dHdr c tt dd (line4dHint z.1), z) := by
  change (line4dChild c tt dd ((line4dHint z.1, none), z.2)).map _ = _
  unfold line4dChildBody
  change (if z.2.1 < avCalls (line4dHdr c tt dd (line4dHint z.1)) then _ else none).map _ = _
  split_ifs
  · cases (avChild (line4dHdr c tt dd (line4dHint z.1), z.2.2)) with
    | none => rfl
    | some W =>
      simp only [Option.bind_some]
      cases topwRawInstance (line4dCtx (line4dHint z.1), W) <;> rfl
  · rfl

theorem quasiFun_line4dOps_child : QuasiFun (line4dOps c tt dd).child :=
  (((polyFun_fst.quasiFun.comp (quasiFun_line4dHdrAt c tt dd)).pair quasiFun_id).comp_poly
    polyFun_line4dChildBody).of_eq (fun z => (line4dOps_child_eq c tt dd z).symm)

theorem polyFun_line4dFinish : PolyFun line4dFinish := by
  have i : PolyFun (fun z : MasterHintInput × AVState => z) := polyFun_id
  have hq := pfst (pfst i)
  have hx := pfst (psnd (psnd (psnd hq)))
  have hτ := pfst (psnd (psnd hq))
  have hgs := pfst (psnd hq)
  have hΔ := pfst hq
  have ha := psnd (psnd (psnd (psnd i)))
  have hpre := (((hx.pair hgs).pair (hΔ.pair ha)).comp polyFun_topwCosetPreimage)
  have hnorm := (hx.pair hpre).comp polyFun_top2NormC
  exact ((hx.pair (((hx.pair hτ).comp polyFun_normPerm).pair hnorm)).comp polyFun_top3Shift).of_eq
    (fun _ => rfl)

theorem quasiFun_line4dOps_combine : QuasiFun (line4dOps c tt dd).combine := by
  have i : PolyFun (fun z : RawMasterSI × ℕ × AVState × RawCoset => z) := polyFun_id
  have hq := pfst i
  have himg : PolyFun (fun z : RawMasterSI × ℕ × AVState × RawCoset =>
      topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
    ((pfst (psnd (psnd (psnd (pfst hq))))).pair ((pfst (pfst hq)).pair
      (psnd (psnd (psnd i))))).comp polyFun_topwCosetImage
  exact (((pfst i).quasiFun.comp (quasiFun_line4dHdrAt c tt dd)).pair
    ((pfst (psnd (psnd i))).pair himg).quasiFun).comp_poly polyFun_avCombine |>.of_eq
      (fun _ => rfl)

/-- The first string of the header is no longer than the header's encoding. -/
theorem length_hdrX_le_size (h : AVHdr) : h.2.2.2.2.1.length ≤ Enc.size h :=
  (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans
    ((size_snd_le' _).trans ((size_snd_le' _).trans (size_snd_le' _)))))

/-- **Section 15, lines 4c–4d: the carrier's local cost data.**  The state and the width
are bounded by quasipolynomials of the node's degree, fixed before the degree is given; the
answer fits the Master's input cap. -/
theorem line4dOps_cost (a b : ℕ) : Nonempty (MasterOpsCost a b (line4dOps c tt dd)) := by
  have hH := quasiFun_line4dHdrAt c tt dd
  obtain ⟨G, hGq, hGm, hGs⟩ := hH.size.exists_quasiPolyBound
  let B : ℕ → ℕ := fun n => G (masterInputCap a b n)
  have hBq : QuasiPolyBound B := hGq.comp_poly (polyBound_masterInputCap a b)
  have hBm : Monotone B := fun _ _ h => hGm _ _ (mono_masterInputCap a b h)
  -- the header's size at a well-formed node
  have hhdr : ∀ p, MasterInputWF a b p →
      Enc.size (line4dHdr c tt dd (line4dHint p)) ≤ B (masterDegree p) :=
    fun p hp => (hGs p).trans (hGm _ _ hp.1)
  have hstate : ∀ (h : AVHdr) (N : ℕ), Enc.size h ≤ N →
      16 * (Enc.size h + chainBound (Enc.size h) + 2) ≤ 16 * (N + chainBound N + 2) := by
    intro h N hN
    have := mono_chainBound hN
    omega
  refine ⟨{
    stateBound := fun n => 16 * (B n + chainBound (B n) + 2)
    widthBound := fun n => B n * B n
    quasiPoly_state := (polyBound_const 16).quasiPoly.mul
      ((hBq.add ((polyBound_chainBound.quasiPoly).comp hBq)).add (polyBound_const 2).quasiPoly)
    mono_state := fun m m' hmm => by
      have h1 := hBm hmm
      have h2 := mono_chainBound h1
      dsimp only
      omega
    quasiPoly_width := hBq.mul hBq
    quasiFun_width := hH.comp_poly polyFun_avCalls
    quasiFun_child := quasiFun_line4dOps_child c tt dd
    quasiFun_init := hH.comp_poly polyFun_avInit
    quasiFun_combine := quasiFun_line4dOps_combine c tt dd
    quasiFun_finish := (((polyFun_fst.comp polyFun_line4dHint).pair polyFun_snd).comp
      polyFun_line4dFinish).quasiFun
    init_le := ?_
    combine_le := ?_
    finish_le := ?_
    width_le := ?_ }⟩
  · intro p hp
    set h := line4dHdr c tt dd (line4dHint p)
    exact (avInit_size h (length_hdrX_le_size h)).trans (hstate h _ (hhdr p hp))
  · intro p j s A hp _
    set h := line4dHdr c tt dd (line4dHint p)
    exact (avCombine_size (h, s, _) (length_hdrX_le_size h)).trans (hstate h _ (hhdr p hp))
  · intro p s _
    have hs := size_top3Shift_le (n := p.1.2.2.2.1.length) rfl le_rfl
      (normPerm (p.1.2.2.2.1, p.1.2.2.1))
      (top2NormC p.1.2.2.2.1 (topwCosetPreimage ((p.1.2.2.2.1, p.1.2.1), p.1.1, s.2.2.2)))
    change Enc.size (top3Shift _) ≤ _
    refine hs.trans ?_
    unfold masterInputCap
    change chainBound (masterDegree p) ≤ _
    omega
  · intro p hp
    set h := line4dHdr c tt dd (line4dHint p)
    have h1 : h.2.2.1.length ≤ Enc.size h :=
      (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans (size_snd_le' _)))
    have h2 : h.2.2.2.1.length ≤ Enc.size h :=
      (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans
        ((size_snd_le' _).trans (size_snd_le' _))))
    have h3 := hhdr p hp
    exact Nat.mul_le_mul (h1.trans h3) (h2.trans h3)

end Carrier

/-! ## The Master's round, without a dominant color class -/

section Shape

variable {W : Type*} [Fintype W] [DecidableEq W] {A : Type*} {G : Subgroup (Perm W)}
  {x y : W → A}

/-- §14.1, line 6: **with no dominant color class, the round is the plain union of Eq. (71)
over the Chain Rule of line 5** (`Babai.AlignShape` notes this: the expansion of line 6 is the
identity). -/
theorem alignShape_red_eq_of_dom_none (S : AlignShape W A G x y) (h : S.dom = none) :
    S.red = (letI := S.act; cosetDesignAlign S.ϕ x y S.X' S.versions (S.head :: S.tail)) := by
  letI := S.act
  have hf : (fun J : SIInstance W A => if J.Δ = S.head then S.dominantRound J
      else .call J .done) = fun J => .call J .done := by
    funext J
    simp only [AlignShape.dominantRound, h, ite_self]
  unfold AlignShape.red cosetAlignExpand
  rw [hf, SIReduction.expand_call_done]

/-- §14.1, line 11: with no dominant color class, no call carries a hint. -/
theorem alignShape_hint_eq_none_of_dom_none (S : AlignShape W A G x y) (h : S.dom = none)
    (J : SIInstance W A) : S.hint J = none := by
  simp only [AlignShape.hint, h]

/-- With no dominant color class, **every call of the round has the letters of the two
strings**: it is a call of the Chain Rule of line 5 on `x` and `y`. -/
theorem alignShape_letters_of_dom_none {k : ℕ} {x y : W → ℕ} {G : Subgroup (Perm W)}
    (S : AlignShape W ℕ G x y) (h : S.dom = none) (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ S.red.calls, MasterCallLetters k J := by
  rw [alignShape_red_eq_of_dom_none S h]
  exact SIReduction.mem_calls_unionOver _
    (fun _ J hJ => masterLetters_cosetChain k x y hx hy _ _ J hJ) _

end Shape

/-- §14.1 and Eq. (72): **with no dominant color class, every call of the round has a window of
at most `4n/5` points** (the hint alternative of `Babai.Line4cdData.calls_progress` is empty). -/
theorem line4cdData_five_mul_windowSize_of_dom_none {N : ℕ} {A : Type*}
    {G : Subgroup (Perm (Fin N))} {x y : Fin N → A} {par cost : ℕ}
    (D : Line4cdData (Fin N) A G x y par cost) (h : D.shape.dom = none) :
    ∀ J ∈ D.shape.red.calls, 5 * J.windowSize ≤ 4 * N := by
  intro J hJ
  rcases D.calls_progress J hJ with hs | hs
  · rwa [Fintype.card_fin] at hs
  · rw [alignShape_hint_eq_none_of_dom_none D.shape h] at hs
    exact absurd hs (by simp)

/-! ## The witness of Theorem 9.2.3 the machine meets -/

section Witness

/-- The machine's count of line 4c in the window size (`Algo.line4cVersions_length_le_window`). -/
noncomputable def line4cCountBound (c tt dd : ℕ) : ℕ → ℕ :=
  (line4cVersions_length_le_window c tt dd).choose

theorem line4cCountBound_spec (c tt dd : ℕ) :
    QuasiPolyBound (line4cCountBound c tt dd) ∧ Monotone (line4cCountBound c tt dd) ∧
    ∀ z : RawLine4cIn,
      z.1.1.2.1.length ≤ z.1.1.1.1.length → z.1.2.1.length ≤ z.1.1.1.1.length →
      z.1.2.2.length ≤ z.1.1.1.1.length →
      (line4cVersions c tt dd z).1.length ≤ line4cCountBound c tt dd z.1.1.1.1.length ∧
        (line4cVersions c tt dd z).2.length ≤ line4cCountBound c tt dd z.1.1.1.1.length :=
  (line4cVersions_length_le_window c tt dd).choose_spec

/-- **The witness of Theorem 9.2.3 at lines 4c–4d on the machine**: the multiplicative cost
`q923` of `Babai.theorem_9_2_3` raised by the machine's own count.  It is admissible
(`Algo.line4dQ_admissible`), so `Babai.Theorem_1_1_1_math_of_admissible` holds for the Master
Algorithm run with `Babai.Sec15Choices` at `(line4dQ, c923)`. -/
noncomputable def line4dQ (c tt dd : ℕ) (n : ℕ) : ℕ := Babai.q923 n + line4cCountBound c tt dd n

theorem line4dQ_admissible (c tt dd : ℕ) :
    QuasiPolyBound (line4dQ c tt dd) ∧ Babai.Theorem923Uniform (line4dQ c tt dd) Babai.c923 :=
  ⟨(Babai.quasiPolyBound_q923.add (line4cCountBound_spec c tt dd).1).mono
      (fun _ => le_of_eq rfl),
    Babai.theorem923Uniform_q923.mono (fun n => Nat.le_add_right _ _)⟩

end Witness

/-! ## The carrier walks the Master's round -/

section Match

variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 4)
    (hb : Line4cBounds c tt dd)

include hx hy hgs hp hG hϕ hn hr hb in
/-- **Section 15, lines 4c–4d, on the Master's node.**  At a node of route `4` (lines 1, 2,
4a and 4b failed) where line 6 of Procedure Align finds no dominant color class, there is a
round of Procedure Align of the Master (`Babai.Line4cdData`, with the versions line 4c found,
each once, and the windows of lines 5–6), with the cost `Babai.Line4cdDataAt` asks at the
admissible witness `(Algo.line4dQ, c923)` of Theorem 9.2.3, such that the carrier `Algo.line4dOps` walks, call
for call, its round `Babai.AlignShape.red` on the window, read on the node's domain and
shifted by the node's representative (Eq. (59)), exactly as line 4b reads its round
(`Algo.master4Tree`). -/
theorem line4dOps_match (a b : ℕ) (hnd' : line4dHasDom c tt dd p = false) :
    ∃ D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
        (decStrN p.1.1.length (masterHintTop p).2.1)
        (decStrN p.1.1.length (masterHintTop p).2.2) m
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length))),
      D.shape.dom = none ∧ AVDescribes p.1.1.length (line4dHdr c tt dd p) D.shape (D.shape.head :: D.shape.tail) ∧
      LoopMatch (masterAdmittedRound a b (line4dOps c tt dd)) (fun J => decWinSI n J.1)
        (decCoset n) (p.1, some p.2) ((line4dOps c tt dd).width (p.1, some p.2)) 0
        ((line4dOps c tt dd).init (p.1, some p.2))
        ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
          D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  have hxl : (masterHintTop p).2.1.length = p.1.1.length := by
    show (rawRestrictStr (p.1.2.2.2.1, p.1.1)).length = _
    exact length_rawRestrictStr _ _
  have hyl : (masterHintTop p).2.2.length = p.1.1.length := by
    show (rawRestrictStr (top4aTarget (p.1.2.2.2.1, p.1.2.2.1, p.1.2.2.2.2), p.1.1)).length = _
    exact length_rawRestrictStr _ _
  obtain ⟨D₀, hdom, hD⟩ := exists_line4dData p hp hG hϕ hn hr hb hxl hyl hK hnd'
  -- the machine's count is below the cost of `Babai.Line4cdDataAt` at `(line4dQ, c923)`
  obtain ⟨-, -, -, -, hmn, -⟩ := masterLine4c_facts p hp hG hϕ hn hr
  have hcnt := ((line4cCountBound_spec c tt dd).2.2 (masterLine4cInput p)
    (by show (masterHintTop p).1.2.1.length ≤ p.1.1.length; rw [hp.2.1]; exact hmn)
    (by show (masterHintTop p).2.1.length ≤ p.1.1.length; rw [hxl])
    (by show (masterHintTop p).2.2.length ≤ p.1.1.length; rw [hyl])).2
  have hle : (line4cVersions c tt dd (masterLine4cInput p)).2.length *
      (Fintype.card (Fin p.1.1.length) + 1) *
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin p.1.1.length)) ≤
      line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length)) := by
    rw [line4cdCost, Fintype.card_fin]
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
    have hq : line4cCountBound c tt dd p.1.1.length ≤ qMax (line4dQ c tt dd) p.1.1.length :=
      (Nat.le_add_left _ (Babai.q923 p.1.1.length)).trans
        (le_qMax (line4dQ c tt dd) (le_refl p.1.1.length))
    exact (hcnt.trans hq).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  let D := D₀.mono hle
  refine ⟨D, hdom, hD, ?_⟩
  have hinner := line4dInner_loopMatch (n := p.1.1.length) (h := line4dHdr c tt dd p)
    D.shape hdom hD hxl
  have hgrp := masterLine4b_group hgs hnd hlt hinv
  have hK' : ∀ J ∈ D.shape.red.calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  have hR : D.shape.red.run ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [D.run_red, ← hgrp]
    exact fun _ h => h.1
  have hlift := line4dRound_lift c tt dd (gens := p.1.2.1.map (decPerm n))
    (map_encPerm_decPerm hgs).symm hx.1 hnd hlt hinv hinner hK' hR
  have hwsize : masterWindowSize (p.1, some p.2) ≤ masterDegree (p.1, some p.2) := by
    change p.1.1.length ≤ p.1.2.2.2.1.length
    rw [hx.1]
    exact length_le_of_nodup_lt hnd hlt
  refine masterAdmittedRound_checked_match a b (R := line4dRound c tt dd)
    (F := line4dOps c tt dd) (I := (p, none)) (p := (p.1, some p.2)) hx.1 hwsize
    line4dNodeRead id (line4dDecode n) (fun _ _ _ _ => rfl) rfl (fun _ _ => rfl) rfl
    (fun _ _ _ => rfl) (fun _ => rfl) hlift ?_
  -- the calls: letters of the node's strings, and windows of at most `4|Δ|/5` points
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hyy := (masterStrWF_iff hy.1).mp hy
  have hix : ∀ u, decStrN p.1.1.length (masterHintTop p).2.1 u < 2 * n + 1 := by
    rw [show (masterHintTop p).2.1 = rawRestrictStr (p.1.2.2.2.1, p.1.1) from rfl,
      topwRestrictStr_decode hnd hlt]
    exact fun u => hxx _
  have hiy : ∀ u, decStrN p.1.1.length (masterHintTop p).2.2 u < 2 * n + 1 := by
    rw [show (masterHintTop p).2.2 = rawRestrictStr
      (top4aTarget (p.1.2.2.2.1, p.1.2.2.1, p.1.2.2.2.2), p.1.1) from rfl,
      top4aTarget_restrict hx.1 hnd hlt]
    exact fun u => hyy _
  have hlet := alignShape_letters_of_dom_none D.shape hdom hix hiy
  have hwin := line4cdData_five_mul_windowSize_of_dom_none D hdom
  have hcos := top4wTree_calls_isCosetInstance hnd hlt hinv (decStrN n p.1.2.2.2.1) D.shape.red
    (by rw [← hgrp]; exact D.calls_coset)
  intro J hJ
  simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
  have hJc := hcos J hJ
  simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
  rw [calls_topwReduction hnd hlt hinv _ _ hK'] at hJ
  obtain ⟨K, hKm, rfl⟩ := List.mem_map.mp hJ
  refine ⟨masterLetters_topwInstance p.1.1 hnd hlt _ hinv _ hxx K (hlet K hKm), ?_, _, hJc⟩
  rw [topwInstance_windowSize]
  have := hwin K hKm
  change K.windowSize < p.1.1.length
  omega

end Match

end Algo

#print axioms Algo.line4dOps_cost
#print axioms Algo.line4dOps_match
#print axioms Algo.line4dQ_admissible
