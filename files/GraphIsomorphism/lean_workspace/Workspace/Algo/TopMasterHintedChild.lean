import Workspace.Algo.TopMasterRecursionL57

/-! # Hinted children of the node carrier: Procedure Align, line 11

Section 14.1, Procedure Align, line 11 (as repaired in the corrected paper): in case 3 of the
dominant color class, the first call of the Chain Rule over the orbits of `G*` is made on a
dominant orbit `Δ₁` of `G*` *with* the giant representation `ϕ*` of `G*` onto `S(Γ*)`; that
call is the Johnson case with parameter `m* ≤ m/2` of Eq. (73). Its window need not be smaller
than the node's, so the progress it makes is that of recurrence (ii): the window does not
grow and the Johnson parameter is halved.

On the machine a call carries its hint in its second component (`Algo.RawMasterSI`). The
carriers of lines 4d and 5–7 propose calls without a hint (`Algo.masterCheckedCall`). This file
adds the generic path that attaches a hint to a proposed call:

* `Algo.MasterOps.withHint F H`: the carrier `F`, with every proposed child `C` at the step
  `(P, j, s)` given the hint `H ((P, j, s), C)` when `H` returns one
  (`Algo.masterAttachHint`); it keeps every other routine of `F`, and has local costs once `F`
  has and `H` is quasipolynomial (`Algo.MasterOpsCost.withHint`);
* `Algo.masterHintedCall_admitted`: a checked window with a hint that has its meaning
  (`Algo.MasterHintGood`), a parameter at most half the node's, and small labels, passes the
  admission test at the node, window kept or not;
* `Algo.masterHintedCall_good`: such a child is a good node and makes the progress of
  recurrence (ii) (`Babai.MakesProgress`, second alternative);
* the matches with a condition on the children (`Algo.LoopMatchG`) carried through the
  layers of the node carrier (`Algo.LoopMatchG.embed`, `Algo.masterPairIte_matchG_pos`,
  `Algo.masterPairIte_matchG_neg`, `Algo.masterShiftOps_matchG`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ### Attaching a hint -/

/-- A proposed call with the hint `o` attached, when there is one. -/
def masterAttachHint (z : RawMasterSI × Option RawMasterHint) : RawMasterSI :=
  z.2.elim z.1 (fun h => (z.1.1, some h))

@[simp] theorem masterAttachHint_none (C : RawMasterSI) : masterAttachHint (C, none) = C := rfl

@[simp] theorem masterAttachHint_some (C : RawMasterSI) (h : RawMasterHint) :
    masterAttachHint (C, some h) = (C.1, some h) := rfl

/-- Attaching a hint does not change the window instance. -/
@[simp] theorem masterAttachHint_fst (z : RawMasterSI × Option RawMasterHint) :
    (masterAttachHint z).1 = z.1.1 := by
  obtain ⟨C, o⟩ := z
  cases o <;> rfl

theorem polyFun_masterAttachHint : PolyFun masterAttachHint := by
  have hh : PolyFun (fun q : RawMasterHint × RawMasterSI => ((q.2.1, some q.1) : RawMasterSI)) :=
    (polyFun_snd.comp polyFun_fst).pair (polyFun_fst.comp polyFun_some)
  refine ((polyFun_snd.pair polyFun_fst).comp (PolyFun.optionElim polyFun_id hh)).of_eq
    (fun z => ?_)
  obtain ⟨C, o⟩ := z
  cases o <;> rfl

/-- **The carrier `F` with the hints of `H`**: at the step `(P, j, s)`, a child `C` that `F`
proposes is proposed with the hint `H ((P, j, s), C)` when `H` returns one, and as it is
otherwise. The other routines are those of `F`. -/
def MasterOps.withHint {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) : MasterOps S :=
  { F with child := fun z => (F.child z).map (fun C => masterAttachHint (C, H (z, C))) }

@[simp] theorem MasterOps.withHint_width {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) :
    (F.withHint H).width = F.width := rfl

@[simp] theorem MasterOps.withHint_init {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) :
    (F.withHint H).init = F.init := rfl

@[simp] theorem MasterOps.withHint_combine {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) :
    (F.withHint H).combine = F.combine := rfl

@[simp] theorem MasterOps.withHint_finish {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) :
    (F.withHint H).finish = F.finish := rfl

theorem MasterOps.withHint_child {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint)
    (z : RawMasterSI × ℕ × S) :
    (F.withHint H).child z = (F.child z).map (fun C => masterAttachHint (C, H (z, C))) := rfl

/-- Without hints the carrier is unchanged. -/
theorem MasterOps.withHint_none {S : Type} (F : MasterOps S) :
    F.withHint (fun _ => none) = F := by
  cases F
  simp only [MasterOps.withHint, masterAttachHint_none, Option.map_id']

theorem quasiFun_withHint_child {S : Type} [Enc S] {F : MasterOps S}
    {H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint}
    (hc : QuasiFun F.child) (hH : QuasiFun H) : QuasiFun (F.withHint H).child := by
  let Z := RawMasterSI × ℕ × S
  have hbr : QuasiFun (fun q : RawMasterSI × Z =>
      (some (masterAttachHint (q.1, H (q.2, q.1))) : Option RawMasterSI)) :=
    ((polyFun_fst.quasiFun.pair ((polyFun_snd.pair polyFun_fst).quasiFun.comp hH)).comp_poly
      polyFun_masterAttachHint).comp_poly polyFun_some
  refine ((hc.pair polyFun_id.quasiFun).comp
    (QuasiFun.optionElim (g := fun _ : Z => (none : Option RawMasterSI)) (quasiFun_const none)
      hbr)).of_eq (fun z => ?_)
  change (F.child z).elim none _ = (F.child z).map _
  cases F.child z <;> rfl

/-- **The local costs of the carrier with hints**: those of `F`, with a quasipolynomial hint
routine. -/
def MasterOpsCost.withHint {S : Type} [Enc S] {a b : ℕ} {F : MasterOps S}
    {H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint}
    (C : MasterOpsCost a b F) (hH : QuasiFun H) : MasterOpsCost a b (F.withHint H) where
  stateBound := C.stateBound
  widthBound := C.widthBound
  quasiPoly_state := C.quasiPoly_state
  mono_state := C.mono_state
  quasiPoly_width := C.quasiPoly_width
  quasiFun_width := C.quasiFun_width
  quasiFun_child := quasiFun_withHint_child C.quasiFun_child hH
  quasiFun_init := C.quasiFun_init
  quasiFun_combine := C.quasiFun_combine
  quasiFun_finish := C.quasiFun_finish
  init_le := C.init_le
  combine_le := C.combine_le
  finish_le := C.finish_le
  width_le := C.width_le

/-- The shift of the answer and the hints commute. -/
theorem masterShiftOps_withHint {S : Type} (F : MasterOps S)
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint) :
    (masterShiftOps F).withHint H = masterShiftOps (F.withHint H) := rfl

/-! ### Admission and progress of a hinted call -/

section Hinted
variable {n : ℕ} {W' : RawWinSI} {h : RawMasterHint}
    (hW' : AggnCheckedWindowWF n W') (hg : MasterHintGood (W', h))
    (hrows : ∀ i ∈ h.1.1, i < n)

include hW' hg hrows in
/-- **A hinted call is small**: a checked window with a hint that has its meaning and labels
below `n` has at most the size of a Cameron child (`Algo.masterCameronChildBound`). -/
theorem masterHintedCall_size :
    Enc.size ((W', some h) : RawMasterSI) ≤ masterCameronChildBound n := by
  obtain ⟨m, ϕ, B, hB, hp, -, -, -, -, -, ht, hm, -⟩ := hg
  have hn := length_le_of_nodup_lt hW'.1 hW'.2.1
  have hmn : m ≤ n := hm.trans hn
  have hrl : h.1.1.length = m := hp.2.1
  have hlen : h.1.2.length ≤ n * n := by
    have h1 := hp.2.2.2.2.1
    simp only [List.length_map] at h1
    have h2 : (masterHintTop (W', h)).1.1.2.length = W'.2.1.length := by
      change (rawRestrictGens ((W'.2.2.2.1, W'.2.1), W'.1)).length = _
      simp [rawRestrictGens]
    change (masterHintTop (W', h)).1.1.2.length = h.1.2.length at h1
    rw [← h1, h2]
    exact hW'.2.2.2.1
  have himg : Enc.size h.1.2 ≤ gensBound n := by
    have hs := size_list_le_of_entries h.1.2 (strBound n)
      (fun g hg => size_perm_le' hmn (hp.2.2.2.1 g hg))
    have hl := Nat.mul_le_mul_right (2 * strBound n + 1) hlen
    dsimp [gensBound]
    omega
  have hdom : Enc.size h.1.1 ≤ strBound n :=
    size_natList_le (by omega) hrows
  have htt : h.2 ≤ n := by
    have : 2 * h.2 < m := ht
    omega
  have hts : Enc.size h.2 ≤ n + 2 := (size_nat_le_self h.2).trans (by omega)
  have hwin := aggnCheckedWindow_size hW'
  have h1 := size_pair_le' ((W', some h) : RawMasterSI)
  have h2 := size_pair_le' h
  have h3 := size_pair_le' h.1
  dsimp only at h1
  rw [size_some_eq] at h1
  unfold masterCameronChildBound
  omega

variable {p : RawMasterSI} (hinvW : rawIsInvariant (W'.2.1, W'.1) = true)
    (hpn : masterDegree p = n) (hwin : W'.1.length ≤ masterWindowSize p)
    (hpar : 2 * h.1.1.length ≤ masterParameter p) (hpar1 : 1 ≤ masterParameter p)

include hW' hg hrows hinvW hpn hwin hpar hpar1 in
/-- **Admission of a hinted call** (Procedure Align, line 11): at a node `p` of degree `n`, a
checked window `W'` no larger than `p`'s window, with a hint that has its meaning, labels below
`n`, and a Johnson parameter at most half of `p`'s (Eq. (73)), passes the admission test —
its measure drops because the parameter does, even when the window is kept. -/
theorem masterHintedCall_admitted {a b : ℕ}
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    masterAdmitChild a b (p, some ((W', some h) : RawMasterSI)) = some (W', some h) := by
  have hdeg : masterDegree ((W', some h) : RawMasterSI) = n := hW'.2.2.2.2.2.1.1
  have hn := length_le_of_nodup_lt hW'.1 hW'.2.1
  have hpw := masterParameter_le_of_hintGood hg
  change h.1.1.length ≤ W'.1.length at hpw
  refine masterAdmitChild_some.mpr ⟨rfl, ⟨?_, ?_, ?_⟩, hdeg.trans hpn.symm, ?_, hinvW⟩
  · rw [hdeg]
    exact (masterHintedCall_size hW' hg hrows).trans hcap
  · change W'.1.length ≤ masterDegree ((W', some h) : RawMasterSI)
    rw [hdeg]
    exact hn
  · change h.1.1.length ≤ 2 * W'.1.length
    omega
  · apply masterRawMeasure_lt (hdeg.trans hpn.symm) hwin
    · change h.1.1.length ≤ 2 * masterDegree p
      rw [hpn]
      omega
    · right
      change h.1.1.length < masterParameter p
      omega

include hW' hg hinvW hpn hwin hpar hpar1 in
/-- **A hinted call is a good child that makes progress** (recurrence (ii)): it is a good node
(its hint has its meaning), its window is at most the node's, and its Johnson parameter is at
most half the node's. -/
theorem masterHintedCall_good (hnot : ¬ MasterChainRuleNode p) :
    MasterNodeGood n ((W', some h) : RawMasterSI) ∧
      MasterStepProgress p ((W', some h) : RawMasterSI) := by
  have hdeg : masterDegree ((W', some h) : RawMasterSI) = n := hW'.2.2.2.2.2.1.1
  refine ⟨⟨⟨hdeg, hW', (rawIsInvariant_eq_true_iff hW'.2.2.1 hW'.2.1).mp hinvW⟩,
    fun h' hh' => by cases hh'; exact hg⟩, fun hc => absurd hc hnot, fun _ => Or.inr ⟨hwin, hpar1, hpar⟩⟩
end Hinted

/-! ### Matches with a condition on the children, through the layers of the carrier -/

section Embed
variable {ι ω ω' α Ω A : Type} {R : Round ι ω α} {R' : Round ι ω' α} {C : ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)} {I : ι}

/-- **A match carries over to a round that runs the same fold at `I` on an embedded state.** -/
theorem LoopMatchG.embed (e : ω → ω')
    (hc : ∀ j s, R'.child (I, j, e s) = R.child (I, j, s))
    (hu : ∀ j s a, R'.combine (I, j, e s, a) = e (R.combine (I, j, s, a)))
    (hf : ∀ s, R'.finish (I, e s) = R.finish (I, s)) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatchG R C decI decA I w j s T → LoopMatchG R' C decI decA I w j (e s) T := by
  intro w j s T h
  induction h with
  | done w j s a hch ha => exact .done w j (e s) a ((hc j s).trans hch) ((hf s).symm ▸ ha)
  | call w j s J k hch hC hn ih =>
    refine .call w j (e s) J k ((hc j s).trans hch) hC (fun a ha => ?_)
    rw [hu]
    exact ih a ha
end Embed

section PairMatchG
variable {S T : Type} {sel : RawMasterSI → Bool} {F : MasterOps S} {G : MasterOps T}
    {dS : S} {dT : T} {p : RawMasterSI} {Ω A : Type} {C : RawMasterSI → Prop}
    {decI : RawMasterSI → SIInstance Ω A} {decA : RawMasterSI → RawCoset → Set (Equiv.Perm Ω)}

/-- `Algo.masterPairIte_start_pos` for matches with a condition on the children. -/
theorem masterPairIte_matchG_pos (a b : ℕ) (h : sel p = true)
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatchG (masterAdmittedRound a b F) C decI decA p (F.width p) 0 (F.init p) T') :
    LoopMatchG (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) C decI decA p
      ((MasterOps.pairIte sel F G dS dT).width p) 0
      ((MasterOps.pairIte sel F G dS dT).init p) T' := by
  have hw : (MasterOps.pairIte sel F G dS dT).width p = F.width p := if_pos h
  have hi : (MasterOps.pairIte sel F G dS dT).init p = (F.init p, dT) := if_pos h
  rw [hw, hi]
  refine LoopMatchG.embed (R := masterAdmittedRound a b F) (fun s => (s, dT)) ?_ ?_ ?_ hm
  · intro j s
    simp only [masterAdmittedRound, masterGuardedChild, MasterOps.pairIte, h, if_true]
  · intro j s a
    exact if_pos h
  · intro s
    exact if_pos h

/-- `Algo.masterPairIte_start_neg` for matches with a condition on the children. -/
theorem masterPairIte_matchG_neg (a b : ℕ) (h : sel p = false)
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatchG (masterAdmittedRound a b G) C decI decA p (G.width p) 0 (G.init p) T') :
    LoopMatchG (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) C decI decA p
      ((MasterOps.pairIte sel F G dS dT).width p) 0
      ((MasterOps.pairIte sel F G dS dT).init p) T' := by
  have hw : (MasterOps.pairIte sel F G dS dT).width p = G.width p := by
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
  have hi : (MasterOps.pairIte sel F G dS dT).init p = (dS, G.init p) := by
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
  rw [hw, hi]
  refine LoopMatchG.embed (R := masterAdmittedRound a b G) (fun t => (dS, t)) ?_ ?_ ?_ hm
  · intro j t
    simp only [masterAdmittedRound, masterGuardedChild, MasterOps.pairIte, h,
      Bool.false_eq_true, if_false]
  · intro j t a
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
    rfl
  · intro t
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
    rfl
end PairMatchG

/-- `Algo.masterShiftOps_match` for matches with a condition on the children. -/
theorem masterShiftOps_matchG {S : Type} (a b : ℕ) (F : MasterOps S) {C : RawMasterSI → Prop}
    {n : ℕ} {p : RawMasterSI} (hx : p.1.2.2.2.1.length = n)
    {w j : ℕ} {s : S} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatchG (masterAdmittedRound a b F) C (fun J => decWinSI n J.1)
      (fun _ => decCoset n) p w j s T) :
    LoopMatchG (masterAdmittedRound a b (masterShiftOps F)) C (fun J => decWinSI n J.1)
      (fun _ => decCoset n) p w j s (T.bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  induction h with
  | done w j s A hc ha =>
    refine .done w j s _ hc ?_
    change decCoset n (top3Shift (p.1.2.2.2.1, p.1.2.2.1, F.finish (p, s))) = _
    rw [decCoset_top3Shift hx]
    exact congrArg (fun C => decPerm n p.1.2.2.1 • C) ha
  | call w j s J k hc hC hn ih =>
    exact .call w j s J _ hc hC (fun A hA => ih A hA)

end Algo
