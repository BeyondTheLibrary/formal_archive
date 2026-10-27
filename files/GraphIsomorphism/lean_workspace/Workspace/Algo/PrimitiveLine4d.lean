/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4d on the RAM: Procedure Align on the versions line 4c found.
-/
import Workspace.Algo.PrimitiveLine4cRoute
import Workspace.Algo.AlignOutcomeDedup
import Workspace.Algo.AlignOutcomeLab
import Workspace.Algo.AggNodeLine57Match
import Workspace.Algo.PrimitiveLine4dDomFacts

/-!
# Section 15, line 4d: Procedure Align on the versions of line 4c

> 4d. (: canonical structure `X` on `Γ` found: colored equipartition or Johnson scheme :)
>     apply Procedure Align to `X` (Sec. 14.1)

Line 4c (`Workspace/Algo/PrimitiveLine4c*.lean`) gives two lists of raw outcomes of
Theorem 9.2.3, one for `x` and one for `y`.  This file turns them into the header of the loop
of Eq. (71) (`Workspace/Algo/AlignVersions.lean`) and proves that the loop walks the
Master's round of Procedure Align, `Babai.AlignShape.red`, call for call.

**The header** (`Algo.line4dHdr`):
* the fixed version `X'` of `X(x)` is the first entry of the deduplicated list for `x`;
* the versions of `X(y)` are the deduplicated list for `y`, and the empty list when line 4b's
  test says the relative symmetry defect of `H(y)` is below `1/2` (then `X(y)` has no
  version: Theorem 9.2.3 is not applicable, see `Algo.line4cVers`);
* the windows are the color classes of `Ω` under the coloring of `X'`
  (`Algo.alignRWindows`), with line 6's dominant window first when there is one.

**Each version once.**  Def. 6.0.1 makes `F(Y)` a set, and the union of Eq. (71) runs over
its members, one term each.  The list of Theorem 9.2.3 on the RAM may repeat an outcome, so
the header deduplicates it (`Algo.rawVersDedup`).  This is the Master's side of the interface:
`Babai.Line4cdData.versions_spec` asks for each version exactly once.

**The Master's data** (`Algo.exists_line4dData`): the header describes a
`Babai.Line4cdData` whose versions are the decoded versions of the header and whose windows
are the decoded windows of the header.  The loop of Eq. (71) then walks its round
(`Algo.line4dInner_match`).

**The dominant case is not covered.**  When line 6 finds a dominant color class, the Master's
round expands the call on the dominant window by lines 7–11 of Procedure Align
(`Babai.AlignShape.dom`).  Those lines are not on the RAM in the Sec. 13 routines this file
reuses (`Workspace/Algo/AlignVersionsShape.lean`, "The dominant case (lines 7–11) is not on
the RAM yet").  So the match below assumes that line 6 finds no dominant color class
(`Algo.line4dHasDom = false`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## The header -/

section Header

variable (c tt dd : ℕ)

/-- Line 4d: the fixed version `X'` of `X(x)`, the first outcome line 4c found at `x`. -/
def line4dFixed (p : MasterHintInput) : RawAlignOutcome :=
  (rawVersDedup ((masterHintTop p).1.2.1,
    (line4cVersions c tt dd (masterLine4cInput p)).1)).headD (none, none)

/-- Line 4d, Eq. (71): the versions of `X(y)`, each once. -/
def line4dYs (p : MasterHintInput) : List RawAlignOutcome :=
  if primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.2) then []
  else rawVersDedup ((masterHintTop p).1.2.1, (line4cVersions c tt dd (masterLine4cInput p)).2)

/-- §14.1, line 4: the coloring of `Γ` by the fixed version. -/
def line4dLab (p : MasterHintInput) : RawLab :=
  alignOutcomeLab ((masterHintTop p).1.2.1, line4dFixed c tt dd p)

/-- §14.1, lines 6–7: is there a dominant color class, **with a nontrivial structure**?
Line 6 asks for a color class `Δ_j` with more than half of the points of `Γ`, and line 7 goes
on only when `X'` restricted to `Δ_j` is a nontrivial equipartition (A) or a Johnson scheme
(B), that is when `m* ≥ 2`.  With `m* = 1` the class is a single block, the Master's round has
no data of lines 7–11 (`Babai.AlignShape.dom = none`), and its windows are those of lines 5–6
(`Algo.exists_line4dData`). -/
def line4dHasDom (p : MasterHintInput) : Bool :=
  alignRHasDom ((masterHintTop p).1, line4dLab c tt dd p) &&
    decide (2 ≤ alignRMs ((masterHintTop p).1, line4dFixed c tt dd p))

/-- **Line 4d: the header of Eq. (71).**  The action, the fixed version of `X(x)`, the
versions of `X(y)`, the windows of lines 5 and 6, and the two strings on the window. -/
def line4dHdr (p : MasterHintInput) : AVHdr :=
  ((masterHintTop p).1, line4dFixed c tt dd p, line4dYs c tt dd p,
    alignRWindows ((masterHintTop p).1, line4dLab c tt dd p),
    (masterHintTop p).2.1, (masterHintTop p).2.2)

theorem quasiFun_line4dFixed : QuasiFun (line4dFixed c tt dd) := by
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    polyFun_masterHintTop.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hv := quasiFun_masterLine4cVersions c tt dd
  have hin : QuasiFun (fun p : MasterHintInput => ((masterHintTop p).1.2.1,
      (line4cVersions c tt dd (masterLine4cInput p)).1)) :=
    hg.quasiFun.pair (hv.comp_poly polyFun_fst)
  exact ((hin.comp_poly (polyFun_rawVersDedup.comp polyFun_headOption)).pair
    (quasiFun_const (none, none))).comp_poly polyFun_optionGetD |>.of_eq (fun _ => by
      rw [line4dFixed, List.headD_eq_head?_getD])

theorem quasiFun_line4dYs : QuasiFun (line4dYs c tt dd) := by
  have hT := polyFun_masterHintTop
  have hd : PolyFun (fun p : MasterHintInput =>
      primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.2)) :=
    (hT.comp (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))).comp
      polyFun_primitiveSmallDefect
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    hT.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hin : QuasiFun (fun p : MasterHintInput => ((masterHintTop p).1.2.1,
      (line4cVersions c tt dd (masterLine4cInput p)).2)) :=
    hg.quasiFun.pair ((quasiFun_masterLine4cVersions c tt dd).comp_poly polyFun_snd)
  exact (QuasiFun.ite hd (quasiFun_const []) (hin.comp_poly polyFun_rawVersDedup)).of_eq
    (fun _ => rfl)

theorem quasiFun_line4dLab : QuasiFun (line4dLab c tt dd) := by
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    polyFun_masterHintTop.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  exact ((hg.quasiFun.pair (quasiFun_line4dFixed c tt dd)).comp_poly
    polyFun_alignOutcomeLab).of_eq (fun _ => rfl)

theorem quasiFun_line4dHasDom : QuasiFun (line4dHasDom c tt dd) := by
  have hP : PolyFun (fun q : RawAction × RawAlignOutcome =>
      alignRHasDom (alignRColorOf q) && decide (2 ≤ alignRMs q)) :=
    polyFun_and (polyFun_alignRColorOf.comp polyFun_alignRHasDom)
      ((polyFun_const 2).le polyFun_alignRMs)
  exact ((polyFun_masterHintTop.comp polyFun_fst).quasiFun.pair
    (quasiFun_line4dFixed c tt dd)).comp_poly hP |>.of_eq (fun _ => rfl)

theorem quasiFun_line4dHdr : QuasiFun (line4dHdr c tt dd) := by
  have hT := polyFun_masterHintTop
  have hA : PolyFun (fun p : MasterHintInput => (masterHintTop p).1) := hT.comp polyFun_fst
  have hW : QuasiFun (fun p : MasterHintInput =>
      alignRWindows ((masterHintTop p).1, line4dLab c tt dd p)) :=
    (hA.quasiFun.pair (quasiFun_line4dLab c tt dd)).comp_poly polyFun_alignRWindows
  exact (hA.quasiFun.pair ((quasiFun_line4dFixed c tt dd).pair ((quasiFun_line4dYs c tt dd).pair
    (hW.pair ((hT.comp (polyFun_snd.comp polyFun_fst)).quasiFun.pair
      (hT.comp (polyFun_snd.comp polyFun_snd)).quasiFun))))).of_eq (fun _ => rfl)

theorem length_line4dYs_le (p : MasterHintInput) :
    (line4dYs c tt dd p).length ≤ (line4cVersions c tt dd (masterLine4cInput p)).2.length := by
  unfold line4dYs
  split_ifs
  · exact Nat.zero_le _
  · exact length_rawVersDedup_le _

end Header

/-! ## The windows of lines 5 and 6

The raw windows color `Ω` by the raw labels of `Γ`, and the Master colors `Ω` by
`Babai.alignIdx X'`.  The two colorings of `Γ` have the same classes
(`Algo.alignOutcomeLab_eq_iff`), and the coloring of `Ω` that Lemma 7.2.1 induces depends only
on the classes of the coloring of `Γ` (`Algo.omegaColor_eq_iff_of_fibers`).  So every raw
window is a color class of the Master (`Algo.winSet_alignRClasses_eq`). -/

section Windows

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Perm Ω)}

/-- Two points of `Ω` get the same color vector exactly when their labels meet every color
class of `Γ` in the same number of points. -/
theorem omegaColor_eq_iff_forall (ϕ : G →* Perm (Fin m)) {κ : Type*} (c : Fin m → κ)
    (u v : Ω) : omegaColor ϕ c u = omegaColor ϕ c v ↔ ∀ γ : Fin m,
      (Tpoint ϕ u ∩ {δ | c δ = c γ}).ncard = (Tpoint ϕ v ∩ {δ | c δ = c γ}).ncard := by
  simp only [omegaColor, tColor]
  constructor
  · intro h γ
    exact congrFun h (c γ)
  · intro h
    funext k
    by_cases hk : ∃ γ, c γ = k
    · obtain ⟨γ, rfl⟩ := hk
      exact h γ
    · push_neg at hk
      have he : ∀ w : Ω, Tpoint ϕ w ∩ {δ | c δ = k} = ∅ := fun w =>
        Set.eq_empty_iff_forall_notMem.2 fun δ hδ => hk δ hδ.2
      show (Tpoint ϕ u ∩ {δ | c δ = k}).ncard = (Tpoint ϕ v ∩ {δ | c δ = k}).ncard
      rw [he u, he v]

/-- §14.1, line 4: **the coloring of `Ω` depends only on the classes of the coloring of
`Γ`.** -/
theorem omegaColor_eq_iff_of_fibers (ϕ : G →* Perm (Fin m)) {κ κ' : Type*} (c : Fin m → κ)
    (c' : Fin m → κ') (h : ∀ γ γ', c γ = c γ' ↔ c' γ = c' γ') (u v : Ω) :
    omegaColor ϕ c u = omegaColor ϕ c v ↔ omegaColor ϕ c' u = omegaColor ϕ c' v := by
  rw [omegaColor_eq_iff_forall, omegaColor_eq_iff_forall]
  have hs : ∀ γ, {δ | c δ = c γ} = {δ | c' δ = c' γ} := fun γ => Set.ext fun δ => h δ γ
  simp only [hs]

end Windows

section RawWindows

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

open scoped Classical in
/-- §14.1, lines 4 and 5: **every raw color class of `Ω` is a color class of the Master**,
for the coloring of `Γ` by a raw outcome that decodes to `X`. -/
theorem winSet_alignRClasses_eq (hA : RawAction.WF n m A ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n A.1.2)))
    {o : RawAlignOutcome} {X : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X)
    {W : List ℕ} (hW : W ∈ alignRClasses (A, alignOutcomeLab (A.2.1, o))) :
    ∃ u : Fin n, winSet n W = omegaColorClass ϕ (alignIdx X) (omegaColor ϕ (alignIdx X) u) := by
  obtain ⟨u, hu, rfl⟩ := mem_alignRClasses hW
  have hun : u < n := by rw [← hA.1]; exact hu
  refine ⟨⟨u, hun⟩, ?_⟩
  have h := winSet_alignROmegaClass (gens := A.1.2.map (decPerm n)) (imgs := A.2.2.map (decPerm m))
    (lab := alignOutcomeLab (A.2.1, o)) (ϕ := ϕ) hA.1 hA.2.1 hA.2.2.2.2 hϕ hk ⟨u, hun⟩
  simp only [map_encPerm_decPerm hA.2.2.1, map_encPerm_decPerm hA.2.2.2.1, Prod.mk.eta] at h
  rw [h]
  ext v
  simp only [Set.mem_setOf_eq, mem_omegaColorClass]
  refine omegaColor_eq_iff_of_fibers ϕ _ _ (fun γ γ' => ?_) v ⟨u, hun⟩
  rw [alignOutcomeLab_eq_iff hA.2.1 hX γ γ']
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The raw color classes of `Ω` are pairwise different sets. -/
theorem nodup_map_winSet_alignRClasses (q : RawAction × RawLab) (hlen : q.1.1.1.length = n) :
    ((alignRClasses q).map (winSet n)).Nodup := by
  rw [alignRClasses, List.map_map]
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ List.nodup_range)
  intro u₁ h₁ u₂ h₂ he
  rw [List.mem_filter, List.mem_range] at h₁ h₂
  have hf₁ : rawGet (alignROmegaClass (q, u₁), 0) = u₁ := by
    have := h₁.2; rw [alignRIsFirst, decide_eq_true_iff] at this; exact this
  have hf₂ : rawGet (alignROmegaClass (q, u₂), 0) = u₂ := by
    have := h₂.2; rw [alignRIsFirst, decide_eq_true_iff] at this; exact this
  have hmem : (⟨u₁, by omega⟩ : Fin n) ∈ winSet n (alignROmegaClass (q, u₁)) :=
    mem_winSet.2 (self_mem_alignROmegaClass (z := (q, u₁)) h₁.1)
  have hmem' := congrArg (fun S => (⟨u₁, by omega⟩ : Fin n) ∈ S) he
  simp only [Function.comp_apply] at hmem'
  rw [hmem', mem_winSet] at hmem
  have hcol := (mem_alignROmegaClass.1 hmem).2
  have hcl : alignROmegaClass (q, u₁) = alignROmegaClass (q, u₂) := alignROmegaClass_congr hcol
  rw [← hf₁, ← hf₂, hcl]

/-- A color class of `Γ` counted on the raw labels. -/
theorem card_colorSet_eq {gdom lab : List ℕ} (hg : gdom.length = m) {κ : Type*} [DecidableEq κ]
    {c : Fin m → κ} (hc : ∀ γ γ' : Fin m, labAt lab γ = labAt lab γ' ↔ c γ = c γ')
    (γ : Fin m) : (colorSet c (c γ)).card =
      ((List.range gdom.length).filter (fun j => decide (labAt lab j = labAt lab γ))).length := by
  set L := (List.range gdom.length).filter (fun j => decide (labAt lab j = labAt lab γ)) with hL
  have hnd : L.Nodup := List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext j
  simp only [colorSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, List.mem_toFinset, hL, List.mem_filter, List.mem_range,
    decide_eq_true_eq, hg]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨δ.isLt, (hc δ γ).2 hδ⟩
  · rintro ⟨hj, hlab⟩
    exact ⟨⟨j, hj⟩, (hc ⟨j, hj⟩ γ).1 hlab, rfl⟩

/-- §14.1, line 6: **when the raw test finds no dominant color, every color class of `Γ` has
at most half of the points.** -/
theorem two_mul_card_colorSet_le {lab : List ℕ} (hg : A.2.1.length = m) {κ : Type*}
    [DecidableEq κ] {c : Fin m → κ}
    (hc : ∀ γ γ' : Fin m, labAt lab γ = labAt lab γ' ↔ c γ = c γ')
    (hnd : alignRHasDom (A, lab) = false) (i : κ) : 2 * (colorSet c i).card ≤ m := by
  by_cases hi : ∃ γ, c γ = i
  · obtain ⟨γ, rfl⟩ := hi
    rw [card_colorSet_eq hg hc γ]
    rw [alignRHasDom, decide_eq_false_iff_not, not_lt, Nat.le_zero, List.length_eq_zero_iff,
      alignRDomPoints, List.filter_eq_nil_iff] at hnd
    have ht := hnd γ (List.mem_range.2 (by rw [hg]; exact γ.isLt))
    rw [alignRDomTest, decide_eq_true_eq, not_lt] at ht
    dsimp only at ht
    omega
  · push_neg at hi
    have : colorSet c i = ∅ := by
      ext γ
      simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact hi γ
    rw [this, Finset.card_empty]
    omega

end RawWindows

/-! ## The loop of Eq. (71) as a round on the window -/

/-- An instance of the loop on the window: the header, and the call when the instance is
one. -/
abbrev Line4dInnerNode := AVHdr × Option RawWinSI

/-- The instance a node of the loop on the window stands for. -/
noncomputable def line4dInnerDecode (n : ℕ) (I : Line4dInnerNode) : SIInstance (Fin n) ℕ :=
  decWinSI n (I.2.getD ([], [], [], [], []))

/-- The loop of Eq. (71) on the window of the node, as a round.  It is a device of the
proofs only: the Master's carrier (`Algo.line4dOps`) runs these steps with every call lifted
to the node's domain.  It asks nothing of its instances (`WF` is `False`), so the laws of a
round that speak about well-formed instances hold trivially. -/
def line4dInnerRound : Round Line4dInnerNode AVState RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := avCalls I.1
  child z := z.1.2.elim
    (if z.2.1 < avCalls z.1.1 then (avChild (z.1.1, z.2.2)).map (fun J => (z.1.1, some J))
      else none) (fun _ => none)
  init I := avInit I.1
  combine z := avCombine (z.1.1, z.2.2.1, z.2.2.2)
  finish z := z.2.2.2.2
  bot := none
  child_eq_none := by
    rintro ⟨h, _ | J⟩ j s hj
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

/-- §14.1 and Eq. (71), **the loop on the window walks the Master's round**: when line 6
found no dominant color class and the header describes the shape `S`, the loop of Eq. (71)
walks `S.red` call for call, within `avCalls h` calls, and its accumulator decodes to the
answer of `S.red`. -/
theorem line4dInner_loopMatch {n : ℕ} {h : AVHdr}
    (S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2)) (hdom : S.dom = none) (hD : AVDescribes n h S (S.head :: S.tail))
    (hx : h.2.2.2.2.1.length = n) :
    LoopMatch line4dInnerRound (line4dInnerDecode n) (decCoset n) (h, none) (avCalls h) 0
      (avInit h) S.red := by
  let Good : ℕ → AVState → Prop := fun j s => j + avRem (h, s) ≤ avCalls h
  have hchild : ∀ j s J, Good j s → avChild (h, id s) = some J →
      line4dInnerRound.child ((h, none), j, s) = some (h, some J) := by
    intro j s J hg hav
    have := avRem_pos hav
    simp only [id] at this
    show (if j < avCalls h then (avChild (h, s)).map (fun J => (h, some J)) else none) =
      some (h, some J)
    rw [if_pos (by simp only [Good] at hg; omega)]
    rw [show avChild (h, s) = some J from hav]
    rfl
  have hcomb : ∀ j s a J, Good j s → avChild (h, id s) = some J →
      id (line4dInnerRound.combine ((h, none), j, s, a)) = avCombine (h, id s, a) ∧
        Good (j + 1) (line4dInnerRound.combine ((h, none), j, s, a)) := by
    intro j s a J hg hav
    refine ⟨rfl, ?_⟩
    have := avRem_combine (a := a) hav
    show j + 1 + avRem (h, avCombine (h, s, a)) ≤ avCalls h
    simp only [Good, id] at hg this
    omega
  have hstart : Good 0 (avInit h) := by
    have := avRem_init h
    show 0 + avRem (h, avInit h) ≤ avCalls h
    omega
  have hmain := phaseMatch_alignShape_value (R := line4dInnerRound)
    (decI := line4dInnerDecode n) (I := (h, none)) (h := h) (pr := id)
    (emb := fun J => (h, some J)) (Good := Good) S hdom (fun _ _ _ => rfl) hchild
    hcomb hD.action hD.giant hD.cat hD.fixed hD.versions hD.windows hx hD.lt hD.inv hD.run 0
    (avInit h) rfl hstart
  have hlenV : h.2.2.1.length = S.versions.length := by
    simpa only [List.length_map] using congrArg List.length hD.versions
  refine loopMatch_of_phaseMatch hmain ?_ (by rw [avCalls, hlenV])
  rintro b j' s' ⟨-, a, hs', ha⟩
  simp only [id] at hs'
  subst hs'
  refine ⟨?_, ha⟩
  show (if j' < avCalls h then
    (avChild (h, (h.2.2.1.length, 0, none, a))).map (fun J => (h, some J)) else none) = none
  split_ifs <;> rfl

/-! ## The Master's data the header describes -/

section MasterData

variable (p : MasterHintInput) {n m : ℕ}
    {ϕ : decGroup n (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup n (masterHintTop p).1.1.2)) (hϕ : IsGiantRep ϕ)
    (hn : 64 ≤ n) (hroute : masterHintRoute p = 4)
    {c tt dd : ℕ} (hb : Line4cBounds c tt dd)
    (hx : (masterHintTop p).2.1.length = n) (hy : (masterHintTop p).2.2.length = n)
    [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))

include hp hG hϕ hn hroute hb hx hy hK

/-- Line 4d: **the fixed version `X'` decodes, and it is a version of `X(x)`.**  Line 4c found
a version of `X(x)` (Theorem 9.2.3 applies to `x`, since line 4b failed), so the deduplicated
list for `x` is not empty and its first entry describes a version. -/
theorem line4dFixed_spec : ∃ X' : Pt (SplitOutcomes (Fin m)),
    decAlignOutcome m (line4dFixed c tt dd p) = some X' ∧
      X' ∈ line4cVers c tt dd (masterHintTop p).1 p.2.2 (masterHintTop p).2.1
        (masterHintTop p).2.2 m (decStrN n (masterHintTop p).2.1) := by
  obtain ⟨-, ⟨Z₀, hZ₀⟩, hXmem, -, -, -, -⟩ :=
    masterLine4c_versions p hp hG hϕ hn hroute hb hx hy hK
  set V := line4cVersions c tt dd (masterLine4cInput p)
  obtain ⟨hmx, -, hmemx⟩ := rawVersDedup_spec hp.2.1 V.1
  set r := rawVersDedup ((masterHintTop p).1.2.1, V.1) with hr
  have hZ₀L : Z₀ ∈ r.filterMap (decAlignOutcome m) := (hmemx Z₀).2 ((hXmem Z₀).1 hZ₀)
  obtain ⟨o₀, rest, hr0⟩ : ∃ o₀ rest, r = o₀ :: rest := by
    cases hrr : r with
    | nil => rw [hrr] at hZ₀L; simp at hZ₀L
    | cons o₀ rest => exact ⟨o₀, rest, rfl⟩
  have hfix : line4dFixed c tt dd p = o₀ := by
    rw [line4dFixed, ← hr, hr0]; rfl
  have hin : decAlignOutcome m o₀ ∈ (r.filterMap (decAlignOutcome m)).map some := by
    rw [← hmx, hr0]; exact List.mem_map_of_mem List.mem_cons_self
  obtain ⟨X', hX'L, hX'⟩ := List.mem_map.1 hin
  refine ⟨X', by rw [hfix, hX'], (hXmem X').2 ((hmemx X').1 hX'L)⟩

/-- Line 4d, Eq. (71): **the versions of `X(y)` in the header are the Master's versions,
each once.** -/
theorem line4dYs_spec :
    (line4dYs c tt dd p).map (decAlignOutcome m) =
        ((line4dYs c tt dd p).filterMap (decAlignOutcome m)).map some ∧
      ((line4dYs c tt dd p).filterMap (decAlignOutcome m)).Nodup ∧
      ∀ Z, Z ∈ (line4dYs c tt dd p).filterMap (decAlignOutcome m) ↔
        Z ∈ line4cVers c tt dd (masterHintTop p).1 p.2.2 (masterHintTop p).2.1
          (masterHintTop p).2.2 m (decStrN n (masterHintTop p).2.2) := by
  obtain ⟨-, -, -, hYmem, -, -, -⟩ := masterLine4c_versions p hp hG hϕ hn hroute hb hx hy hK
  unfold line4dYs
  by_cases hd : primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.2) = true
  · rw [if_pos hd]
    refine ⟨rfl, List.nodup_nil, fun Z => ?_⟩
    rw [hYmem Z, hd]
    simp
  · rw [if_neg hd]
    obtain ⟨h1, h2, h3⟩ := rawVersDedup_spec hp.2.1 (line4cVersions c tt dd (masterLine4cInput p)).2
    refine ⟨h1, h2, fun Z => ?_⟩
    rw [h3 Z, hYmem Z]
    simp only [Bool.not_eq_true] at hd
    simp [hd]

open scoped Classical in
/-- **Line 4d: the header describes the Master's round of Procedure Align.**  When line 6
finds no dominant color class, there is a `Babai.Line4cdData` whose round runs Procedure Align
on the versions and windows of the header: its fixed version is the decoded `X'` of the
header, its versions are the decoded versions of the header in their order, each once, and
its windows are the decoded windows of the header in their order.

The data is built with `Babai.Line4cdData.ofShape` from these lists.  What it asks of them is
what the paper asks of Procedure Align: the versions are the canonical family of Theorem
9.2.3 (line 4c, `Algo.masterLine4c_versions`), `X'` is a version of `X(x)`, the windows are the
color classes of `Ω` of line 4 (`Algo.winSet_alignRClasses_eq`), invariant under
`ϕ⁻¹(Aut(X'))`, covering `Ω`, and, with no dominant color, each of at most `4n/5` points
(Eq. (72), `Babai.five_mul_ncard_omegaColorClasses_le` at `α = 1/2`). -/
theorem exists_line4dData_of_noDom
    (hnd : alignRHasDom ((masterHintTop p).1, line4dLab c tt dd p) = false) :
    ∃ D : Line4cdData (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
        (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) m
        ((line4cVersions c tt dd (masterLine4cInput p)).2.length * (Fintype.card (Fin n) + 1) *
          AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n))),
      D.shape.dom = none ∧
        AVDescribes n (line4dHdr c tt dd p) D.shape (D.shape.head :: D.shape.tail) := by
  obtain ⟨hvl, id, ht2, hm, hmn, -⟩ := masterLine4c_facts p hp hG hϕ hn hroute
  obtain ⟨hcan, -, -, -, hfin, -, -⟩ := masterLine4c_versions p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨X', hXdec, hXmem⟩ := line4dFixed_spec p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨hYmap, hYnd, hYmem⟩ := line4dYs_spec p hp hG hϕ hn hroute hb hx hy hK
  have hWLc : alignRWindows ((masterHintTop p).1, line4dLab c tt dd p) =
      alignRClasses ((masterHintTop p).1, line4dLab c tt dd p) := alignRWindows_eq_classes hnd
  -- every window is a color class of the Master
  have hcls : ∀ W ∈ alignRWindows ((masterHintTop p).1, line4dLab c tt dd p),
      ∃ u : Fin n, winSet n W =
        omegaColorClass ϕ (alignIdx X') (omegaColor ϕ (alignIdx X') u) := by
    intro W hW
    rw [hWLc] at hW
    exact winSet_alignRClasses_eq hp hϕ hvl hXdec hW
  have hnwl : (alignRWindows ((masterHintTop p).1, line4dLab c tt dd p)).map (winSet n) ≠ [] := by
    obtain ⟨W, hW, -⟩ := alignRWindows_cover (q := ((masterHintTop p).1, line4dLab c tt dd p))
      (u := 0) (by rw [hp.1]; omega)
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h] at hW
    simp at hW
  obtain ⟨S₀, rest, hlist⟩ := List.exists_cons_of_ne_nil hnwl
  have hnd' : (S₀ :: rest).Nodup := by
    rw [← hlist, hWLc]; exact nodup_map_winSet_alignRClasses _ hp.1
  have hmemW : ∀ Δ ∈ S₀ :: rest, ∃ u : Fin n,
      Δ = omegaColorClass ϕ (alignIdx X') (omegaColor ϕ (alignIdx X') u) := by
    intro Δ hΔ
    rw [← hlist, List.mem_map] at hΔ
    obtain ⟨W, hW, rfl⟩ := hΔ
    exact hcls W hW
  have hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    obtain ⟨u, rfl⟩ := hmemW Δ hΔ
    exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hcover : (⋃ Δ ∈ S₀ :: rest, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hW, hu⟩ := alignRWindows_cover (q := ((masterHintTop p).1, line4dLab c tt dd p))
      (u := u) (by rw [hp.1]; exact u.isLt)
    exact Set.mem_iUnion₂.2 ⟨winSet n W, by rw [← hlist]; exact List.mem_map_of_mem hW,
      mem_winSet.2 hu⟩
  have hL : (S₀ :: rest).length ≤ Fintype.card (Fin n) + 1 := by
    rw [← hlist, List.length_map, Fintype.card_fin, ← hp.1]
    exact length_alignRWindows_le _
  -- no dominant class: every color class of `Γ` has at most half of the points
  have hhalf : ∀ i : AlignColor, ((colorSet (alignColor X') i).card : ℝ) ≤ 1 / 2 * m := by
    intro i
    have h2 := two_mul_card_colorSet_le (A := (masterHintTop p).1)
      (lab := line4dLab c tt dd p) hp.2.1
      (fun γ γ' => alignOutcomeLab_eq_iff hp.2.1 hXdec γ γ') hnd i
    have : (2 : ℝ) * (colorSet (alignColor X') i).card ≤ m := by exact_mod_cast h2
    linarith
  have hsizes : ∀ Δ ∈ S₀ :: rest, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, rfl⟩ := hmemW Δ hΔ
    have h4 := id.four_t
    rw [Fintype.card_fin] at h4
    exact five_mul_ncard_omegaColorClasses_le hG ϕ hϕ hvl (by omega) id.tPointOf_eq (by omega)
      (by omega) X' (α := 1 / 2) (by norm_num) (by norm_num) hhalf _
      (mem_omegaColorClasses.2 ⟨u, rfl⟩)
  let S : AlignShape (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
      (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) :=
    { m := m, ϕ := ϕ, act := inst,
      Vers := line4cVers c tt dd (masterHintTop p).1 p.2.2 (masterHintTop p).2.1
        (masterHintTop p).2.2 m,
      finY := hfin _, X' := X', head := S₀, tail := rest, dom := none,
      versions := (line4dYs c tt dd p).filterMap (decAlignOutcome m) }
  have hv : S.versions.Perm S.finY.toFinset.toList := by
    refine (List.perm_ext_iff_of_nodup hYnd (Finset.nodup_toList _)).2 fun Z => ?_
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    exact hYmem Z
  have hVlen : S.versions.length ≤ (line4cVersions c tt dd (masterLine4cInput p)).2.length :=
    (List.length_filterMap_le _ _).trans (length_line4dYs_le c tt dd p)
  have hc1 : 1 ≤ AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n)) := by
    rw [AlignDominantRoundData.alignDominantRoundCost, Fintype.card_fin]
    omega
  let D := Line4cdData.ofShape S m _ _ _ hv (List.nodup_cons.1 hnd').1 hcover hinv
    (fun D hD => by simp [S] at hD) (fun D hD => by simp [S] at hD) hcan hXmem hVlen hL hc1
    (fun D hD => by simp [S] at hD) (fun Δ hΔ _ => hsizes Δ hΔ)
  have hlt : ∀ W ∈ alignRWindows ((masterHintTop p).1, line4dLab c tt dd p), ∀ u ∈ W,
      u < n := by
    intro W hW u hu
    have := lt_of_mem_of_mem_alignRWindows hW hu
    rw [hp.1] at this
    exact this
  refine ⟨D, rfl, ?_⟩
  exact ⟨alignShape_red_of_dom_none S rfl, hp, hϕ, hK, hXdec, hYmap, hlist, List.cons_ne_nil _ _,
    hlt, hinv, D.run_red⟩

open scoped Classical in
/-- **Line 4d, a dominant class with a trivial structure** (§14.1, lines 6–7).  When line 6
finds a dominant color class `Δ_j` but `m* < 2`, the class is a single block of the
`3/4`-partition `X'` (`Algo.four_mul_ncard_domClass_le`), so line 7's "nontrivial
equipartition" fails and the round does not expand the dominant window.  The Master's round
then runs Procedure Align on the windows of lines 5 and 6 as they are: the window `Ω(Δ_j)`
first, then the other color classes.  Each has at most `4n/5` points: `Ω(Δ_j)` by Eq. (72) at
`α = 3/4`, since `|Δ_j| ≤ 3m/4`, and the others by Eq. (72) at `α = 1/2`
(`Babai.five_mul_ncard_omegaColorClass_le_of_ne_dom`). -/
theorem exists_line4dData_of_trivDom
    (hhd : alignRHasDom ((masterHintTop p).1, line4dLab c tt dd p) = true)
    (hms : alignRMs ((masterHintTop p).1, line4dFixed c tt dd p) < 2) :
    ∃ D : Line4cdData (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
        (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) m
        ((line4cVersions c tt dd (masterLine4cInput p)).2.length * (Fintype.card (Fin n) + 1) *
          AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n))),
      D.shape.dom = none ∧
        AVDescribes n (line4dHdr c tt dd p) D.shape (D.shape.head :: D.shape.tail) := by
  obtain ⟨hvl, id, ht2, hm, hmn, -⟩ := masterLine4c_facts p hp hG hϕ hn hroute
  obtain ⟨hcan, -, -, -, hfin, -, hgood⟩ :=
    masterLine4c_versions p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨X', hXdec, hXmem⟩ := line4dFixed_spec p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨hYmap, hYnd, hYmem⟩ := line4dYs_spec p hp hG hϕ hn hroute hb hx hy hK
  have hZ := hgood _ X' hXmem
  have hd : (masterHintTop p).1.1.1.length = n := hp.1
  have hg : (masterHintTop p).1.2.1.length = m := hp.2.1
  have h4t : 4 * p.2.2 < m := by simpa only [Fintype.card_fin] using id.four_t
  have h34 := four_mul_ncard_domClass_le hp hXdec hZ hhd hms
  set lab := line4dLab c tt dd p with hlab
  set dc := alignRDomColor ((masterHintTop p).1, lab) with hdcdef
  set domWin := alignRDomWindow (((masterHintTop p).1, lab), dc) with hdomWin
  have hW : alignRWindows ((masterHintTop p).1, lab) =
      domWin :: (alignRClasses ((masterHintTop p).1, lab)).filter
        (fun W => alignRNotDom (((masterHintTop p).1, lab), W)) := by
    rw [alignRWindows, if_pos hhd]
  -- the dominant class, as a class of `Babai.alignIdx`
  set γ₀ : Fin m := ⟨(alignRDomPoints ((masterHintTop p).1, lab)).getD 0 0,
    alignRDomFirst_lt hg hhd⟩
  haveI : Nonempty (AlignIdx X') := nonempty_alignIdx (by omega)
  set i₀ := alignIdx X' γ₀ with hi₀
  have hset : {γ : Fin m | labAt lab (γ : ℕ) = dc} = {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ
    simp only [Set.mem_setOf_eq]
    rw [show dc = labAt lab (γ₀ : ℕ) from rfl, hlab, line4dLab,
      alignOutcomeLab_eq_iff hg hXdec γ γ₀, hi₀]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hcs : ((colorSet (alignIdx X') i₀ : Finset (Fin m)) : Set (Fin m)) =
      {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ; simp [colorSet]
  have hcard : (colorSet (alignIdx X') i₀).card = {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard := by
    rw [← Set.ncard_coe_finset, hcs, ← hset]
  have hdomI : m < 2 * (colorSet (alignIdx X') i₀).card := by
    rw [hcard]
    exact alignRDomColor_dominant_of_wf hp hhd
  have h34' : 4 * (colorSet (alignIdx X') i₀).card ≤ 3 * m := by
    rw [hcard]; exact h34
  set v₀ : AlignIdx X' → ℕ := fun j => if j = i₀ then p.2.2 else 0 with hv₀def
  have hS₀eq : omegaColorClass (Ω := Fin n) ϕ (alignIdx X') v₀ =
      omegaOf ϕ {γ : Fin m | alignIdx X' γ = i₀} :=
    omegaColorClass_eq_omegaOf ϕ id.tPointOf_eq (alignIdx X') i₀ v₀ (by simp [hv₀def])
      (fun j hj => by simp [hv₀def, hj])
  have hhead : winSet n domWin = omegaColorClass (Ω := Fin n) ϕ (alignIdx X') v₀ := by
    rw [hS₀eq, hdomWin, winSet_alignRDomWindow_of_wf hp hϕ hvl lab dc, hset]
  -- the windows
  set head : Set (Fin n) := winSet n domWin with hheaddef
  set tail : List (Set (Fin n)) :=
    ((alignRClasses ((masterHintTop p).1, lab)).filter
      (fun W => alignRNotDom (((masterHintTop p).1, lab), W))).map (winSet n) with htaildef
  have hlist : (alignRWindows ((masterHintTop p).1, lab)).map (winSet n) = head :: tail := by
    rw [hW]; rfl
  have htailmem : ∀ Δ ∈ tail, ∃ u : ℕ,
      alignROmegaClass (((masterHintTop p).1, lab), u) ∈ alignRClasses ((masterHintTop p).1, lab) ∧
      alignROmegaClass (((masterHintTop p).1, lab), u) ≠ domWin ∧
      Δ = winSet n (alignROmegaClass (((masterHintTop p).1, lab), u)) := by
    intro Δ hΔ
    obtain ⟨W, hW', rfl⟩ := List.mem_map.1 hΔ
    rw [List.mem_filter, alignRNotDom, decide_eq_true_iff] at hW'
    obtain ⟨u, -, rfl⟩ := mem_alignRClasses hW'.1
    exact ⟨u, hW'.1, hW'.2, rfl⟩
  have hne : head ∉ tail := by
    intro hmem
    obtain ⟨u, -, hune, he⟩ := htailmem head hmem
    exact winSet_alignROmegaClass_ne (q := ((masterHintTop p).1, lab)) hd hune he.symm
  have hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hWm, hu⟩ := alignRWindows_cover (q := ((masterHintTop p).1, lab)) (u := u)
      (by rw [hd]; exact u.isLt)
    refine Set.mem_iUnion₂.2 ⟨winSet n W, ?_, mem_winSet.2 hu⟩
    rw [← hlist]
    exact List.mem_map_of_mem hWm
  have hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · rw [hhead]
      exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
    · obtain ⟨u, hcl, -, rfl⟩ := htailmem Δ hΔ
      obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hp hϕ hvl hXdec hcl
      rw [hv]
      exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hsizes : ∀ Δ ∈ head :: tail, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · -- the window `Ω(Δ_j)`: Eq. (72) at `α = 3/4`
      rw [hhead]
      refine five_mul_ncard_omegaColorClass_le_of_le_at hG ϕ hϕ hvl (by omega) id.tPointOf_eq
        (by omega) (by omega) (alignIdx X') (α := 3 / 4) (by norm_num) (by norm_num) v₀ ?_
      intro i hi
      by_cases hii : i = i₀
      · rw [hii]
        have : (4 : ℝ) * (colorSet (alignIdx X') i₀).card ≤ 3 * m := by exact_mod_cast h34'
        linarith
      · simp only [hv₀def, hii, if_false] at hi
        omega
    · -- the other classes: Eq. (72) at `α = 1/2`
      obtain ⟨u, hcl, hune, rfl⟩ := htailmem Δ hΔ
      obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hp hϕ hvl hXdec hcl
      rw [hv]
      refine five_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) id.tPointOf_eq
        (by omega) (by omega) (alignIdx X') hdomI _ ?_
      rw [← hv, ← hS₀eq, ← hhead]
      exact winSet_alignROmegaClass_ne (q := ((masterHintTop p).1, lab)) hd hune
  have hL : (head :: tail).length ≤ Fintype.card (Fin n) + 1 := by
    rw [← hlist, List.length_map, Fintype.card_fin, ← hd]
    exact length_alignRWindows_le _
  let S : AlignShape (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
      (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) :=
    { m := m, ϕ := ϕ, act := inst,
      Vers := line4cVers c tt dd (masterHintTop p).1 p.2.2 (masterHintTop p).2.1
        (masterHintTop p).2.2 m,
      finY := hfin _, X' := X', head := head, tail := tail, dom := none,
      versions := (line4dYs c tt dd p).filterMap (decAlignOutcome m) }
  have hv : S.versions.Perm S.finY.toFinset.toList := by
    refine (List.perm_ext_iff_of_nodup hYnd (Finset.nodup_toList _)).2 fun Z => ?_
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    exact hYmem Z
  have hVlen : S.versions.length ≤ (line4cVersions c tt dd (masterLine4cInput p)).2.length :=
    (List.length_filterMap_le _ _).trans (length_line4dYs_le c tt dd p)
  have hc1 : 1 ≤ AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n)) := by
    rw [AlignDominantRoundData.alignDominantRoundCost, Fintype.card_fin]
    omega
  let D := Line4cdData.ofShape S m _ _ _ hv hne hcover hinv
    (fun D hD => by simp [S] at hD) (fun D hD => by simp [S] at hD) hcan hXmem hVlen hL hc1
    (fun D hD => by simp [S] at hD) (fun Δ hΔ _ => hsizes Δ hΔ)
  have hlt : ∀ W ∈ alignRWindows ((masterHintTop p).1, line4dLab c tt dd p), ∀ u ∈ W,
      u < n := by
    intro W hW u hu
    have := lt_of_mem_of_mem_alignRWindows hW hu
    rw [hp.1] at this
    exact this
  refine ⟨D, rfl, ?_⟩
  exact ⟨alignShape_red_of_dom_none S rfl, hp, hϕ, hK, hXdec, hYmap, hlist, List.cons_ne_nil _ _,
    hlt, hinv, D.run_red⟩

/-- **Line 4d: the header describes the Master's round of Procedure Align** whenever lines
6–7 do not expand a dominant window (`Algo.line4dHasDom = false`): either there is no
dominant color class (`Algo.exists_line4dData_of_noDom`), or there is one with `m* < 2`, a
single block (`Algo.exists_line4dData_of_trivDom`). -/
theorem exists_line4dData (hnd : line4dHasDom c tt dd p = false) :
    ∃ D : Line4cdData (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
        (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) m
        ((line4cVersions c tt dd (masterLine4cInput p)).2.length * (Fintype.card (Fin n) + 1) *
          AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n))),
      D.shape.dom = none ∧
        AVDescribes n (line4dHdr c tt dd p) D.shape (D.shape.head :: D.shape.tail) := by
  cases hd0 : alignRHasDom ((masterHintTop p).1, line4dLab c tt dd p)
  · exact exists_line4dData_of_noDom p hp hG hϕ hn hroute hb hx hy hK hd0
  · have hms : alignRMs ((masterHintTop p).1, line4dFixed c tt dd p) < 2 := by
      have h := hnd
      unfold line4dHasDom at h
      rw [hd0, Bool.true_and, decide_eq_false_iff_not] at h
      omega
    exact exists_line4dData_of_trivDom p hp hG hϕ hn hroute hb hx hy hK hd0 hms

end MasterData

end Algo

#print axioms Algo.quasiFun_line4dHdr
#print axioms Algo.line4dInner_loopMatch
#print axioms Algo.exists_line4dData
#print axioms Algo.exists_line4dData_of_trivDom
