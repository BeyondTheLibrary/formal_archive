/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 4c and 4d: what a branch that runs on the window has to provide, and the
four facts its lift to `Ω` then has.
-/
import Workspace.Master.HintTransport
import Workspace.Master.Line4cd
import Workspace.Master.CosetAlignExpand

/-!
# The branch of lines 4c–4d on the window, and its lift

Lines 4c–4d run on the window `Δ` of the instance: the Extended Design Lemma is applied to
the hypergraph `H(x|_Δ)` on `Γ`, and Procedure Align runs on `Ω = ↥Δ` with the group
`G = K^Δ`.  `Babai.liftWindow` carries the result back to `Ω`.

`Babai.Line4cdCore` is the list of what the branch on the window produces: the reduction,
the hint of line 11 of Procedure Align, and the five facts the fields of
`Babai.Sec15Remaining` ask for, stated on the window.  This file turns a
`Babai.Line4cdCore` into those five facts on `Ω`.  The only step that is not immediate is
the hint: the round attaches a `Babai.JohnsonCaseData` to a call `J'` of the window type,
and the field `lift` asks for one on `Ω`.  `Babai.windowHintLift` is the transport, built on
`Babai.JohnsonCaseData.ofWindow`.

The transport recognizes the lifted instances: `Babai.LiftedHint` says that the instance on
`Ω` comes from a call of the window type that carries a hint.  Which call is recognized does
not matter — a hinted instance only ever has a *smaller* Johnson parameter, and the bound
`2m* ≤ m` of Eq. (73) is asked of every hint the round attaches (`Line4cdCore.hint_le`), so
it holds whichever call is recognized.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

/-! ### The hint of a call, read on `Ω` -/

section HintLift

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} [Fintype Δ]

/-- §15: the instance `J` on `Ω` is the lift of a call of the window type that carries a
hint, and that hint is with respect to a subgroup of the group `K^Δ` induced on the
window. -/
def LiftedHint (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (x₀ : Ω → A) (H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J'))
    (J : SIInstance Ω A) : Prop :=
  ∃ J' : SIInstance Δ A, windowInstance K Δ hinv x₀ J' = J ∧ (H J').isSome = true ∧
    ∀ d : JohnsonCaseData J', H J' = some d → d.K ≤ restrictTo K Δ hinv

/-- Transporting a Johnson case along an equality of instances does not change its Johnson
parameter. -/
theorem JohnsonCaseData.m_of_eqRec {I J : SIInstance Ω A} (h : I = J)
    (d : JohnsonCaseData I) : (h ▸ d).m = d.m := by subst h; rfl

/-- Transporting a Johnson case along an equality of instances does not change its group. -/
theorem JohnsonCaseData.K_of_eqRec {I J : SIInstance Ω A} (h : I = J)
    (d : JohnsonCaseData I) : (h ▸ d).K = d.K := by subst h; rfl

open scoped Classical in
/-- §15, line 11 of Procedure Align: **the hint a branch that runs on the window attaches to
a call, read on `Ω`**.  It is `Babai.JohnsonCaseData.ofWindow` applied to the hint of a call
of the window type that the instance comes from. -/
noncomputable def windowHintLift (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    (H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J')) (J : SIInstance Ω A) :
    Option (JohnsonCaseData J) :=
  if h : LiftedHint K Δ hinv x₀ H J then
    some (h.choose_spec.1 ▸ (((H h.choose).get h.choose_spec.2.1).ofWindow hinv x₀
      (h.choose_spec.2.2 _ (Option.some_get h.choose_spec.2.1).symm)))
  else none

/-- The lifted hint of an instance that is not recognized is empty. -/
theorem windowHintLift_of_not (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J')} {J : SIInstance Ω A}
    (h : ¬ LiftedHint K Δ hinv x₀ H J) : windowHintLift hinv x₀ H J = none := by
  classical
  rw [windowHintLift, dif_neg h]

/-- **The Johnson parameter of the lifted hint is the Johnson parameter of a hint the branch
attached on the window.**  Which one is not determined, and does not have to be: the bound
`Babai.Line4cdCore.hint_le` is asked of every one of them. -/
theorem param_windowHintLift (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J')} {J : SIInstance Ω A}
    (h : LiftedHint K Δ hinv x₀ H J) :
    ∃ (J' : SIInstance Δ A) (d : JohnsonCaseData J'), H J' = some d ∧
      param (⟨J, windowHintLift hinv x₀ H J⟩ : HintedInstance Ω A) = d.m := by
  classical
  refine ⟨h.choose, (H h.choose).get h.choose_spec.2.1,
    (Option.some_get h.choose_spec.2.1).symm, ?_⟩
  rw [windowHintLift, dif_pos h]
  exact (JohnsonCaseData.m_of_eqRec _ _).trans (JohnsonCaseData.ofWindow_m _ _ _ _)

end HintLift

/-! ### What the branch on the window provides -/

section Core

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 4c and 4d on the window**: the reduction the branch builds, the hint of
line 11 of Procedure Align, and the five facts the fields of `Babai.Sec15Remaining` ask
for, stated on the window type.

**This is an output format, not a specification.**  The field `red` is free, so
`red := .done (Iso_G(x,y))` fills every field at cost `0`.  Nothing is ever *chosen* at this
type: the rounds of lines 4c–4d and of lines 5–7 are chosen as data
(`Babai.Line4cdData`, `Babai.Line57Data`) and read through this interface by `toCore`, which
is what the lift to `Ω` below is stated for.  See the corrected paper entries on Finding 1
of the audit of Secs. 14–15.

* `par` is the Johnson parameter `m` of the ambient instance, which Eq. (73) halves;
* `cost` is the number of instances the branch produces. -/
structure Line4cdCore (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Equiv.Perm W)) (x y : W → A) (par cost : ℕ) where
  /-- The reduction of lines 4c–4d on the window. -/
  red : SIReduction W A (Set (Equiv.Perm W))
  /-- Line 11 of Procedure Align: the hint each call carries. -/
  hint : (J : SIInstance W A) → Option (JohnsonCaseData J)
  /-- The reduction is correct. -/
  run_red : red.run = strIso (G : Set (Equiv.Perm W)) x y
  /-- Every call is made with respect to a subset of `G`, so the lift to `Ω` applies. -/
  calls_K : ∀ J ∈ red.calls, J.K ⊆ (G : Set (Equiv.Perm W))
  /-- Every call is a group instance. -/
  calls_group : ∀ J ∈ red.calls, IsGroupInstance J
  /-- The number of calls. -/
  calls_length : red.calls.length ≤ cost
  /-- Every hint is with respect to a subgroup of `G`, and its Johnson parameter is at most
  half of `par` — Eq. (73). -/
  hint_le : ∀ (J : SIInstance W A) (d : JohnsonCaseData J), hint J = some d →
    d.K ≤ G ∧ 2 * d.m ≤ par
  /-- Every call either has a window of at most `4n/5` points or carries a hint.  The
  constant is the one of `Babai.MakesProgress`; see the corrected paper entry on Sec. 15
  lines 5–7a and Sec. 14.2 Eqs. (72)–(73). -/
  calls_progress : ∀ J ∈ red.calls,
    5 * J.windowSize ≤ 4 * Fintype.card W ∨ (hint J).isSome = true

end Core

/-! ### The data of one round of Procedure Align, and the reduction built from it

`Babai.Line4cdCore` stores the reduction as a field, so nothing in it ties the reduction to
Procedure Align: the leaf `.done (Iso_G(x,y))` fills every field, at cost `0`.  See
the corrected paper entry on Finding 1 of the audit of Secs. 14–15.

`Babai.AlignShape` is the repair for lines 4c–4d.  It carries the **geometric data** of one
round of Procedure Align — the giant representation, the canonical family of versions of
Theorem 9.2.3, the fixed version of `X(x)`, the color classes with the window of line 6
first, and the round of lines 7–11 on that window when line 6 found a dominant color — and
the reduction is a `def` on that data, `Babai.AlignShape.red`.  Choosing the data is
allowed: the paper says *"find a minimal block system"*, *"apply the Extended Design
Lemma"*.  Choosing an arbitrary correct program is not.

**One code path for both cases of line 6.**  When there is no dominant color, the expansion
of line 6 is the identity (`Babai.SIReduction.expand_call_done`), so `red` is the plain
Chain Rule of line 5 over the color classes, `Babai.designAlignReduction`. -/

section Shape

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §14.1 and §15, lines 4d–7a: **the data one round of Procedure Align runs on**.

* `m` and `ϕ` are the giant representation `ϕ : G → S(Γ)` with `Γ = Fin m`;
* `act` is the action of `S(Γ)` on the outcomes of Theorem 9.2.3
  (`Babai.exists_isCatAction_splitOutcomes`);
* `Vers` is the canonical family of versions of the structure, `X'` the fixed version of
  `X(x)`;
* `head` and `tail` are the color classes of `Ω`, the window of line 6 first;
* `dom` is the round of lines 7–11 on `head`, present exactly when line 6 found a dominant
  color class. -/
structure AlignShape (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Equiv.Perm W)) (x y : W → A) where
  /-- The number of points of `Γ`. -/
  m : ℕ
  /-- The giant representation `ϕ : G → S(Γ)`. -/
  ϕ : G →* Equiv.Perm (Fin m)
  /-- The action of `S(Γ)` on the outcomes of Theorem 9.2.3. -/
  act : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))
  /-- The canonical family of versions of the structure, Theorem 9.2.3. -/
  Vers : (W → A) → Set (Pt (SplitOutcomes (Fin m)))
  /-- The versions of `y` are finitely many — Eq. (71). -/
  finY : (Vers y).Finite
  /-- The fixed version of `X(x)`. -/
  X' : Pt (SplitOutcomes (Fin m))
  /-- Line 6: the color class the Chain Rule of line 5 starts with. -/
  head : Set W
  /-- The other color classes. -/
  tail : List (Set W)
  /-- Lines 7–11 on the window of line 6, when line 6 found a dominant color class. -/
  dom : Option (AlignDominantRoundData W)
  /-- Eq. (71): the supplied order of the target versions. -/
  versions : List (Pt (SplitOutcomes (Fin m))) := finY.toFinset.toList
  /-- Lines 7–11: the supplied orbit and coset enumerations. -/
  domEnum : AlignDominantEnum W := match dom with
    | none => ⟨[], [], fun _ => []⟩
    | some D => D.defaultCosetEnum

namespace AlignShape

variable {G : Subgroup (Equiv.Perm W)} {x y : W → A} (S : AlignShape W A G x y)

/-- §14.1, lines 6–11: **what the Chain Rule of line 5 does on the window it starts with**.
When line 6 found a dominant color class, the call on that window is expanded by the round
of lines 7–11; otherwise the call stands. -/
noncomputable def dominantRound (J : SIInstance W A) : SIReduction W A (Set (Equiv.Perm W)) :=
  match S.dom with
  | none => .call J .done
  | some D => D.cosetRound S.domEnum J

/-- §15, **lines 4d and 7a**: the reduction of one round of Procedure Align, as a named
function of the data: the branching over the versions of `X(y)` (Eq. (71)), then Procedure
Align lines 1–3 on each pair of versions, then the Chain Rule of line 5 over the color
classes with the window of line 6 first, with the call on that window expanded by the round
of lines 7–11. -/
noncomputable def red : SIReduction W A (Set (Equiv.Perm W)) :=
  letI := S.act
  cosetAlignExpand S.ϕ x y S.X' S.versions S.head S.tail S.dominantRound

/-- §14.1, line 11: **the hint the round attaches to each of its calls**.  Only the round
of lines 7–11 has one to attach. -/
noncomputable def hint (J : SIInstance W A) : Option (JohnsonCaseData J) :=
  match S.dom with
  | none => none
  | some D => D.hint J J

end AlignShape

/-- §15, **lines 4c and 4d on the window**: one round of Procedure Align, as the data of
`Babai.AlignShape` together with the five facts the fields of `Babai.Sec15Remaining` ask
for.  The reduction is not a field: it is `Babai.AlignShape.red`.

* `par` is the Johnson parameter `m` of the ambient instance, which Eq. (73) halves;
* `cost` is the number of instances the round produces. -/
structure Line4cdData (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Equiv.Perm W)) (x y : W → A) (par cost : ℕ) where
  /-- The data Procedure Align runs on. -/
  shape : AlignShape W A G x y
  /-- Eq. (71): every version is listed once. -/
  versions_spec : shape.versions.Perm shape.finY.toFinset.toList
  /-- Lines 4–6: the head is not repeated among the remaining windows. -/
  head_not_mem : shape.head ∉ shape.tail
  /-- The listed windows cover the domain. -/
  windows_cover : (⋃ Δ ∈ shape.head :: shape.tail, Δ) = Set.univ
  /-- The source stabilizer preserves each listed window. -/
  windows_invariant : letI := shape.act
    ∀ Δ ∈ shape.head :: shape.tail,
      IsInvariant (preimageSubgroup shape.ϕ (structAut shape.X')) Δ
  /-- The dominant round uses the source stabilizer and the first window. -/
  dom_spec : letI := shape.act
    ∀ D, shape.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup shape.ϕ (structAut shape.X') ∧
      D.toAlignDominant.window = shape.head
  /-- The supplied dominant enumerations meet their cover, order, and size conditions. -/
  domEnum_spec : ∀ D, shape.dom = some D → shape.domEnum.Spec D
  /-- The reduction is correct. -/
  run_red : shape.red.run = strIso (G : Set (Equiv.Perm W)) x y
  /-- Every call is made with respect to a subset of `G`, so the lift to `Ω` applies. -/
  calls_K : ∀ J ∈ shape.red.calls, J.K ⊆ (G : Set (Equiv.Perm W))
  /-- Every call is a coset instance in the ambient group. -/
  calls_coset : ∀ J ∈ shape.red.calls, IsCosetInstance G J
  /-- The number of calls. -/
  calls_length : shape.red.calls.length ≤ cost
  /-- Every hint is with respect to a subgroup of `G`, and its Johnson parameter is at most
  half of `par` — Eq. (73). -/
  hint_le : ∀ (J : SIInstance W A) (d : JohnsonCaseData J), shape.hint J = some d →
    d.K ≤ G ∧ 2 * d.m ≤ par
  /-- Every call either has a window of at most `4n/5` points or carries a hint. -/
  calls_progress : ∀ J ∈ shape.red.calls,
    5 * J.windowSize ≤ 4 * Fintype.card W ∨ (shape.hint (alignInst J)).isSome = true

/-- Legacy group interface. Live branches use `toCosetCore` and align after lifting. -/
noncomputable def Line4cdData.toCore {G : Subgroup (Equiv.Perm W)} {x y : W → A} {par cost : ℕ}
    (C : Line4cdData W A G x y par cost) : Line4cdCore W A G x y par cost where
  red := C.shape.red.alignCalls
  hint := C.shape.hint
  run_red := by rw [run_alignCalls]; exact C.run_red
  calls_K := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact K_alignInst_subset (C.calls_coset J' hJ')
  calls_group := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact isGroupInstance_alignInst (C.calls_coset J' hJ')
  calls_length := by rw [calls_alignCalls, List.length_map]; exact C.calls_length
  hint_le := C.hint_le
  calls_progress := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact C.calls_progress J' hJ' 

/-- Sec. 14.1: the list and geometric specifications prove all facts about the
coset round. The proof does not select any enumeration. -/
noncomputable def Line4cdData.ofShape {G : Subgroup (Perm W)} {x y : W → A}
    (S : AlignShape W A G x y) (par V L c : ℕ)
    (hv : S.versions.Perm S.finY.toFinset.toList)
    (hne : S.head ∉ S.tail)
    (hcover : (⋃ Δ ∈ S.head :: S.tail, Δ) = Set.univ)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head ∧ D.toAlignDominant.m = par)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D)
    (hcan : letI := S.act; IsCanonicalVersions S.ϕ S.Vers) (hX : S.X' ∈ S.Vers x)
    (hV : S.versions.length ≤ V) (hL : (S.head :: S.tail).length ≤ L)
    (hc : 1 ≤ c)
    (hcD : ∀ D, S.dom = some D →
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card W) ≤ c)
    (hsmall : ∀ Δ ∈ S.head :: S.tail, (Δ ≠ S.head ∨ S.dom = none) →
      5 * Δ.ncard ≤ 4 * Fintype.card W) : Line4cdData W A G x y par (V * L * c) := by
  classical
  letI := S.act
  have hr : ∀ J : SIInstance W A,
      CosetAlignCall G (preimageSubgroup S.ϕ (structAut S.X')) S.head S.tail J →
      J.Δ = S.head → (S.dominantRound J).run = J.answer := by
    intro J hJ hΔ
    unfold AlignShape.dominantRound
    split
    · rfl
    · next D hD =>
        apply D.run_cosetRound _ (he D hD) J
        · obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
          exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩
        · rw [(hd D hD).2.1]; exact hΔ
  have hg : ∀ J ∈ S.red.calls, IsCosetInstance G J := by
    refine calls_cosetAlignExpand (x := x) (y := y) (versions := S.versions) hne hinv hr ?_ ?_
    · intro J hJ hΔ K hK
      unfold AlignShape.dominantRound at hK
      split at hK
      · simp only [SIReduction.calls_call, SIReduction.calls_done, List.mem_singleton] at hK
        subst K
        exact hJ.2.1
      · next D hD =>
          refine D.isCosetInstance_calls_cosetRound _ (he D hD) ?_ J ?_ K hK
          · rw [(hd D hD).1]; exact preimageSubgroup_le _ _
          · rw [(hd D hD).1]; exact hJ.2.2 hΔ
    · exact fun J hJ _ => hJ.2.1
  refine {
    shape := S
    versions_spec := hv
    head_not_mem := hne
    windows_cover := hcover
    windows_invariant := hinv
    dom_spec := fun D hD => ⟨(hd D hD).1, (hd D hD).2.1⟩
    domEnum_spec := he
    run_red := ?_
    calls_K := fun J hJ => (hg J hJ).K_subset
    calls_coset := hg
    calls_length := ?_
    hint_le := ?_
    calls_progress := ?_ }
  · exact run_cosetAlignExpand hcan hX
      (fun Y => hv.mem_iff.trans (by simp)) hne hinv hcover hr
  · refine (calls_length_cosetAlignExpand hne hinv hr hc ?_).trans
      (Nat.mul_le_mul_right c (Nat.mul_le_mul hV hL))
    intro J hJ hΔ
    unfold AlignShape.dominantRound
    split
    · simpa using hc
    · next D hD => exact (D.calls_length_cosetRound _ (he D hD) J).trans (hcD D hD)
  · intro J d hJ
    unfold AlignShape.hint at hJ
    split at hJ
    · simp at hJ
    · next D hD =>
        by_cases hh : D.HasHint J J
        · rw [AlignDominantRoundData.hint, dif_pos hh] at hJ
          have heq := (Option.some.inj hJ).symm
          subst d
          constructor
          · rw [JohnsonCaseData.K_of_eqRec]
            change D.toAlignDominant.Gs ≤ G
            rw [(hd D hD).1]
            exact preimageSubgroup_le _ _
          · rw [JohnsonCaseData.m_of_eqRec]
            change 2 * D.toAlignDominant.ms ≤ par
            rw [← (hd D hD).2.2]
            exact D.toAlignDominant.param_halved
        · rw [AlignDominantRoundData.hint, dif_neg hh] at hJ
          simp at hJ
  · refine calls_cosetAlignExpand (x := x) (y := y) (versions := S.versions) hne hinv hr ?_ ?_
    · intro J hJ hΔ K hK
      unfold AlignShape.dominantRound at hK
      split at hK
      · next hD =>
          simp only [SIReduction.calls_call, SIReduction.calls_done, List.mem_singleton] at hK
          subst K
          exact Or.inl (hsmall J.Δ hJ.1 (Or.inr hD))
      · next D hD =>
          have hk : ∃ σ : Perm W, J.K = σ • (D.toAlignDominant.Gs : Set (Perm W)) := by
            obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
            exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩
          rcases D.cosetRound_small_or_hint _ (he D hD) J hk K hK with hs | hh
          · exact Or.inl (by omega)
          · right
            simp only [AlignShape.hint, hD]
            rw [AlignDominantRoundData.hint, dif_pos hh]
            rfl
    · intro J hJ hj
      exact Or.inl (hsmall J.Δ hJ.1 (Or.inl hj))

/-! #### The regression: the round cannot write the answer down

These are the statements that fail for the old `Babai.Line4cdCore`, where `red` was a field
and `red := .done (Iso_G(x,y))` was allowed at cost `0`.  Now `red` is built from the data,
and the round makes a call as soon as one version of `y` is carried to the fixed version of
`x` by an element of `G` — which is the only case in which Procedure Align has anything to
compare. -/

namespace SIReduction

/-- Replacing every call by the same call changes nothing. -/
theorem expand_call_done (R : SIReduction W A (Set (Equiv.Perm W))) :
    R.expand (fun I => .call I .done) = R := by
  induction R with
  | done a => rw [SIReduction.expand]
  | call I k ih =>
    rw [SIReduction.expand]
    show SIReduction.call I (fun a => (k a).expand _) = _
    exact congrArg _ (funext ih)

/-- A call of one branch of the union of Eq. (71) is a call of the union. -/
theorem mem_calls_unionOver_of_mem {𝒴 : Type*}
    (b : 𝒴 → SIReduction W A (Set (Equiv.Perm W))) {L : List 𝒴} {Y : 𝒴} (hY : Y ∈ L)
    {J : SIInstance W A} (hJ : J ∈ (b Y).calls) :
    J ∈ (SIReduction.unionOver L b).calls := by
  induction L with
  | nil => exact absurd hY (List.not_mem_nil)
  | cons Z rest ih =>
    have hcalls : (SIReduction.unionOver (Z :: rest) b).calls
        = (b Z).calls ++ (SIReduction.unionOver rest b).calls := by
      simp [SIReduction.unionOver]
    rw [hcalls, List.mem_append]
    rcases List.mem_cons.1 hY with rfl | hmem
    · exact Or.inl hJ
    · exact Or.inr (ih hmem)

/-- If every substituted sub-reduction makes a call, substitution keeps the calls. -/
theorem calls_expand_ne_nil
    {f : SIInstance W A → SIReduction W A (Set (Equiv.Perm W))} (hf : ∀ I, (f I).calls ≠ [])
    {R : SIReduction W A (Set (Equiv.Perm W))} (hR : R.calls ≠ []) :
    (R.expand f).calls ≠ [] := by
  cases R with
  | done a => exact absurd rfl hR
  | call I k =>
    obtain ⟨J, hJ⟩ := List.exists_mem_of_ne_nil _ (hf I)
    refine List.ne_nil_of_mem (a := J) ?_
    rw [SIReduction.expand, SIReduction.calls_bind]
    exact List.mem_append_left _ hJ

end SIReduction

section Regression

variable {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳]
  {G : Subgroup (Equiv.Perm W)}

/-- §14.1, lines 1–3: a branch that is not rejected makes the calls of its continuation. -/
theorem calls_alignBranch_ne_nil {ϕ : G →* Equiv.Perm Γ} (y : W → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm W) → (W → A) → SIReduction W A (Set (Equiv.Perm W)))
    (h : ∃ σ : G, (ϕ σ) • X' = Y')
    (hk : ∀ z, (k (preimageSubgroup ϕ (structAut X')) z).calls ≠ []) :
    (alignBranch ϕ y X' Y' k).calls ≠ [] := by
  classical
  rw [alignBranch, dif_pos h, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil]
  exact hk _

/-- §14.1, line 5: the Chain Rule over a nonempty list of windows begins with a call. -/
theorem calls_alignChainReduction_ne_nil (N : Subgroup (Equiv.Perm W)) (Δ : Set W)
    (Δs : List (Set W)) (x z : W → A) :
    (alignChainReduction N (Δ :: Δs) x z).calls ≠ [] := by
  rw [alignChainReduction, chainReduction, SIReduction.calls_call]
  exact List.cons_ne_nil _ _

/-- The Chain Rule over a nonempty list of windows begins with a call, at any shift and any
group. -/
theorem calls_chainReduction_ne_nil (N : Subgroup (Equiv.Perm W)) (x z : W → A) (Δ : Set W)
    (Δs : List (Set W)) (σ : Equiv.Perm W) (M : Subgroup (Equiv.Perm W)) :
    (chainReduction (A := A) N x z (Δ :: Δs) σ M).calls ≠ [] := by
  rw [chainReduction, SIReduction.calls_call]
  exact List.cons_ne_nil _ _

/-- **Regression, Finding 1 of the audit of Secs. 14–15.**  The round of lines 7–11 on the
dominant window makes at least one call, as soon as that window has a point.

Both cases of line 7 make one.  In cases 2 and 3 the round is the Chain Rule over the
orbits of `G*` inside the window, and a point of the window has its orbit in that list.  In
case 1 it is Luks's descent to `ker ϕ*` over the coset representatives — there is at least
one (`Babai.cosetRepList_ne_nil`) — and each of its instances is expanded by the Chain Rule
over the orbits of `ker ϕ*` inside the window, which is nonempty for the same reason. -/
theorem AlignDominantRoundData.calls_round_ne_nil (D : AlignDominantRoundData W)
    (hw : (D.toAlignDominant.window).Nonempty) (I : SIInstance W A) :
    (D.round (A := A) I).calls ≠ [] := by
  classical
  obtain ⟨u, hu⟩ := hw
  rw [AlignDominantRoundData.round]
  by_cases h : D.LargeParam
  · rw [if_pos h]
    have hmem : (orbit D.toAlignDominant.Gs u : Set W) ∈
        orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window :=
      mem_orbitListDomFirst.2 (orbit_mem_orbitListOn D.isInvariant_window hu)
    obtain ⟨Δ, Δs, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
    rw [hl]
    exact calls_chainReduction_ne_nil _ _ _ _ _ _ _
  · rw [if_neg h]
    refine SIReduction.calls_expand_ne_nil (fun J => ?_) ?_
    · have hmem : (orbit D.ker u : Set W) ∈
          orbitListOn D.ker D.toAlignDominant.window :=
        orbit_mem_orbitListOn D.isInvariant_window_ker hu
      obtain ⟨Δ, Δs, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
      rw [chainOverOrbitsOn, hl]
      exact calls_chainReduction_ne_nil _ _ _ _ _ _ _
    · have hlen := calls_length_descentReduction D.ker D.toAlignDominant.window I.x I.y
        (cosetRepList D.ker D.toAlignDominant.Gs)
      have hpos : 0 < (cosetRepList D.ker D.toAlignDominant.Gs).length :=
        List.length_pos_of_ne_nil (cosetRepList_ne_nil _ _)
      exact List.ne_nil_of_length_pos (by omega)

variable {x y : W → A}

/-- **Regression, Finding 1 of the audit of Secs. 14–15.**  One round of Procedure Align
makes at least one call, as soon as some version `Y'` of `y` is carried to the fixed
version `X'` of `x` by an element of `G` — outside that case Eq. (70) says the piece of
`Iso_G(x,y)` belonging to `Y'` is empty, and there is nothing to compute.

The round of lines 7–11 on the window of line 6 is a hypothesis here: the same statement
for `Babai.AlignDominantRoundData.round` belongs with lines 5–7. -/
theorem AlignShape.calls_ne_nil (S : AlignShape W A G x y)
    (hne : S.head ∉ S.tail)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D)
    (hw : ∀ D, S.dom = some D → D.toAlignDominant.window.Nonempty)
    (Y' : Pt (SplitOutcomes (Fin S.m))) (hY' : Y' ∈ S.versions)
    (hσ : letI := S.act; ∃ σ : G, (S.ϕ σ) • S.X' = Y') : S.red.calls ≠ [] := by
  classical
  letI := S.act
  apply calls_cosetAlignExpand_ne_nil hne hinv ?_ ?_ hY' hσ
  · intro J hJ hΔ
    unfold AlignShape.dominantRound
    split
    · rfl
    · next D hD =>
        apply D.run_cosetRound _ (he D hD) J
        · obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
          exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩
        · rw [(hd D hD).2]; exact hΔ
  · intro J hJ hΔ
    unfold AlignShape.dominantRound
    split
    · simp
    · next D hD =>
        apply D.calls_cosetRound_ne_nil _ (he D hD) J _ (hw D hD)
        obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
        exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩

/-- A branch with no dominant color still has to query its first color window. -/
theorem AlignShape.calls_ne_nil_of_dom_none (S : AlignShape W A G x y)
    (hd : S.dom = none) (Y' : Pt (SplitOutcomes (Fin S.m))) (hY' : Y' ∈ S.versions)
    (hσ : letI := S.act; ∃ σ : G, (S.ϕ σ) • S.X' = Y') : S.red.calls ≠ [] := by
  classical
  letI := S.act
  have hf : (fun J : SIInstance W A =>
      if J.Δ = S.head then S.dominantRound J else SIReduction.call J SIReduction.done) =
      fun J => SIReduction.call J SIReduction.done := by
    funext J
    simp [AlignShape.dominantRound, hd]
  rw [AlignShape.red, cosetAlignExpand, hf, SIReduction.expand_call_done]
  obtain ⟨σ, hσ⟩ := hσ
  have hc : (alignTransporter S.ϕ S.X' Y').Nonempty := ⟨σ, σ.2, hσ⟩
  obtain ⟨J, hJ⟩ := List.exists_mem_of_ne_nil _
    (calls_cosetChain_cons_ne_nil x y S.head S.tail hc)
  exact List.ne_nil_of_mem (SIReduction.mem_calls_unionOver_of_mem _ hY' hJ)

/-- In the dominant case the coset round also has to make a recursive call. -/
theorem AlignShape.calls_ne_nil_of_dom_some {par cost : ℕ}
    (C : Line4cdData W A G x y par cost) (D : AlignDominantRoundData W)
    (hd : C.shape.dom = some D) (hw : D.toAlignDominant.window.Nonempty)
    (Y' : Pt (SplitOutcomes (Fin C.shape.m))) (hY' : Y' ∈ C.shape.versions)
    (hσ : letI := C.shape.act; ∃ σ : G, (C.shape.ϕ σ) • C.shape.X' = Y') :
    C.shape.red.calls ≠ [] :=
  C.shape.calls_ne_nil C.head_not_mem C.windows_invariant C.dom_spec C.domEnum_spec
    (fun D' hD' => by
      have he : D' = D := Option.some.inj (hD'.symm.trans hd)
      rw [he]
      exact hw) Y' hY' hσ

/-- Eq. (71): a comparable target version forces positive cost in the undominated case. -/
theorem Line4cdData.calls_length_pos {par cost : ℕ}
    (C : Line4cdData W A G x y par cost) (hd : C.shape.dom = none)
    (Y' : Pt (SplitOutcomes (Fin C.shape.m))) (hY' : Y' ∈ C.shape.versions)
    (hσ : letI := C.shape.act; ∃ σ : G, (C.shape.ϕ σ) • C.shape.X' = Y') :
    0 < cost :=
  (List.length_pos_of_ne_nil (C.shape.calls_ne_nil_of_dom_none hd Y' hY' hσ)).trans_le
    C.calls_length

end Regression

end Shape

/-! ### The lift of the branch to `Ω` -/

section Lift

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} [Fintype Δ]

namespace Line4cdCore

variable {hinv : IsInvariant K Δ} {x₀ : Ω → A} {par cost : ℕ}
  (C : Line4cdCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x₀) (restrictStr Δ x₀) par cost)

/-- The lift of the branch to `Ω`. -/
noncomputable def lift (y₀ : Ω → A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  liftWindow K Δ hinv y₀ C.red

end Line4cdCore

/-- §15, lines 4c–4d: **the branch on the window, read on `Ω`, is correct**. -/
theorem run_liftWindow_core {hinv : IsInvariant K Δ} {x y : Ω → A} {par cost : ℕ}
    (C : Line4cdCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (I : SIInstance Ω A) (hK : I.K = (K : Set (Equiv.Perm Ω))) (hΔ : I.Δ = Δ)
    (hx : I.x = x) (hy : I.y = y) :
    (liftWindow K Δ hinv x C.red).run = I.answer := by
  rw [run_liftWindow hinv x y C.red C.calls_K C.run_red, SIInstance.answer, hK, hΔ, hx, hy]

/-- §15, lines 4c–4d: **the calls of the lifted branch are group instances**. -/
theorem calls_liftWindow_core_group {hinv : IsInvariant K Δ} {x y : Ω → A} {par cost : ℕ}
    (C : Line4cdCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (x₀ : Ω → A) : ∀ J ∈ (liftWindow K Δ hinv x₀ C.red).calls, IsGroupInstance J :=
  calls_liftWindow_isGroupInstance hinv x₀ C.red C.calls_K C.calls_group

/-- §15, lines 4c–4d: **the number of calls of the lifted branch** is the number of calls of
the branch on the window. -/
theorem calls_length_liftWindow_core {hinv : IsInvariant K Δ} {x y : Ω → A} {par cost : ℕ}
    (C : Line4cdCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (x₀ : Ω → A) : ((liftWindow K Δ hinv x₀ C.red).calls).length ≤ cost := by
  rw [calls_length_liftWindow hinv x₀ C.red C.calls_K]
  exact C.calls_length

/-- The window of a call of the lifted branch lies inside `Δ`, so it has at most as many
points. -/
theorem windowSize_le_of_calls_liftWindow {hinv : IsInvariant K Δ} (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ hinv : Set (Equiv.Perm Δ)))
    (hfin : Δ.Finite) :
    ∀ J ∈ (liftWindow K Δ hinv x₀ R).calls, J.windowSize ≤ Δ.ncard := by
  intro J hJ
  rw [calls_liftWindow hinv x₀ R hK, List.mem_map] at hJ
  obtain ⟨J', -, rfl⟩ := hJ
  show (Subtype.val '' J'.Δ).ncard ≤ Δ.ncard
  exact Set.ncard_le_ncard (by rintro _ ⟨w, -, rfl⟩; exact w.2) hfin

/-- §15, lines 4c–4d, **the progress**: every call of the lifted branch either has a window
of at most `4n/5` points, or is recognized as a lifted hinted call, and then its Johnson
parameter is at most `par/2` by Eq. (73). -/
theorem decreases_liftWindow_core {hinv : IsInvariant K Δ} {x y : Ω → A} {par cost : ℕ}
    (C : Line4cdCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (x₀ : Ω → A) (hcard : Fintype.card Δ = Δ.ncard) :
    ∀ J ∈ (liftWindow K Δ hinv x₀ C.red).calls,
      5 * J.windowSize ≤ 4 * Δ.ncard ∨
        (J.windowSize ≤ Δ.ncard ∧
          2 * param (⟨J, windowHintLift hinv x₀ C.hint J⟩ : HintedInstance Ω A) ≤ par) := by
  intro J hJ
  have hsize : J.windowSize ≤ Δ.ncard :=
    windowSize_le_of_calls_liftWindow x₀ C.red C.calls_K (Set.toFinite _) J hJ
  have hJ' := hJ
  rw [calls_liftWindow hinv x₀ C.red C.calls_K, List.mem_map] at hJ'
  obtain ⟨J', hJ'mem, rfl⟩ := hJ'
  rcases C.calls_progress J' hJ'mem with hsmall | hhint
  · refine Or.inl ?_
    rw [windowSize_windowInstance hinv x₀ J']
    rw [← hcard]
    exact hsmall
  · refine Or.inr ⟨hsize, ?_⟩
    have hrec : LiftedHint K Δ hinv x₀ C.hint (windowInstance K Δ hinv x₀ J') :=
      ⟨J', rfl, hhint, fun d hd => (C.hint_le J' d hd).1⟩
    obtain ⟨J'', d, hd, hpar⟩ := param_windowHintLift hinv x₀ hrec
    rw [hpar]
    exact (C.hint_le J'' d hd).2

end Lift

end Babai
