/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 13–15, lines 5–7 of the Master Algorithm: the round does not depend on the names of
the letters.
-/
import Workspace.Master.Line567a

/-!
# Renaming the letters of lines 5–7

The paper's String Isomorphism problem compares letters only for equality: `Iso_K(x,y)` is
`{τ ∈ K | x^τ = y}` (Eq. (56)), and every object of Sections 13–14 that the round of lines
5–7 reads is built from such sets (the stages `H(W) = Aut^W_{G_T}(x)` of Procedure
LocalCertificates, the certificates `K(T)`, the fullness of a test set, `F(x)`, `F(x)^Γ`,
`D(x)`, the comparison sets of Prop. 13.1.11, the local guide).  So a renaming `r` of the
letters that is injective on the letters used changes none of them, and the round of lines
5–7 on the renamed strings is the round on the original strings with the letters of every
call renamed.

This file proves that, for the reduction `Babai.Line57Shape.red` of `Babai.Line57Data` and
for every piece it is built from.

* `Babai.SIReduction.mapLetters r R` is the reduction `R` with every call renamed by `r`
  (the continuations are unchanged).  With `r` injective on the letters of the calls
  (`Babai.SIReduction.AllLettersIn`), its value is the value of `R`
  (`Babai.SIReduction.run_mapLetters`) and its calls are the renamed calls of `R`
  (`Babai.SIReduction.calls_mapLetters`).
* The invariance of the objects of Sec. 13 (`Babai.stages_rename`, `Babai.haltIndex_rename`,
  `Babai.certK_rename`, `Babai.bigFGamma_rename`, `Babai.fixedGamma_rename`,
  `Babai.compareIso_rename`, `Babai.pairedQ_rename`, `Babai.guideClassMissing_rename`).
* The equality of trees, piece by piece: `Babai.aggregateRoundStrong_rename` (Procedure
  AggregateCertificates), `Babai.AlignShape.red_rename` (Procedure Align),
  `Babai.Line57Shape.red_rename` (the whole round).
* `Babai.Line57Data.rename`: the data of lines 5–7 on `x, y` give the data on `r ∘ x, r ∘ y`,
  with the renamed reduction (`Babai.Line57Data.red_rename`), and
  `Babai.Line57Data.exists_rename` states it for any strings `x', y'` with `x' = r ∘ x`,
  `y' = r ∘ y` pointwise.

No letter is compared other than for equality anywhere in these definitions: the letter type
of `Babai.Line57Shape` is an arbitrary type with no structure.
-/

universe u v w

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

/-! ### Renaming the letters of an instance and of a reduction -/

section Generic

variable {Ω : Type u} {A : Type*} {B : Type*}

/-- An instance with its letters renamed by `r`; the candidate set and the window are
unchanged. -/
def SIInstance.mapLetters (r : A → B) (I : SIInstance Ω A) : SIInstance Ω B :=
  ⟨I.K, I.Δ, r ∘ I.x, r ∘ I.y⟩

@[simp] theorem SIInstance.mapLetters_K (r : A → B) (I : SIInstance Ω A) :
    (I.mapLetters r).K = I.K := rfl
@[simp] theorem SIInstance.mapLetters_Δ (r : A → B) (I : SIInstance Ω A) :
    (I.mapLetters r).Δ = I.Δ := rfl
@[simp] theorem SIInstance.mapLetters_x (r : A → B) (I : SIInstance Ω A) :
    (I.mapLetters r).x = r ∘ I.x := rfl
@[simp] theorem SIInstance.mapLetters_y (r : A → B) (I : SIInstance Ω A) :
    (I.mapLetters r).y = r ∘ I.y := rfl

theorem SIInstance.windowSize_mapLetters (r : A → B) (I : SIInstance Ω A) :
    (I.mapLetters r).windowSize = I.windowSize := rfl

/-- The letters of the instance lie in `S`. -/
def SIInstance.LettersIn (S : Set A) (I : SIInstance Ω A) : Prop :=
  ∀ u, I.x u ∈ S ∧ I.y u ∈ S

/-- A reduction with every call renamed by `r`; the continuations are unchanged. -/
def SIReduction.mapLetters {α : Type*} (r : A → B) :
    SIReduction Ω A α → SIReduction Ω B α
  | .done a => .done a
  | .call I k => .call (I.mapLetters r) fun a => (k a).mapLetters r

/-- Every call of the reduction, on every branch, has its letters in `S`. -/
def SIReduction.AllLettersIn {α : Type*} (S : Set A) : SIReduction Ω A α → Prop
  | .done _ => True
  | .call I k => I.LettersIn S ∧ ∀ a, (k a).AllLettersIn S

namespace SIReduction

variable {α β : Type*} (r : A → B)

@[simp] theorem mapLetters_done (a : α) :
    (SIReduction.done (Ω := Ω) (A := A) a).mapLetters r = .done a := rfl

@[simp] theorem mapLetters_call (I : SIInstance Ω A) (k : Set (Perm Ω) → SIReduction Ω A α) :
    (SIReduction.call I k).mapLetters r = .call (I.mapLetters r) fun a => (k a).mapLetters r :=
  rfl

theorem mapLetters_bind (R : SIReduction Ω A β) (g : β → SIReduction Ω A α) :
    (R.bind g).mapLetters r = (R.mapLetters r).bind fun b => (g b).mapLetters r := by
  induction R with
  | done b => rfl
  | call I k ih =>
    change SIReduction.call _ _ = SIReduction.call _ _
    congr 1
    funext a
    exact ih a

theorem mapLetters_sequence (L : List (SIReduction Ω A β)) :
    (sequence L).mapLetters r = sequence (L.map (mapLetters r)) := by
  induction L with
  | nil => rfl
  | cons S rest ih =>
    rw [List.map_cons, sequence_cons, sequence_cons, mapLetters_bind]
    congr 1
    funext b
    rw [mapLetters_bind, ih]
    rfl

theorem mapLetters_expand (f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω)))
    (f' : SIInstance Ω B → SIReduction Ω B (Set (Perm Ω)))
    (hf : ∀ I, f' (I.mapLetters r) = (f I).mapLetters r) :
    ∀ R : SIReduction Ω A α, (R.expand f).mapLetters r = (R.mapLetters r).expand f' := by
  intro R
  induction R with
  | done a => rfl
  | call I k ih =>
    change ((f I).bind fun ans => (k ans).expand f).mapLetters r =
      (f' (I.mapLetters r)).bind fun ans => ((k ans).mapLetters r).expand f'
    rw [mapLetters_bind, hf]
    congr 1
    funext a
    exact ih a

theorem mapLetters_unionOver {𝒴 : Type*} (b : 𝒴 → SIReduction Ω A (Set (Perm Ω))) :
    ∀ L : List 𝒴, (unionOver L b).mapLetters r = unionOver L fun Y => (b Y).mapLetters r := by
  intro L
  induction L with
  | nil => rfl
  | cons Y rest ih =>
    change ((b Y).bind fun S => (unionOver rest b).bind fun S' => .done (S ∪ S')).mapLetters r =
      ((b Y).mapLetters r).bind fun S =>
        (unionOver rest fun Y => (b Y).mapLetters r).bind fun S' => .done (S ∪ S')
    rw [mapLetters_bind]
    congr 1
    funext S
    rw [mapLetters_bind, ih]
    rfl

theorem allLettersIn_bind {S : Set A} {R : SIReduction Ω A β} {g : β → SIReduction Ω A α}
    (hR : R.AllLettersIn S) (hg : ∀ b, (g b).AllLettersIn S) : (R.bind g).AllLettersIn S := by
  induction R with
  | done b => exact hg b
  | call I k ih => exact ⟨hR.1, fun a => ih a (hR.2 a)⟩

theorem allLettersIn_sequence {S : Set A} {L : List (SIReduction Ω A β)}
    (h : ∀ R ∈ L, R.AllLettersIn S) : (sequence L).AllLettersIn S := by
  induction L with
  | nil => trivial
  | cons R rest ih =>
    rw [sequence_cons]
    exact allLettersIn_bind (h R List.mem_cons_self) fun _ =>
      allLettersIn_bind (ih fun R' hR' => h R' (List.mem_cons_of_mem _ hR')) fun _ => trivial

theorem allLettersIn_expand {S : Set A} {f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}
    (hf : ∀ I, I.LettersIn S → (f I).AllLettersIn S) :
    ∀ {R : SIReduction Ω A α}, R.AllLettersIn S → (R.expand f).AllLettersIn S := by
  intro R hR
  induction R with
  | done a => trivial
  | call I k ih => exact allLettersIn_bind (hf I hR.1) fun a => ih a (hR.2 a)

theorem allLettersIn_unionOver {S : Set A} {𝒴 : Type*} {b : 𝒴 → SIReduction Ω A (Set (Perm Ω))}
    (hb : ∀ Y, (b Y).AllLettersIn S) : ∀ L : List 𝒴, (unionOver L b).AllLettersIn S := by
  intro L
  induction L with
  | nil => trivial
  | cons Y rest ih =>
    exact allLettersIn_bind (hb Y) fun _ => allLettersIn_bind ih fun _ => trivial

end SIReduction

end Generic

/-! ### A renaming injective on the letters used changes no set of isomorphisms -/

section Iso

variable {Ω : Type u} {A : Type*} {B : Type*} {r : A → B} {S : Set A}

theorem strAct_comp (r : A → B) (x : Ω → A) (τ : Perm Ω) :
    strAct (r ∘ x) τ = r ∘ strAct x τ := rfl

/-- A renaming of the letters injective on the letters used changes no `Iso^Δ_K`. -/
theorem wIso_rename (hr : Set.InjOn r S) {x y : Ω → A} (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (Δ : Set Ω) (K : Set (Perm Ω)) :
    wIso Δ K (r ∘ x) (r ∘ y) = wIso Δ K x y := by
  ext τ
  simp only [wIso, Set.mem_setOf_eq, Function.comp]
  refine and_congr_right fun _ => forall₂_congr fun u _ => ⟨fun h => ?_, fun h => by rw [h]⟩
  exact hr (hx _) (hy _) h

/-- A renaming of the letters injective on the letters used changes no `Iso_K`. -/
theorem strIso_rename (hr : Set.InjOn r S) {x y : Ω → A} (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (K : Set (Perm Ω)) :
    strIso K (r ∘ x) (r ∘ y) = strIso K x y := by
  ext τ
  simp only [strIso, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h => funext fun u => ?_, fun h => ?_⟩
  · exact hr (hx _) (hy _) (congrFun h u)
  · rw [strAct_comp, h]

theorem SIInstance.answer_mapLetters (hr : Set.InjOn r S) {I : SIInstance Ω A}
    (hI : I.LettersIn S) : (I.mapLetters r).answer = I.answer :=
  wIso_rename hr (fun u => (hI u).1) (fun u => (hI u).2) I.Δ I.K

namespace SIReduction

variable {α : Type*}

/-- **The renamed reduction has the same value**, when the renaming is injective on the
letters of its calls. -/
theorem run_mapLetters (hr : Set.InjOn r S) :
    ∀ {R : SIReduction Ω A α}, R.AllLettersIn S → (R.mapLetters r).run = R.run := by
  intro R hR
  induction R with
  | done a => rfl
  | call I k ih =>
    change ((k (I.mapLetters r).answer).mapLetters r).run = (k I.answer).run
    rw [SIInstance.answer_mapLetters hr hR.1]
    exact ih _ (hR.2 _)

/-- **The calls of the renamed reduction are the renamed calls**, when the renaming is
injective on the letters of the calls. -/
theorem calls_mapLetters (hr : Set.InjOn r S) :
    ∀ {R : SIReduction Ω A α}, R.AllLettersIn S →
      (R.mapLetters r).calls = R.calls.map (SIInstance.mapLetters r) := by
  intro R hR
  induction R with
  | done a => rfl
  | call I k ih =>
    change I.mapLetters r :: ((k (I.mapLetters r).answer).mapLetters r).calls =
      I.mapLetters r :: (k I.answer).calls.map _
    rw [SIInstance.answer_mapLetters hr hR.1, ih _ (hR.2 _)]

theorem mem_calls_allLettersIn {S : Set A} :
    ∀ {R : SIReduction Ω A α}, R.AllLettersIn S → ∀ I ∈ R.calls, I.LettersIn S := by
  intro R hR
  induction R with
  | done a => intro I hI; simp at hI
  | call J k ih =>
    intro I hI
    rcases List.mem_cons.1 hI with rfl | hI
    · exact hR.1
    · exact ih _ (hR.2 _) I hI

end SIReduction

theorem wAutSubgroup_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (H : Subgroup (Perm Ω)) (Δ : Set Ω) (h : IsInvariant H Δ) :
    wAutSubgroup H Δ h (r ∘ x) = wAutSubgroup H Δ h x := by
  ext σ
  change σ ∈ wAut Δ (H : Set (Perm Ω)) (r ∘ x) ↔ σ ∈ wAut Δ (H : Set (Perm Ω)) x
  rw [wAut, wAut, wIso_rename hr hx hx]

end Iso

/-! ### Section 13.1: the stages of Procedure LocalCertificates do not see the renaming -/

section Stages

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {A : Type*} {B : Type*} {r : A → B} {S : Set A}

/-- A stage of the while loop of Procedure LocalCertificates for `x` is a stage for `r ∘ x`,
with the same window and group: `Aut^W_{G_T}(r ∘ x) = Aut^W_{G_T}(x)`. -/
def Stage.rename {ϕ : G →* Perm Γ} {x : Ω → A} {T : Set Γ} (hr : Set.InjOn r S)
    (hx : ∀ u, x u ∈ S) (s : Stage ϕ x T) : Stage ϕ (r ∘ x) T where
  W := s.W
  H := s.H
  le := s.le
  isAut := by rw [s.isAut, wAut, wAut, wIso_rename hr hx hx]
  inv := s.inv
  sub := s.sub

theorem Stage.ext_WH {ϕ : G →* Perm Γ} {x : Ω → A} {T : Set Γ} {s s' : Stage ϕ x T}
    (hW : s.W = s'.W) (hH : s.H = s'.H) : s = s' := by
  cases s
  cases s'
  simp only at hW hH
  subst hW hH
  rfl

variable (ϕ : G →* Perm Γ) (T : Set Γ)

/-- §13.1: **the stages of the while loop for `r ∘ x` are those for `x`**. -/
theorem stages_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    ∀ i, stages ϕ (r ∘ x) T i = (stages ϕ x T i).rename hr hx := by
  intro i
  induction i with
  | zero => exact Stage.ext_WH rfl rfl
  | succ i ih =>
    rw [stages_succ, stages_succ, ih]
    refine Stage.ext_WH rfl ?_
    exact wAutSubgroup_rename hr hx _ _ (stages ϕ x T i).isInvariant_aff

theorem loopCond_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) (i : ℕ) :
    (stages ϕ (r ∘ x) T i).LoopCond ↔ (stages ϕ x T i).LoopCond := by
  rw [stages_rename ϕ T hr hx]
  rfl

theorem haltIndex_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    haltIndex ϕ (r ∘ x) T = haltIndex ϕ x T := by
  apply le_antisymm
  · exact Nat.find_le (by rw [loopCond_rename ϕ T hr hx]; exact not_loopCond_outStage ϕ x T)
  · exact Nat.find_le (by
      rw [← loopCond_rename ϕ T hr hx]; exact not_loopCond_outStage ϕ (r ∘ x) T)

theorem outStage_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    outStage ϕ (r ∘ x) T = (outStage ϕ x T).rename hr hx := by
  rw [outStage, haltIndex_rename ϕ T hr hx, stages_rename ϕ T hr hx]
  rfl

theorem windowOut_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    windowOut ϕ (r ∘ x) T = windowOut ϕ x T := by
  rw [windowOut, outStage_rename ϕ T hr hx]
  rfl

theorem certK_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    certK ϕ (r ∘ x) T = certK ϕ x T := by
  rw [certK, windowOut_rename ϕ T hr hx, outStage_rename ϕ T hr hx]
  rfl

theorem kerN_stages_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) (i : ℕ) :
    kerN (stages ϕ (r ∘ x) T i) = kerN (stages ϕ x T i) := by
  rw [stages_rename ϕ T hr hx]
  rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem autG_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    autG G (r ∘ x) = autG G x :=
  wAutSubgroup_rename hr hx _ _ _

theorem imgOn_congr_sub {L L' : Subgroup (Perm Ω)} (e : L = L') (A : Set Γ)
    (h : L ≤ stabIn ϕ (le_refl G) A) (h' : L' ≤ stabIn ϕ (le_refl G) A) :
    imgOn ϕ A h = imgOn ϕ A h' := by
  subst e
  rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ] in
theorem stabIn_congr_sub {L L' : Subgroup (Perm Ω)} (e : L = L') (h : L ≤ G) (h' : L' ≤ G)
    (A : Set Γ) : stabIn ϕ h A = stabIn ϕ h' A := by
  subst e
  rfl

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ] in
theorem imgPhi_congr_sub {L L' : Subgroup (Perm Ω)} (e : L = L') (h : L ≤ G) (h' : L' ≤ G) :
    imgPhi ϕ h = imgPhi ϕ h' := by
  subst e
  rfl

/-- Definition 13.1.2: fullness of a test set does not see the renaming. -/
theorem isFull_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    IsFull ϕ (r ∘ x) T ↔ IsFull ϕ x T := by
  unfold IsFull
  rw [imgOn_congr_sub ϕ (stabIn_congr_sub ϕ (autG_rename hr hx) _ (autG_le G x) T) T _
    (autStab_le ϕ x T)]

theorem fullSets_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) (t : ℕ) :
    fullSets ϕ (r ∘ x) t = fullSets ϕ x t := by
  ext T
  simp only [fullSets, Set.mem_setOf_eq, isFull_rename ϕ T hr hx]

variable (t : ℕ)

/-- §13.2: `F(r ∘ x) = F(x)`. -/
theorem bigF_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    bigF ϕ (r ∘ x) t = bigF ϕ x t := by
  simp only [bigF, fullSets_rename ϕ hr hx, certK_rename ϕ _ hr hx]

/-- §13.2: `F(r ∘ x)^Γ = F(x)^Γ`. -/
theorem bigFGamma_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    bigFGamma ϕ (r ∘ x) t = bigFGamma ϕ x t :=
  imgPhi_congr_sub ϕ (bigF_rename ϕ t hr hx) _ _

/-- §13.2, case (3): `D(r ∘ x) = D(x)`. -/
theorem fixedGamma_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    fixedGamma ϕ (r ∘ x) t = fixedGamma ϕ x t := by
  simp only [fixedGamma, bigFGamma_rename ϕ t hr hx]

theorem aggregateCase2a_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) :
    AggregateCase2a ϕ (r ∘ x) t ↔ AggregateCase2a ϕ x t := by
  have key : ∀ {H H' : Subgroup (Perm Γ)}, H = H' →
      ((∃ γ : Γ, 4 * Fintype.card Γ < 5 * (orbit H γ : Set Γ).ncard ∧
        alternatingGroup ((orbit H γ : Set Γ)) ≤ restrictTo H _ (isInvariant_orbit H γ)) ↔
      (∃ γ : Γ, 4 * Fintype.card Γ < 5 * (orbit H' γ : Set Γ).ncard ∧
        alternatingGroup ((orbit H' γ : Set Γ)) ≤ restrictTo H' _ (isInvariant_orbit H' γ))) := by
    rintro H H' rfl
    rfl
  exact key (bigFGamma_rename ϕ t hr hx)

end Stages

/-! ### Prop. 13.1.11 and the local guide of Sec. 13.2 do not see the renaming -/

section Compare

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {A : Type*} {B : Type*} {r : A → B} {S : Set A}

/-- The renaming of the letters of a truncated, colored string (Notation 13.1.10). -/
def optRename (r : A → B) : Option (A × Bool) → Option (B × Bool) :=
  Option.map (Prod.map r id)

theorem injOn_optRename (hr : Set.InjOn r S) :
    Set.InjOn (optRename r) {o | ∀ p ∈ o, p.1 ∈ S} := by
  rintro (_ | ⟨a, b⟩) ho (_ | ⟨a', b'⟩) ho' h
  · rfl
  · simp [optRename] at h
  · simp [optRename] at h
  · simp only [optRename, Option.map_some, Option.some.injEq, Prod.map, Prod.mk.injEq,
      id] at h
    have ha : a ∈ S := ho (a, b) rfl
    have ha' : a' ∈ S := ho' (a', b') rfl
    rw [hr ha ha' h.1, h.2]

variable (ϕ : G →* Perm Γ)

theorem truncate_colorByFace_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (T : Set Γ) :
    truncate (colorByFace ϕ (r ∘ x) T) (windowOut ϕ (r ∘ x) T) =
      optRename r ∘ truncate (colorByFace ϕ x T) (windowOut ϕ x T) := by
  funext u
  rw [windowOut_rename ϕ T hr hx]
  simp only [truncate, colorByFace, Function.comp]
  split <;> rfl

theorem truncate_colorByFace_mem {x : Ω → A} (hx : ∀ u, x u ∈ S) (T : Set Γ) (u : Ω) :
    truncate (colorByFace ϕ x T) (windowOut ϕ x T) u ∈ {o : Option (A × Bool) | ∀ p ∈ o, p.1 ∈ S} := by
  intro p hp
  simp only [truncate, colorByFace] at hp
  split at hp
  · rw [Option.mem_def, Option.some.injEq] at hp
    rw [← hp]
    exact hx u
  · simp at hp

/-- Prop. 13.1.11: the comparison set `Iso_G(x_T^{W(T)}, (x')_{T'}^{W'(T')})` does not see the
renaming. -/
theorem compareIso_rename (hr : Set.InjOn r S) {x x' : Ω → A} (hx : ∀ u, x u ∈ S)
    (hx' : ∀ u, x' u ∈ S) (T T' : Set Γ) :
    compareIso ϕ (r ∘ x) (r ∘ x') T T' = compareIso ϕ x x' T T' := by
  rw [compareIso, compareIso, truncate_colorByFace_rename ϕ hr hx,
    truncate_colorByFace_rename ϕ hr hx']
  exact strIso_rename (injOn_optRename hr) (truncate_colorByFace_mem ϕ hx T)
    (truncate_colorByFace_mem ϕ hx' T') _

/-- The set `Q` of the paired loop does not see the renaming. -/
theorem pairedQ_rename (hr : Set.InjOn r S) {x y : Ω → A} (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (T : Set Γ) (σ₀ : Perm Ω) (i : ℕ) :
    pairedQ ϕ (r ∘ x) (r ∘ y) T σ₀ i = pairedQ ϕ x y T σ₀ i := by
  rw [pairedQ, pairedQ, stages_rename ϕ T hr hx]
  exact wIso_rename hr hx hy _ _

end Compare

section Guide

variable {W : Type u} [Fintype W] [DecidableEq W] {A : Type v} {B : Type*} {r : A → B}
  {S : Set A} {G : Subgroup (Perm W)} {m : ℕ} (ϕ : G →* Perm (Fin m)) (ts : ℕ)

/-- The relation `∼` of the local guide between a tuple of `D(x)` and a tuple of `D(y)`,
read on `Γ`: some `σ ∈ G` in the comparison set of their underlying test sets maps the one
onto the other. -/
def GuideRel (x y : W → A) (a b : Fin ts → Fin m) : Prop :=
  ∃ σ : G, (σ : Perm W) ∈ compareIso ϕ x y (Set.range a) (Set.range b) ∧
    ∀ i, (ϕ σ : Perm (Fin m)) (a i) = b i

theorem mkClass_eq_iff_guideRel {x y : W → A} (hset : LocalCertSetting G ϕ)
    (ht : LargeK ts (Nat.card W)) (htm : 10 * ts ≤ Nat.card (Fin m)) [Nonempty W]
    (u : Fin ts ↪ ↥(fixedGamma ϕ x ts)) (v : Fin ts ↪ ↥(fixedGamma ϕ y ts)) :
    (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass ⟨false, u⟩ =
        (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass ⟨true, v⟩ ↔
      GuideRel ϕ ts x y (fun i => (u i : Fin m)) (fun i => (v i : Fin m)) := by
  rw [LocalGuideData.mkClass_eq_iff]
  have hru : (Subtype.val '' Set.range (u : Fin ts → ↥(fixedGamma ϕ x ts))) =
      Set.range (fun i => (u i : Fin m)) := by
    ext γ; simp
  have hrv : (Subtype.val '' Set.range (v : Fin ts → ↥(fixedGamma ϕ y ts))) =
      Set.range (fun i => (v i : Fin m)) := by
    ext γ; simp
  constructor
  · rintro ⟨α, ⟨σ, hσ, hα⟩, hαt⟩
    refine ⟨σ, ?_, fun i => ?_⟩
    · change (σ : Perm W) ∈ compareIso ϕ x y (Subtype.val '' Set.range u)
        (Subtype.val '' Set.range v) at hσ
      rwa [hru, hrv] at hσ
    · exact (hα ⟨u i, ⟨i, rfl⟩⟩).symm.trans (congrArg Subtype.val (hαt i))
  · rintro ⟨σ, hσ, hσt⟩
    have key : ∀ i, ((Equiv.ofInjective _ u.injective).symm.trans
        (Equiv.ofInjective _ v.injective)) ⟨u i, ⟨i, rfl⟩⟩ = ⟨v i, ⟨i, rfl⟩⟩ := by
      intro i
      rw [Equiv.trans_apply, Equiv.ofInjective_symm_apply]
      rfl
    refine ⟨(Equiv.ofInjective _ u.injective).symm.trans (Equiv.ofInjective _ v.injective),
      ⟨σ, ?_, fun a => ?_⟩, fun i => ?_⟩
    · change (σ : Perm W) ∈ compareIso ϕ x y (Subtype.val '' Set.range u)
        (Subtype.val '' Set.range v)
      rwa [hru, hrv]
    · obtain ⟨_, i, rfl⟩ := a
      exact (congrArg (fun z : ↥(Set.range v) => ((z : ↥(fixedGamma ϕ y ts)) : Fin m))
        (key i)).trans (hσt i).symm
    · exact congrArg Subtype.val (key i)

theorem guideRel_rename (hr : Set.InjOn r S) {x y : W → A} (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (a b : Fin ts → Fin m) :
    GuideRel ϕ ts (r ∘ x) (r ∘ y) a b ↔ GuideRel ϕ ts x y a b := by
  have h := compareIso_rename ϕ hr hx hy (Set.range a) (Set.range b)
  constructor
  · rintro ⟨σ, h1, h2⟩
    exact ⟨σ, h ▸ h1, h2⟩
  · rintro ⟨σ, h1, h2⟩
    exact ⟨σ, h.symm ▸ h1, h2⟩

/-- §13.2, case (3): **the missing guide class does not see the renaming** (entry 121). -/
theorem val_setCongr {α : Type*} {s t : Set α} (h : s = t) (a : s) :
    ((Equiv.setCongr h a : t) : α) = a := by
  subst h
  rfl

/-- §13.2, case (3): **the missing guide class does not see the renaming** (entry 121). -/
theorem guideClassMissing_rename (hr : Set.InjOn r S) {x y : W → A} (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ Nat.card (Fin m)) (hW : Nonempty W)
    (h : GuideClassMissing ϕ ts x y hset ht htm hW) :
    GuideClassMissing ϕ ts (r ∘ x) (r ∘ y) hset ht htm hW := by
  obtain ⟨v, hv⟩ := h
  have hfx := fixedGamma_rename ϕ ts hr hx
  have hfy := fixedGamma_rename ϕ ts hr hy
  refine ⟨v.trans (Equiv.setCongr hfy.symm).toEmbedding, fun u' => ?_⟩
  have hu := hv (u'.trans (Equiv.setCongr hfx).toEmbedding)
  rw [Ne, mkClass_eq_iff_guideRel] at hu ⊢
  have eu : (fun i => (((u'.trans (Equiv.setCongr hfx).toEmbedding) i :
      ↥(fixedGamma ϕ x ts)) : Fin m)) = fun i => (u' i : Fin m) := by
    funext i
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, val_setCongr]
  have ev : (fun i => (((v.trans (Equiv.setCongr hfy.symm).toEmbedding) i :
      ↥(fixedGamma ϕ (r ∘ y) ts)) : Fin m)) = fun i => (v i : Fin m) := by
    funext i
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, val_setCongr]
  rw [eu] at hu
  rw [ev, guideRel_rename ϕ ts hr hx hy]
  exact hu
end Guide

/-! ### The trees of Sections 11 and 13 with renamed letters -/

section Trees

variable {Ω : Type*} {A : Type*} {B : Type*} {r : A → B} {S : Set A}

open SIReduction in
/-- §11.1, Eq. (63) iterated: the Chain Rule on renamed strings is the renamed Chain Rule. -/
theorem cosetChain_rename (r : A → B) (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)),
      cosetChain (r ∘ x) (r ∘ y) Δs C = (cosetChain x y Δs C).mapLetters r := by
  intro Δs
  induction Δs with
  | nil => intro C; rfl
  | cons Δ rest ih =>
    intro C
    rw [cosetChain, cosetChain]
    split
    · rfl
    · rw [mapLetters_call]
      congr 1
      funext a
      exact ih a

theorem allLettersIn_cosetChain {x y : Ω → A} (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)), (cosetChain x y Δs C).AllLettersIn S := by
  intro Δs
  induction Δs with
  | nil => intro C; trivial
  | cons Δ rest ih =>
    intro C
    rw [cosetChain]
    split
    · trivial
    · exact ⟨fun u => ⟨hx u, hy u⟩, fun a => ih a⟩

theorem unionAnswers_rename (r : A → B) :
    ∀ L : List (SIReduction Ω A (Set (Perm Ω))),
      (unionAnswers L).mapLetters r = unionAnswers (L.map (SIReduction.mapLetters r)) := by
  intro L
  induction L with
  | nil => rfl
  | cons R rest ih =>
    rw [List.map_cons, unionAnswers, unionAnswers, SIReduction.mapLetters_bind]
    congr 1
    funext a
    rw [SIReduction.mapLetters_bind, ih]
    rfl

theorem allLettersIn_unionAnswers {L : List (SIReduction Ω A (Set (Perm Ω)))}
    (h : ∀ R ∈ L, R.AllLettersIn S) : (unionAnswers L).AllLettersIn S := by
  induction L with
  | nil => trivial
  | cons R rest ih =>
    rw [unionAnswers]
    exact SIReduction.allLettersIn_bind (h R List.mem_cons_self) fun _ =>
      SIReduction.allLettersIn_bind (ih fun R' hR' => h R' (List.mem_cons_of_mem _ hR'))
        fun _ => trivial

variable [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Sec. 11.1, strong descent, on renamed strings. -/
theorem strongDescent_rename (r : A → B) (N : Subgroup (Perm Ω)) (x y : Ω → A)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    strongDescent N (r ∘ x) (r ∘ y) L Δs = (strongDescent N x y L Δs).mapLetters r := by
  rw [strongDescent, strongDescent, unionAnswers_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro σ _
  exact cosetChain_rename r x y Δs _

omit [Fintype Ω] [DecidableEq Ω] in
theorem allLettersIn_strongDescent (N : Subgroup (Perm Ω)) {x y : Ω → A}
    (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S) (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    (strongDescent N x y L Δs).AllLettersIn S := by
  rw [strongDescent]
  apply allLettersIn_unionAnswers
  intro R hR
  obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hR
  exact allLettersIn_cosetChain hx hy _ _

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Perm Ω)}
  (ϕ : G →* Perm Γ) (T : Set Γ)

theorem recomputeStrong_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S) (i : ℕ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    recomputeStrong (stages ϕ (r ∘ x) T i) L Δs =
      (recomputeStrong (stages ϕ x T i) L Δs).mapLetters r := by
  rw [recomputeStrong, recomputeStrong, kerN_stages_rename ϕ T hr hx]
  exact strongDescent_rename r _ x x L Δs

/-- Sec. 13.1, lines 02–05, on renamed strings. -/
theorem loopStrong_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    ∀ i, loopStrong ϕ (r ∘ x) T L Δs i = (loopStrong ϕ x T L Δs i).mapLetters r := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [loopStrong, loopStrong, ih, SIReduction.mapLetters_bind]
    congr 1
    funext p
    rw [SIReduction.mapLetters_bind, recomputeStrong_rename ϕ T hr hx]
    rfl

theorem allLettersIn_loopStrong {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    ∀ i, (loopStrong ϕ x T L Δs i).AllLettersIn S := by
  intro i
  induction i with
  | zero => trivial
  | succ i ih =>
    rw [loopStrong]
    exact SIReduction.allLettersIn_bind ih fun _ => SIReduction.allLettersIn_bind
      (allLettersIn_strongDescent _ hx hx _ _) fun _ => trivial

/-- Sec. 13.1, Procedure LocalCertificates, on renamed strings. -/
theorem certRunStrong_rename (hr : Set.InjOn r S) {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    certRunStrong ϕ (r ∘ x) T L Δs = (certRunStrong ϕ x T L Δs).mapLetters r := by
  rw [certRunStrong, certRunStrong, localCertStrong, localCertStrong,
    haltIndex_rename ϕ T hr hx, loopStrong_rename ϕ T hr hx, SIReduction.mapLetters_bind,
    SIReduction.mapLetters_bind]
  rw [SIReduction.bind_assoc, SIReduction.bind_assoc]
  rfl

theorem allLettersIn_certRunStrong {x : Ω → A} (hx : ∀ u, x u ∈ S)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    (certRunStrong ϕ x T L Δs).AllLettersIn S :=
  SIReduction.allLettersIn_bind (SIReduction.allLettersIn_bind
    (allLettersIn_loopStrong ϕ T hx L Δs _) fun _ => trivial) fun _ => trivial

/-- Prop. 13.1.11, the paired loop, on renamed strings. -/
theorem pairedLoopStrong_rename (hr : Set.InjOn r S) {x y : Ω → A} (hx : ∀ u, x u ∈ S)
    (σ : Perm Ω) (E : StrongPairEnum Ω) :
    ∀ i, pairedLoopStrong ϕ (r ∘ x) (r ∘ y) T σ E i =
      (pairedLoopStrong ϕ x y T σ E i).mapLetters r := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pairedLoopStrong, pairedLoopStrong, ih, SIReduction.mapLetters_bind]
    congr 1
    funext p
    cases p with
    | none => rfl
    | some p =>
      simp only
      rw [SIReduction.mapLetters_bind, recomputeStrong_rename ϕ T hr hx]
      congr 1
      funext H
      rw [SIReduction.mapLetters_bind, kerN_stages_rename ϕ T hr hx, strongDescent_rename]
      rfl

theorem allLettersIn_pairedLoopStrong {x y : Ω → A} (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (σ : Perm Ω) (E : StrongPairEnum Ω) :
    ∀ i, (pairedLoopStrong ϕ x y T σ E i).AllLettersIn S := by
  intro i
  induction i with
  | zero => trivial
  | succ i ih =>
    rw [pairedLoopStrong]
    refine SIReduction.allLettersIn_bind ih fun p => ?_
    cases p with
    | none => trivial
    | some p =>
      exact SIReduction.allLettersIn_bind (allLettersIn_strongDescent _ hx hx _ _) fun _ =>
        SIReduction.allLettersIn_bind (allLettersIn_strongDescent _ hx hy _ _) fun _ => trivial

/-- Prop. 13.1.11 on renamed strings. -/
theorem compareStrong_rename (hr : Set.InjOn r S) {x y : Ω → A} (hx : ∀ u, x u ∈ S)
    (σ : Option (Perm Ω)) (E : StrongPairEnum Ω) :
    compareStrong ϕ (r ∘ x) T (r ∘ y) σ E = (compareStrong ϕ x T y σ E).mapLetters r := by
  cases σ with
  | none => rfl
  | some ρ =>
    change pairedComparisonStrong ϕ (r ∘ x) (r ∘ y) T ρ E =
      (pairedComparisonStrong ϕ x y T ρ E).mapLetters r
    rw [pairedComparisonStrong, pairedComparisonStrong, haltIndex_rename ϕ T hr hx,
      pairedLoopStrong_rename ϕ T hr hx, SIReduction.mapLetters_bind]
    rfl

theorem allLettersIn_compareStrong {x y : Ω → A} (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (σ : Option (Perm Ω)) (E : StrongPairEnum Ω) :
    (compareStrong ϕ x T y σ E).AllLettersIn S := by
  cases σ with
  | none => trivial
  | some ρ =>
    exact SIReduction.allLettersIn_bind (allLettersIn_pairedLoopStrong ϕ T hx hy ρ E _)
      fun _ => trivial

omit [Fintype Ω] [DecidableEq Ω] in
theorem cond_comp (r : A → B) (x y : Ω → A) (b : Bool) :
    cond b (r ∘ y) (r ∘ x) = r ∘ cond b y x := by
  cases b <;> rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem cond_mem {x y : Ω → A} (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S) (b : Bool) :
    ∀ u, cond b y x u ∈ S := by
  cases b
  · exact hx
  · exact hy

variable {x y : Ω → A}

/-- Sec. 13.2: the certificate phase on renamed strings. -/
theorem certPhaseStrong_rename (hr : Set.InjOn r S) (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (E : AggEnum Ω Γ) :
    certPhaseStrong ϕ (r ∘ x) (r ∘ y) E = (certPhaseStrong ϕ x y E).mapLetters r := by
  rw [certPhaseStrong, certPhaseStrong, SIReduction.mapLetters_sequence, certRunsStrong,
    certRunsStrong, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro b _
  rw [List.map_map]
  apply List.map_congr_left
  intro T _
  rw [cond_comp]
  exact certRunStrong_rename ϕ T hr (cond_mem hx hy b) _ _

/-- Sec. 13.2: the comparison phase on renamed strings. -/
theorem comparePhaseStrong_rename (hr : Set.InjOn r S) (hx : ∀ u, x u ∈ S)
    (E : AggEnum Ω Γ) :
    comparePhaseStrong ϕ (r ∘ x) (r ∘ y) E = (comparePhaseStrong ϕ x y E).mapLetters r := by
  rw [comparePhaseStrong, comparePhaseStrong, SIReduction.mapLetters_sequence,
    compareRunsStrong, compareRunsStrong, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro b _
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro T _
  rw [List.map_map]
  apply List.map_congr_left
  intro T' _
  rw [cond_comp]
  exact compareStrong_rename ϕ T hr hx _ _

theorem allLettersIn_certPhaseStrong (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (E : AggEnum Ω Γ) : (certPhaseStrong ϕ x y E).AllLettersIn S := by
  apply SIReduction.allLettersIn_sequence
  intro R hR
  obtain ⟨b, T, _, rfl⟩ := (mem_certRunsStrong E).1 hR
  exact allLettersIn_certRunStrong ϕ T (cond_mem hx hy b) _ _

theorem allLettersIn_comparePhaseStrong (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (E : AggEnum Ω Γ) : (comparePhaseStrong ϕ x y E).AllLettersIn S := by
  apply SIReduction.allLettersIn_sequence
  intro R hR
  obtain ⟨b, T, _, T', _, rfl⟩ := (mem_compareRunsStrong E).1 hR
  exact allLettersIn_compareStrong ϕ T hx (cond_mem hx hy b) _ _

/-- **Sec. 13.2, Procedure AggregateCertificates, on renamed strings**: the two phases and
the continuation, renamed. -/
theorem aggregateRoundStrong_rename (hr : Set.InjOn r S) (hx : ∀ u, x u ∈ S)
    (hy : ∀ u, y u ∈ S) (E : AggEnum Ω Γ) {α : Type*} (R : SIReduction Ω A α) :
    aggregateRoundStrong ϕ (r ∘ x) (r ∘ y) E (R.mapLetters r) =
      (aggregateRoundStrong ϕ x y E R).mapLetters r := by
  rw [aggregateRoundStrong, aggregateRoundStrong, certPhaseStrong_rename ϕ hr hx hy,
    comparePhaseStrong_rename ϕ hr hx, SIReduction.mapLetters_bind]
  congr 1
  funext _
  rw [SIReduction.mapLetters_bind]

theorem allLettersIn_aggregateRoundStrong (hx : ∀ u, x u ∈ S) (hy : ∀ u, y u ∈ S)
    (E : AggEnum Ω Γ) {α : Type*} {R : SIReduction Ω A α} (hR : R.AllLettersIn S) :
    (aggregateRoundStrong ϕ x y E R).AllLettersIn S :=
  SIReduction.allLettersIn_bind (allLettersIn_certPhaseStrong ϕ hx hy E) fun _ =>
    SIReduction.allLettersIn_bind (allLettersIn_comparePhaseStrong ϕ hx hy E) fun _ => hR

end Trees

/-! ### Procedure Align with renamed letters -/

section Align

variable {W : Type u} [Fintype W] [DecidableEq W] {A : Type v} {B : Type*}
  {r : A → B} {Sl : Set A}

omit [Fintype W] [DecidableEq W] in
/-- The coset rounds of Sec. 14.1 on renamed strings. -/
theorem cosetDesignAlign_rename {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳] {G : Subgroup (Perm W)}
    (ϕ : G →* Perm Γ) (x y : W → A) (X : 𝒳) (versions : List 𝒳) (windows : List (Set W)) :
    cosetDesignAlign ϕ (r ∘ x) (r ∘ y) X versions windows =
      (cosetDesignAlign ϕ x y X versions windows).mapLetters r := by
  rw [cosetDesignAlign, cosetDesignAlign, SIReduction.mapLetters_unionOver]
  congr 1
  funext Y
  exact cosetChain_rename r x y windows _

omit [Fintype W] [DecidableEq W] in
theorem allLettersIn_cosetDesignAlign {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳]
    {G : Subgroup (Perm W)} (ϕ : G →* Perm Γ) {x y : W → A} (hx : ∀ u, x u ∈ Sl)
    (hy : ∀ u, y u ∈ Sl) (X : 𝒳) (versions : List 𝒳) (windows : List (Set W)) :
    (cosetDesignAlign ϕ x y X versions windows).AllLettersIn Sl :=
  SIReduction.allLettersIn_unionOver (fun _ => allLettersIn_cosetChain hx hy _ _) _

omit [Fintype W] [DecidableEq W] in
/-- Sec. 14.1, lines 1–11: the expanded round on renamed strings, when the round of lines
7–11 commutes with the renaming. -/
theorem cosetAlignExpand_rename {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳] {G : Subgroup (Perm W)}
    (ϕ : G →* Perm Γ) (x y : W → A) (X : 𝒳) (versions : List 𝒳) (head : Set W)
    (tail : List (Set W)) (g : SIInstance W A → SIReduction W A (Set (Perm W)))
    (g' : SIInstance W B → SIReduction W B (Set (Perm W)))
    (hg : ∀ J, g' (J.mapLetters r) = (g J).mapLetters r) :
    cosetAlignExpand ϕ (r ∘ x) (r ∘ y) X versions head tail g' =
      (cosetAlignExpand ϕ x y X versions head tail g).mapLetters r := by
  rw [cosetAlignExpand, cosetAlignExpand, SIReduction.mapLetters_expand, cosetDesignAlign_rename]
  intro J
  change (if J.Δ = head then g' (J.mapLetters r) else .call (J.mapLetters r) .done) = _
  split
  · exact hg J
  · rfl

omit [Fintype W] [DecidableEq W] in
theorem allLettersIn_cosetAlignExpand {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳]
    {G : Subgroup (Perm W)} (ϕ : G →* Perm Γ) {x y : W → A} (hx : ∀ u, x u ∈ Sl)
    (hy : ∀ u, y u ∈ Sl) (X : 𝒳) (versions : List 𝒳) (head : Set W) (tail : List (Set W))
    {g : SIInstance W A → SIReduction W A (Set (Perm W))}
    (hg : ∀ J, J.LettersIn Sl → (g J).AllLettersIn Sl) :
    (cosetAlignExpand ϕ x y X versions head tail g).AllLettersIn Sl := by
  rw [cosetAlignExpand]
  refine SIReduction.allLettersIn_expand (fun J hJ => ?_)
    (allLettersIn_cosetDesignAlign ϕ hx hy X versions _)
  split
  · exact hg J hJ
  · exact ⟨hJ, fun _ => trivial⟩

namespace AlignDominantRoundData

variable (D : AlignDominantRoundData W) (E : AlignDominantEnum W)

/-- Sec. 14.1, lines 7–11, on a renamed call. -/
theorem cosetRound_mapLetters (J : SIInstance W A) :
    D.cosetRound E (J.mapLetters r) = (D.cosetRound E J).mapLetters r := by
  unfold cosetRound
  split
  · exact cosetChain_rename r J.x J.y _ _
  · exact strongDescent_rename r _ J.x J.y _ _

theorem allLettersIn_cosetRound {J : SIInstance W A} (hJ : J.LettersIn Sl) :
    (D.cosetRound E J).AllLettersIn Sl := by
  unfold cosetRound
  split
  · exact allLettersIn_cosetChain (fun u => (hJ u).1) (fun u => (hJ u).2) _ _
  · exact allLettersIn_strongDescent _ (fun u => (hJ u).1) (fun u => (hJ u).2) _ _

omit [Fintype W] [DecidableEq W] in
theorem instance_eq_self_iff {K : Set (Perm W)} {Δ : Set W} {I : SIInstance W A} :
    (⟨K, Δ, I.x, I.y⟩ : SIInstance W A) = I ↔ I.K = K ∧ I.Δ = Δ := by
  cases I
  simp only [SIInstance.mk.injEq, and_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩

/-- Line 11: whether a call carries the hint depends on its group and window alone. -/
theorem hasHint_self_mapLetters (I : SIInstance W A) :
    D.HasHint (I.mapLetters r) (I.mapLetters r) ↔ D.HasHint I I := by
  unfold HasHint
  simp only [instance_eq_self_iff, SIInstance.mapLetters_K, SIInstance.mapLetters_Δ]

theorem isSome_hint_iff {A' : Type*} (I J : SIInstance W A') :
    (D.hint I J).isSome ↔ D.HasHint I J := by
  unfold hint
  split
  · next h => simp [h]
  · next h => simp [h]

theorem hint_some {A' : Type*} {I J : SIInstance W A'} {d : JohnsonCaseData J}
    (h : D.hint I J = some d) : d.K = D.toAlignDominant.Gs ∧ d.m = D.toAlignDominant.ms := by
  unfold hint at h
  split at h
  · next hh =>
    cases h
    exact ⟨JohnsonCaseData.K_of_eqRec _ _, JohnsonCaseData.m_of_eqRec _ _⟩
  · cases h

end AlignDominantRoundData

namespace AlignShape

variable {G : Subgroup (Perm W)} {x y : W → A}

/-- **The data of one round of Procedure Align, for the renamed strings.** Everything the
round runs on is kept; the family of versions is read through the renaming (a version of a
renamed string is a version of the string it is renamed from). -/
noncomputable def rename (Sh : AlignShape W A G x y) (hr : Set.InjOn r Sl)
    (_hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl) : AlignShape W B G (r ∘ x) (r ∘ y) where
  m := Sh.m
  ϕ := Sh.ϕ
  act := Sh.act
  Vers := fun z => {X | ∃ z₀ : W → A, (∀ u, z₀ u ∈ Sl) ∧ r ∘ z₀ = z ∧ X ∈ Sh.Vers z₀}
  finY := by
    have he : {X | ∃ z₀ : W → A, (∀ u, z₀ u ∈ Sl) ∧ r ∘ z₀ = r ∘ y ∧ X ∈ Sh.Vers z₀} =
        Sh.Vers y := by
      ext X
      constructor
      · rintro ⟨z₀, hz, he, hX⟩
        have : z₀ = y := funext fun u => hr (hz u) (hy u) (congrFun he u)
        exact this ▸ hX
      · intro hX
        exact ⟨y, hy, rfl, hX⟩
    rw [he]
    exact Sh.finY
  X' := Sh.X'
  head := Sh.head
  tail := Sh.tail
  dom := Sh.dom
  versions := Sh.versions
  domEnum := Sh.domEnum

variable (Sh : AlignShape W A G x y) (hr : Set.InjOn r Sl) (hx : ∀ u, x u ∈ Sl)
  (hy : ∀ u, y u ∈ Sl)

theorem dominantRound_rename (J : SIInstance W A) :
    (Sh.rename hr hx hy).dominantRound (J.mapLetters r) = (Sh.dominantRound J).mapLetters r := by
  unfold dominantRound
  change (match Sh.dom with
    | none => SIReduction.call (J.mapLetters r) SIReduction.done
    | some D => D.cosetRound Sh.domEnum (J.mapLetters r)) = _
  rcases Sh.dom with _ | D
  · rfl
  · exact D.cosetRound_mapLetters _ J

theorem allLettersIn_dominantRound {J : SIInstance W A} (hJ : J.LettersIn Sl) :
    (Sh.dominantRound J).AllLettersIn Sl := by
  unfold dominantRound
  rcases Sh.dom with _ | D
  · exact ⟨hJ, fun _ => trivial⟩
  · exact D.allLettersIn_cosetRound _ hJ

/-- **Procedure Align on renamed strings is the renamed round.** -/
theorem red_rename : (Sh.rename hr hx hy).red = Sh.red.mapLetters r := by
  letI := Sh.act
  exact cosetAlignExpand_rename (r := r) Sh.ϕ x y Sh.X' Sh.versions Sh.head Sh.tail _ _
    (Sh.dominantRound_rename hr hx hy)

theorem allLettersIn_red (hx' : ∀ u, x u ∈ Sl) (hy' : ∀ u, y u ∈ Sl) :
    Sh.red.AllLettersIn Sl := by
  unfold red
  letI := Sh.act
  exact allLettersIn_cosetAlignExpand _ hx' hy' _ _ _ _
    fun J hJ => Sh.allLettersIn_dominantRound hJ

theorem hint_rename_isSome (J : SIInstance W A) :
    ((Sh.rename hr hx hy).hint (J.mapLetters r)).isSome = (Sh.hint J).isSome := by
  unfold hint
  change (match Sh.dom with
    | none => none
    | some D => D.hint (J.mapLetters r) (J.mapLetters r)).isSome = _
  rcases Sh.dom with _ | D
  · rfl
  · simp only
    rw [Bool.eq_iff_iff, D.isSome_hint_iff, D.isSome_hint_iff, D.hasHint_self_mapLetters]

/-- The hints of the renamed round have the group and the Johnson parameter of a hint of the
original round. -/
theorem hint_rename_some {J' : SIInstance W B} {d' : JohnsonCaseData J'}
    (h : (Sh.rename hr hx hy).hint J' = some d') :
    ∃ (J : SIInstance W A) (d : JohnsonCaseData J), Sh.hint J = some d ∧ d'.K = d.K ∧
      d'.m = d.m := by
  unfold hint at h ⊢
  change (match Sh.dom with
    | none => none
    | some D => D.hint J' J') = some d' at h
  rcases hD : Sh.dom with _ | D
  · rw [hD] at h; cases h
  · rw [hD] at h
    simp only at h ⊢
    have hs : (D.hint J' J').isSome := by rw [h]; rfl
    obtain ⟨hL, c, hc⟩ := (D.isSome_hint_iff J' J').1 hs
    let J : SIInstance W A := ⟨(D.toAlignDominant.Gs : Set (Perm W)), c.Δ₁, x, y⟩
    have hJ : D.HasHint J J := ⟨hL, c, rfl⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((D.isSome_hint_iff J J).2 hJ)
    refine ⟨J, d, hd, ?_, ?_⟩
    · rw [(D.hint_some h).1, (D.hint_some hd).1]
    · rw [(D.hint_some h).2, (D.hint_some hd).2]

end AlignShape

end Align

/-! ### Lines 5–7 with renamed letters -/

section Line57

variable {W : Type u} [Fintype W] [DecidableEq W] {A : Type v} {B : Type*}
  {r : A → B} {Sl : Set A} {G : Subgroup (Perm W)} {x y : W → A} {m : ℕ}
  {ϕ : G →* Perm (Fin m)} {ts : ℕ}

/-- Sec. 13.2: the enumerations of AggregateCertificates meet their specification for the
renamed strings exactly when they meet it for the original ones (one direction is what is
used). -/
theorem AggEnum.Spec.rename {E : AggEnum W (Fin m)} (h : E.Spec ϕ x y ts)
    (hr : Set.InjOn r Sl) (hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl) :
    E.Spec ϕ (r ∘ x) (r ∘ y) ts := by
  have hc := fun b => cond_mem hx hy b
  refine ⟨⟨?_, h.toCover.transporter, ?_⟩, ⟨h.toBound.tests, ?_, ?_⟩⟩
  · intro b T hT i hi
    rw [cond_comp] at hi ⊢
    rw [haltIndex_rename ϕ T hr (hc b)] at hi
    rw [stages_rename ϕ T hr (hc b)]
    have hc := h.toCover.cert b T hT i hi
    exact ⟨hc.cosets, hc.windows⟩
  · intro b T hT T' hT' σ hσ
    have hp := h.toCover.pair b T hT T' hT' σ hσ
    rw [cond_comp]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [haltIndex_rename ϕ T hr hx] at hi
      rw [stages_rename ϕ T hr hx]
      have hc := hp.source i hi
      exact ⟨hc.cosets, hc.windows⟩
    · rw [haltIndex_rename ϕ T hr hx] at hi
      rw [pairedQ_rename ϕ hr hx (hc b), kerN_stages_rename ϕ T hr hx]
      exact hp.comparison i hi
  · intro b T hT i hi
    rw [cond_comp] at hi ⊢
    rw [haltIndex_rename ϕ T hr (hc b)] at hi
    rw [stages_rename ϕ T hr (hc b)]
    have hc := h.toBound.cert b T hT i hi
    exact ⟨hc.reps, hc.length, hc.orbits⟩
  · intro b T hT T' hT'
    have hp := h.toBound.pair b T hT T' hT'
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [haltIndex_rename ϕ T hr hx] at hi
      rw [stages_rename ϕ T hr hx]
      have hc := hp.source i hi
      exact ⟨hc.reps, hc.length, hc.orbits⟩
    · rw [haltIndex_rename ϕ T hr hx] at hi
      exact hp.comparison i hi

namespace Line57Shape

/-- **The data of lines 5–7 for the renamed strings.** Procedure Align keeps its data
(`Babai.AlignShape.rename`); each reject exit keeps its test, which does not see the
renaming. -/
noncomputable def rename (hr : Set.InjOn r Sl) (hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl) :
    Line57Shape W A G x y ϕ ts → Line57Shape W B G (r ∘ x) (r ∘ y) ϕ ts
  | .align Sh => .align (Sh.rename hr hx hy)
  | .rejectDefect hne => .rejectDefect (by
      rwa [fixedGamma_rename ϕ ts hr hx, fixedGamma_rename ϕ ts hr hy])
  | .rejectCase h1 h2 => .rejectCase
      (by rwa [bigFGamma_rename ϕ ts hr hx, aggregateCase2a_rename ϕ ts hr hx])
      (by rwa [bigFGamma_rename ϕ ts hr hy, aggregateCase2a_rename ϕ ts hr hy])
  | .rejectGuide hset ht htm hW h =>
      .rejectGuide hset ht htm hW (guideClassMissing_rename ϕ ts hr hx hy hset ht htm hW h)

variable (hr : Set.InjOn r Sl) (hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl)

theorem inner_rename (Sh : Line57Shape W A G x y ϕ ts) :
    (Sh.rename hr hx hy).inner = Sh.inner.mapLetters r := by
  cases Sh with
  | align S => exact S.red_rename hr hx hy
  | rejectDefect _ => rfl
  | rejectCase _ _ => rfl
  | rejectGuide _ _ _ _ _ => rfl

omit hr in
include hx hy in
theorem allLettersIn_inner (Sh : Line57Shape W A G x y ϕ ts) : Sh.inner.AllLettersIn Sl := by
  cases Sh with
  | align S => exact S.allLettersIn_red hx hy
  | rejectDefect _ => trivial
  | rejectCase _ _ => trivial
  | rejectGuide _ _ _ _ _ => trivial

/-- **Sec. 15, lines 5–7: the round on the renamed strings is the renamed round.** -/
theorem red_rename (Sh : Line57Shape W A G x y ϕ ts) (E : AggEnum W (Fin m)) :
    (Sh.rename hr hx hy).red E = (Sh.red E).mapLetters r := by
  rw [red, red, inner_rename hr hx hy]
  exact aggregateRoundStrong_rename ϕ hr hx hy E _

omit hr in
include hx hy in
theorem allLettersIn_red (Sh : Line57Shape W A G x y ϕ ts) (E : AggEnum W (Fin m)) :
    (Sh.red E).AllLettersIn Sl :=
  allLettersIn_aggregateRoundStrong ϕ hx hy E (allLettersIn_inner hx hy Sh)

theorem hint_rename_isSome (Sh : Line57Shape W A G x y ϕ ts) (J : SIInstance W A) :
    ((Sh.rename hr hx hy).hint (J.mapLetters r)).isSome = (Sh.hint J).isSome := by
  cases Sh with
  | align S => exact S.hint_rename_isSome hr hx hy J
  | rejectDefect _ => rfl
  | rejectCase _ _ => rfl
  | rejectGuide _ _ _ _ _ => rfl

theorem hint_rename_some (Sh : Line57Shape W A G x y ϕ ts) {J' : SIInstance W B}
    {d' : JohnsonCaseData J'} (h : (Sh.rename hr hx hy).hint J' = some d') :
    ∃ (J : SIInstance W A) (d : JohnsonCaseData J), Sh.hint J = some d ∧ d'.K = d.K ∧
      d'.m = d.m := by
  cases Sh with
  | align S => exact S.hint_rename_some hr hx hy h
  | rejectDefect _ => cases h
  | rejectCase _ _ => cases h
  | rejectGuide _ _ _ _ _ => cases h

end Line57Shape

omit [Fintype W] [DecidableEq W] in
theorem alignInst_mapLetters (J : SIInstance W A) :
    alignInst (J.mapLetters r) = (alignInst J).mapLetters r := rfl

namespace Line57Data

variable {par cost : ℕ}

/-- **Sec. 15, lines 5–7: the data of the round for renamed strings.** The renaming `r` is
injective on the set `Sl`, which holds every letter of `x` and `y`. The reduction is the
renamed reduction (`Babai.Line57Data.red_rename`), with the same enumerations. -/
noncomputable def rename (C : Line57Data W A G x y ϕ ts par cost) (hr : Set.InjOn r Sl)
    (hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl) :
    Line57Data W B G (r ∘ x) (r ∘ y) ϕ ts par cost where
  shape := C.shape.rename hr hx hy
  enum := C.enum
  enum_spec := C.enum_spec.rename hr hx hy
  run_red := by
    rw [Line57Shape.red_rename hr hx hy,
      SIReduction.run_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _), C.run_red,
      strIso_rename hr hx hy]
  calls_K := by
    intro J hJ
    rw [Line57Shape.red_rename hr hx hy,
      SIReduction.calls_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _)] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact C.calls_K J₀ hJ₀
  calls_coset := by
    intro J hJ
    rw [Line57Shape.red_rename hr hx hy,
      SIReduction.calls_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _)] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact C.calls_coset J₀ hJ₀
  calls_length := by
    rw [Line57Shape.red_rename hr hx hy,
      SIReduction.calls_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _),
      List.length_map]
    exact C.calls_length
  hint_le := by
    intro J' d' h
    obtain ⟨J, d, hd, hK, hm⟩ := C.shape.hint_rename_some hr hx hy h
    rw [hK, hm]
    exact C.hint_le J d hd
  calls_progress := by
    intro J hJ
    rw [Line57Shape.red_rename hr hx hy,
      SIReduction.calls_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _)] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    rw [alignInst_mapLetters, C.shape.hint_rename_isSome hr hx hy]
    exact C.calls_progress J₀ hJ₀

variable (C : Line57Data W A G x y ϕ ts par cost) (hr : Set.InjOn r Sl)
  (hx : ∀ u, x u ∈ Sl) (hy : ∀ u, y u ∈ Sl)

/-- **The reduction of the renamed data is the renamed reduction.** -/
theorem red_rename :
    (C.rename hr hx hy).shape.red (C.rename hr hx hy).enum =
      (C.shape.red C.enum).mapLetters r :=
  Line57Shape.red_rename hr hx hy C.shape C.enum

/-- The calls of the renamed data are the renamed calls. -/
theorem calls_rename :
    ((C.rename hr hx hy).shape.red (C.rename hr hx hy).enum).calls =
      (C.shape.red C.enum).calls.map (SIInstance.mapLetters r) := by
  rw [red_rename]
  exact SIReduction.calls_mapLetters hr (Line57Shape.allLettersIn_red hx hy _ _)

omit hr in
include hx hy in
/-- Every call of the round has its letters among those of `x` and `y`. -/
theorem lettersIn_calls : ∀ J ∈ (C.shape.red C.enum).calls, J.LettersIn Sl :=
  SIReduction.mem_calls_allLettersIn (Line57Shape.allLettersIn_red hx hy _ _)

include hr hx hy in
/-- **Sec. 15, lines 5–7, for strings given as renamings.** If `x' = r ∘ x` and
`y' = r ∘ y` pointwise, with `r` injective on the letters of `x` and `y`, the data on `x, y`
give data on `x', y'` with the same enumerations, whose reduction is the reduction on `x, y`
with every call renamed, and whose calls are the renamed calls. -/
theorem exists_rename {x' y' : W → B} (hx' : ∀ u, r (x u) = x' u)
    (hy' : ∀ u, r (y u) = y' u) :
    ∃ C' : Line57Data W B G x' y' ϕ ts par cost, C'.enum = C.enum ∧
      C'.shape.red C'.enum = (C.shape.red C.enum).mapLetters r ∧
      (C'.shape.red C'.enum).calls = (C.shape.red C.enum).calls.map (SIInstance.mapLetters r) := by
  obtain rfl : r ∘ x = x' := funext hx'
  obtain rfl : r ∘ y = y' := funext hy'
  exact ⟨C.rename hr hx hy, rfl, C.red_rename hr hx hy, C.calls_rename hr hx hy⟩

end Line57Data

end Line57

end Babai
