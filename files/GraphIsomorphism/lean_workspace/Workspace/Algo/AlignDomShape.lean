/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the round of Procedure Align on the Master side, `Babai.AlignShape.red`,
rewritten when line 6 finds a dominant color class (§14.1, lines 6–11).
-/
import Workspace.Algo.AlignVersionsShape

/-!
# The Master's round of Procedure Align with a dominant color class

`Babai.AlignShape.red` is the union of Eq. (71) over the versions of `X(y)`; for each version
it runs the Chain Rule of line 5 over the color classes, the window `Ω(Δ_j)` of line 6 first,
and it replaces the call on that window by the round of lines 7–11,
`Babai.AlignDominantRoundData.cosetRound`.

This file writes that tree in the form the machine walks it:

* `Algo.cosetAlignExpand_eq_unionOver`: for each version, if the transporter `C` of lines 1–3
  is empty the branch ends; otherwise it is the round on the head call `⟨C, Ω(Δ_j), x, y⟩`
  followed by the Chain Rule over the other color classes, started from its answer;
* `Algo.alignShape_red_of_dom_large`: in cases 2 and 3 of the repair (`m*` large), the round
  on the head window is the Chain Rule over the orbits of `G*` in the window, so the branch of
  a version is the Chain Rule over those orbits followed by the other color classes — the
  plain loop of Eq. (71) over a longer list of windows;
* `Algo.alignShape_red_of_dom_small`: in case 1 (`m*` small), the round on the head window is
  the strong descent to `ker ϕ*`, `Babai.strongDescent`.
-/

namespace Algo
open Babai Equiv
open scoped Pointwise

universe u v

namespace SIRed

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W] {α β : Type*}

/-- Substitution for calls commutes with `bind`. -/
theorem expand_bind (F : SIInstance W A → SIReduction W A (Set (Perm W)))
    (R : SIReduction W A α) (f : α → SIReduction W A β) :
    (R.bind f).expand F = (R.expand F).bind (fun a => (f a).expand F) := by
  induction R with
  | done a => rfl
  | call I k ih =>
    show (F I).bind (fun ans => ((k ans).bind f).expand F) =
      ((F I).bind fun ans => (k ans).expand F).bind _
    rw [SIReduction.bind_assoc]
    exact congrArg _ (funext ih)

end SIRed

section Tree

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- The substitution of `Babai.cosetAlignExpand`: the head window is expanded, every other
call stands. -/
noncomputable def headExpand (head : Set W)
    (g : SIInstance W A → SIReduction W A (Set (Perm W))) (J : SIInstance W A) :
    SIReduction W A (Set (Perm W)) :=
  if J.Δ = head then g J else .call J .done

/-- A chain over windows other than the head is not touched by the substitution. -/
theorem expand_cosetChain_of_not_mem (x y : W → A) (head : Set W)
    (g : SIInstance W A → SIReduction W A (Set (Perm W))) :
    ∀ (Δs : List (Set W)), head ∉ Δs → ∀ C : Set (Perm W),
      (Babai.cosetChain x y Δs C).expand (headExpand head g) = Babai.cosetChain x y Δs C := by
  intro Δs
  induction Δs with
  | nil => intro _ C; rfl
  | cons Δ rest ih =>
    intro hn C
    have hΔ : Δ ≠ head := fun h => hn (h ▸ List.mem_cons_self)
    have hr : head ∉ rest := fun h => hn (List.mem_cons_of_mem _ h)
    simp only [Babai.cosetChain]
    split
    · rfl
    · show (headExpand head g ⟨C, Δ, x, y⟩).bind _ = _
      rw [headExpand, if_neg hΔ]
      show SIReduction.call _ (fun a => (Babai.cosetChain x y rest a).expand _) = _
      exact congrArg _ (funext fun a => ih hr a)

/-- The branch of one version after the substitution. -/
theorem expand_cosetChain_head (x y : W → A) (head : Set W) (tail : List (Set W))
    (hn : head ∉ tail) (g : SIInstance W A → SIReduction W A (Set (Perm W)))
    (C : Set (Perm W)) :
    (Babai.cosetChain x y (head :: tail) C).expand (headExpand head g) =
      if C = ∅ then .done ∅ else (g ⟨C, head, x, y⟩).bind (fun a => Babai.cosetChain x y tail a) := by
  simp only [Babai.cosetChain]
  split
  · rfl
  · show (headExpand head g ⟨C, head, x, y⟩).bind _ = _
    rw [headExpand, if_pos rfl]
    exact congrArg _ (funext fun a => expand_cosetChain_of_not_mem x y head g tail hn a)

/-- The union of Eq. (71) after the substitution. -/
theorem expand_unionOver {𝒴 : Type*} (F : SIInstance W A → SIReduction W A (Set (Perm W)))
    (b : 𝒴 → SIReduction W A (Set (Perm W))) :
    ∀ L : List 𝒴, (SIReduction.unionOver L b).expand F =
      SIReduction.unionOver L (fun Y => (b Y).expand F) := by
  intro L
  induction L with
  | nil => rfl
  | cons Y rest ih =>
    simp only [SIReduction.unionOver]
    rw [SIRed.expand_bind]
    refine congrArg _ (funext fun S => ?_)
    rw [SIRed.expand_bind, ih]
    rfl

/-- §14.1, lines 5–11: **the round of Procedure Align, version by version.** For each
version the transporter `C` of lines 1–3 is computed; if it is empty the branch ends, and
otherwise the round `g` on the head call is followed by the Chain Rule over the other color
classes, started from its answer. -/
theorem cosetAlignExpand_eq_unionOver {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳]
    {G : Subgroup (Perm W)} (ϕ : G →* Perm Γ) (x y : W → A) (X : 𝒳) (versions : List 𝒳)
    (head : Set W) (tail : List (Set W)) (hn : head ∉ tail)
    (g : SIInstance W A → SIReduction W A (Set (Perm W))) :
    cosetAlignExpand ϕ x y X versions head tail g =
      SIReduction.unionOver versions (fun Y =>
        if alignTransporter ϕ X Y = ∅ then .done ∅
        else (g ⟨alignTransporter ϕ X Y, head, x, y⟩).bind
          (fun a => Babai.cosetChain x y tail a)) := by
  unfold cosetAlignExpand cosetDesignAlign
  have hF : (fun J : SIInstance W A => if J.Δ = head then g J else SIReduction.call J .done) =
      headExpand head g := rfl
  rw [hF, expand_unionOver]
  refine congrArg _ (funext fun Y => ?_)
  unfold cosetAlignChain
  exact expand_cosetChain_head x y head tail hn g _

/-- The Chain Rule from the empty set answers `∅` at once. -/
theorem babaiCosetChain_empty (x y : W → A) (l : List (Set W)) :
    Babai.cosetChain x y l ∅ = .done ∅ := by
  cases l with
  | nil => rfl
  | cons Δ rest => simp [Babai.cosetChain]

/-- The Chain Rule over two lists in a row is the Chain Rule over their concatenation, from
a nonempty coset. -/
theorem cosetChain_append (x y : W → A) :
    ∀ (l₁ l₂ : List (Set W)) (C : Set (Perm W)), C ≠ ∅ →
      (Babai.cosetChain x y l₁ C).bind (fun a => Babai.cosetChain x y l₂ a) = Babai.cosetChain x y (l₁ ++ l₂) C := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C _; rfl
  | cons Δ rest ih =>
    intro l₂ C hC
    simp only [Babai.cosetChain, List.cons_append, if_neg hC]
    show SIReduction.call _ (fun a => (Babai.cosetChain x y rest a).bind _) = _
    refine congrArg _ (funext fun a => ?_)
    by_cases ha : a = ∅
    · subst ha
      rw [babaiCosetChain_empty, babaiCosetChain_empty]
      exact babaiCosetChain_empty x y l₂
    · exact ih l₂ a ha

end Tree

section Shape

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {G : Subgroup (Perm W)} {x y : W → A} (S : AlignShape W A G x y)

/-- §14.1, lines 6–11, **cases 2 and 3 of the repair**: when line 6 found a
dominant color class and `m*` is large, the round of lines 7–11 on the head window is the
Chain Rule over the orbits of `G*` in the window, the dominant orbit first. So each version
runs the Chain Rule over those orbits and then over the other color classes. -/
theorem alignShape_red_of_dom_large (hn : S.head ∉ S.tail) {D : AlignDominantRoundData W}
    (hD : S.dom = some D) (hL : D.LargeParam) :
    S.red = (letI := S.act; cosetDesignAlign S.ϕ x y S.X' S.versions
      (S.domEnum.orbits ++ S.tail)) := by
  letI := S.act
  change cosetAlignExpand S.ϕ x y S.X' S.versions S.head S.tail S.dominantRound = _
  rw [cosetAlignExpand_eq_unionOver _ _ _ _ _ _ _ hn]
  unfold cosetDesignAlign
  refine congrArg _ (funext fun Y => ?_)
  unfold cosetAlignChain
  split
  · rename_i he
    rw [he]
    exact (babaiCosetChain_empty x y _).symm
  · rename_i hne
    have hr : S.dominantRound ⟨alignTransporter S.ϕ S.X' Y, S.head, x, y⟩ =
        Babai.cosetChain x y S.domEnum.orbits (alignTransporter S.ϕ S.X' Y) := by
      unfold AlignShape.dominantRound
      rw [hD]
      simp only [AlignDominantRoundData.cosetRound, if_pos hL]
    rw [hr]
    exact cosetChain_append x y _ _ _ hne

/-- §14.1, lines 6–11, **case 1 of the repair**: when line 6 found a
dominant color class and `m*` is small, the round of lines 7–11 on the head window is the
strong descent to `ker ϕ*`: the Chain Rule over the orbits of `ker ϕ*` in the window, on each
of the listed cosets of `ker ϕ*` covering the candidate set. -/
theorem alignShape_red_of_dom_small (hn : S.head ∉ S.tail) {D : AlignDominantRoundData W}
    (hD : S.dom = some D) (hL : ¬ D.LargeParam) :
    S.red = (letI := S.act; SIReduction.unionOver S.versions (fun Y =>
        if alignTransporter S.ϕ S.X' Y = ∅ then .done ∅
        else (strongDescent D.ker x y (S.domEnum.reps (alignTransporter S.ϕ S.X' Y))
            S.domEnum.kernelOrbits).bind (fun a => Babai.cosetChain x y S.tail a))) := by
  letI := S.act
  change cosetAlignExpand S.ϕ x y S.X' S.versions S.head S.tail S.dominantRound = _
  rw [cosetAlignExpand_eq_unionOver _ _ _ _ _ _ _ hn]
  refine congrArg _ (funext fun Y => ?_)
  split
  · rfl
  · have hr : S.dominantRound ⟨alignTransporter S.ϕ S.X' Y, S.head, x, y⟩ =
        strongDescent D.ker x y (S.domEnum.reps (alignTransporter S.ϕ S.X' Y))
          S.domEnum.kernelOrbits := by
      unfold AlignShape.dominantRound
      rw [hD]
      simp only [AlignDominantRoundData.cosetRound, if_neg hL]
    rw [hr]

end Shape

end Algo
