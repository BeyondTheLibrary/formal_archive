import Workspace.Algo.TopMasterLine57Lift
import Workspace.Master.Line57Rename

/-! # The round of lines 5–7 on the renamed context is the paper's round, renamed

Section 15, lines 5–7: the machine runs the round of lines 5–7 on the normalized context
`Algo.masterL57Ctx`, whose strings are `ρ ∘ x_Δ` and `ρ ∘ y_Δ` for the renaming `ρ` of
`Algo.masterL57Relabel`, and the node renames the calls back by `c ↦ M[c]`
(`Algo.masterL57Unl`, with `M = Algo.masterL57Order`). This file connects that with the
paper's round on `x_Δ, y_Δ`:

* `Algo.redMapCalls_siUnlabel`: renaming back the calls of a tree is
  `Babai.SIReduction.mapLetters` with the map `c ↦ M[c]`;
* `Algo.masterL57Unl_line57Data`: from data of lines 5–7 (`Babai.Line57Data`) on the
  context's strings, the data on `x_Δ, y_Δ` with the same enumerations, whose reduction is the
  context's reduction renamed back, `masterL57Unl P (C'.shape.red C'.enum)`. The renaming back
  is injective on the positions of `M`, which hold every letter of the context
  (`Babai.Line57Data.exists_rename`).
-/

namespace Algo
open RAM Babai Equiv

/-- Renaming back the calls of a tree through `M` is renaming its letters by `c ↦ M[c]`. -/
theorem redMapCalls_siUnlabel {Ω α : Type} (M : List ℕ) :
    ∀ T : SIReduction Ω ℕ α,
      redMapCalls (siUnlabel M) T = T.mapLetters (fun c => rawGet (M, c)) := by
  intro T
  induction T with
  | done a => rfl
  | call I k ih =>
    change SIReduction.call _ _ = SIReduction.call _ _
    congr 1
    funext a
    exact ih a

/-- The renaming back of the context's first string is `x_Δ`. -/
theorem rawGet_masterL57Ctx_x (P : RawMasterSI) (u : Fin P.1.1.length) :
    rawGet (masterL57Order P, decStrN P.1.1.length (masterL57Ctx P).2.1 u) =
      decStrN P.1.1.length (masterL57XW P) u := by
  change rawGet (masterL57Order P, decStrN P.1.1.length
    (masterL57Relabel (masterL57Order P, masterL57XW P)) u) = _
  rw [decStrN_masterL57Relabel _ (length_masterL57XW P)]
  refine (masterL57Rank_letter (masterL57XW_letters P _ ?_)).2
  have hu : (u : ℕ) < (masterL57XW P).length := (length_masterL57XW P).symm ▸ u.isLt
  simp only [decStrN]
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem hu

/-- The renaming back of the context's second string is `y_Δ`. -/
theorem rawGet_masterL57Ctx_y (P : RawMasterSI) (u : Fin P.1.1.length) :
    rawGet (masterL57Order P, decStrN P.1.1.length (masterL57Ctx P).2.2.1 u) =
      decStrN P.1.1.length (masterL57YW P) u := by
  change rawGet (masterL57Order P, decStrN P.1.1.length
    (masterL57Relabel (masterL57Order P, masterL57YW P)) u) = _
  rw [decStrN_masterL57Relabel _ (length_masterL57YW P)]
  refine (masterL57Rank_letter (masterL57YW_letters P _ ?_)).2
  have hu : (u : ℕ) < (masterL57YW P).length := (length_masterL57YW P).symm ▸ u.isLt
  simp only [decStrN]
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem hu

/-- The letters of the context's strings are positions of `M`. -/
theorem masterL57Ctx_x_lt (P : RawMasterSI) (u : Fin P.1.1.length) :
    decStrN P.1.1.length (masterL57Ctx P).2.1 u < (masterL57Order P).length := by
  refine lt_of_lt_of_le (masterL57Rank_lt_letters (length_masterL57XW P)
    (masterL57XW_letters P) u) ?_
  rw [masterL57Order, List.length_append]
  omega

theorem masterL57Ctx_y_lt (P : RawMasterSI) (u : Fin P.1.1.length) :
    decStrN P.1.1.length (masterL57Ctx P).2.2.1 u < (masterL57Order P).length := by
  refine lt_of_lt_of_le (masterL57Rank_lt_letters (length_masterL57YW P)
    (masterL57YW_letters P) u) ?_
  rw [masterL57Order, List.length_append]
  omega

/-- **Sec. 15, lines 5–7: the round on the renamed context, renamed back, is the paper's round
on `x_Δ, y_Δ`.** Data of lines 5–7 on the context's strings give data on `x_Δ, y_Δ` with the
same enumerations, whose reduction is the context's reduction with its calls renamed back
(`Algo.masterL57Unl`), and whose calls are the renamed-back calls. -/
theorem masterL57Unl_line57Data (P : RawMasterSI) {G : Subgroup (Perm (Fin P.1.1.length))}
    {m : ℕ} {ϕ : G →* Perm (Fin m)} {ts par cost : ℕ}
    (C' : Line57Data (Fin P.1.1.length) ℕ G (decStrN P.1.1.length (masterL57Ctx P).2.1)
      (decStrN P.1.1.length (masterL57Ctx P).2.2.1) ϕ ts par cost) :
    ∃ C : Line57Data (Fin P.1.1.length) ℕ G (decStrN P.1.1.length (masterL57XW P))
        (decStrN P.1.1.length (masterL57YW P)) ϕ ts par cost,
      C.enum = C'.enum ∧
      C.shape.red C.enum = masterL57Unl P (C'.shape.red C'.enum) ∧
      (C.shape.red C.enum).calls =
        (C'.shape.red C'.enum).calls.map (siUnlabel (masterL57Order P)) := by
  obtain ⟨C, he, hred, hcalls⟩ := C'.exists_rename (masterL57Unlabel_injOn P)
    (masterL57Ctx_x_lt P) (masterL57Ctx_y_lt P) (rawGet_masterL57Ctx_x P)
    (rawGet_masterL57Ctx_y P)
  refine ⟨C, he, ?_, ?_⟩
  · rw [hred, masterL57Unl, redMapCalls_siUnlabel]
  · rw [hcalls]
    rfl

end Algo
