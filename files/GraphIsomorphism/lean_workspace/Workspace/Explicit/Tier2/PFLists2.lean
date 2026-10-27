/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: more list routines
with explicit polynomial time. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFLists

/-!
# More list routines with explicit constants

The `Explicit.PF` forms of routines of `Workspace/Machine/ListOps2.lean`, each proved as the
`RAM.PolyFun` lemma of the same name: indexing, the default of an option, the emptiness test.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `RAM.polyFun_getStep`. -/
theorem pf_getStep : PF (getStep : (ℕ × Option α) × α → ℕ × Option α) 48 1 13 1 := by
  have hcond := (((PF.fst (α := ℕ × Option α) (β := α)).comp
    (PF.fst (α := ℕ) (β := Option α))).pair
    (PF.const (α := (ℕ × Option α) × α) (1 : ℕ))).comp pf_natEq
  have ht := (PF.const (α := (ℕ × Option α) × α) (0 : ℕ)).pair
    ((PF.snd (α := ℕ × Option α) (β := α)).comp (pf_some (β := α)))
  have he := ((((PF.fst (α := ℕ × Option α) (β := α)).comp
    (PF.fst (α := ℕ) (β := Option α))).pair
    (PF.const (α := (ℕ × Option α) × α) (1 : ℕ))).comp pf_sub).pair
    ((PF.fst (α := ℕ × Option α) (β := α)).comp (PF.snd (α := ℕ) (β := Option α)))
  refine (PF.ite hcond ht he).of_eq (fun s => ?_)
  by_cases h : s.1.1 = 1 <;> simp [getStep, h]

/-- `RAM.polyFun_getElem?`. -/
theorem pf_getElem? : PF (fun p : List α × ℕ => p.1[p.2]?) 382 2 21 1 := by
  have hfold := PF.foldl (ka := 3) (da := 1) (pf_getStep (α := α)) (fun x r j => by
    have := getStep_size_bound x r j
    rw [pow_one]
    omega)
  have hin := ((((PF.snd (α := List α) (β := ℕ)).pair (PF.const (α := List α × ℕ) (1 : ℕ))).comp
    pf_add).pair (PF.const (α := List α × ℕ) (none : Option α))).pair
    (PF.fst (α := List α) (β := ℕ))
  exact ((hin.comp hfold).comp (PF.snd (α := ℕ) (β := Option α))).of_eq
    (fun p => getStep_result p.1 p.2)

/-- `RAM.polyFun_optionGetD`. -/
theorem pf_optionGetD : PF (fun q : Option α × α => q.1.getD q.2) 17 1 1 1 :=
  (PF.optionElim (β := α) (g := (fun a : α => a)) (h := (Prod.fst : α × α → α)) PF.id
    PF.fst).of_eq (fun q => by obtain ⟨o, a⟩ := q; cases o <;> rfl)

/-- `RAM.polyFun_isEmpty`. -/
theorem pf_isEmpty : PF (fun l : List α => l.isEmpty) 33 1 3 0 :=
  (((PF.id (α := List α)).pair (PF.const (α := List α) (0 : ℕ))).comp
    (PF.listCases (α := α) (σ := ℕ) (γ := Bool) (PF.const true) (PF.const false))).of_eq
    (fun l => by cases l <;> rfl)

/-- `RAM.polyFun_getD`. -/
theorem pf_getD : PF (fun p : (List α × ℕ) × α => p.1.1.getD p.1.2 p.2) 395 2 26 1 := by
  have h := (((PF.fst (α := List α × ℕ) (β := α)).comp pf_getElem?).pair
    (PF.snd (α := List α × ℕ) (β := α))).comp pf_optionGetD
  exact h.of_eq (fun p => by simp [List.getD])

end Explicit
