/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the raw permutation
routines with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFEq
import Workspace.Algo.NormalizeSI

/-!
# Raw permutations, with explicit constants

The `Explicit.PF` forms of the routines of `Workspace/Algo/Perm.lean` (`rawApply`, `rawGet`,
`rawMul`, `rawOne`, `rawInvLookup`, `rawInv`, `rawIsPerm`, `rawPermEq`), of the sanitizer of
`Workspace/Algo/Luks.lean` (`capPerm`, `normPerm`, `normGens`) and of the renaming of
`Workspace/Algo/NormalizeSI.lean` (`rawLetterIndex`, `rawRenameStr`), proved along the same
compositions.
-/

namespace Explicit

open RAM Algo

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `Algo.polyFun_rawApply`. -/
theorem pf_rawApply : PF rawApply 402 2 29 1 := by
  have h := ((PF.id (α := RawPerm × ℕ)).pair PF.snd).comp pf_getD
  exact h

/-- `Algo.polyFun_rawGet`. -/
theorem pf_rawGet : PF rawGet 406 2 31 1 := by
  have h := ((PF.id (α := RawStr × ℕ)).pair (PF.const (α := RawStr × ℕ) (0 : ℕ))).comp pf_getD
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawMul`. -/
theorem pf_rawMul : PF rawMul 942 5 64 2 := by
  have h := (PF.mapParamB pf_rawApply).pf
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawOne`. -/
theorem pf_rawOne : PF rawOne 465 5 28 2 := by
  have h := pf_rangeLength (α := ℕ)
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawInvLookup`. -/
theorem pf_rawInvLookup : PF rawInvLookup 415 2 20 1 := by
  have h := ((pf_natListLookup (β := ℕ)).pair
    (PF.const (α := List (ℕ × ℕ) × ℕ) (0 : ℕ))).comp pf_optionGetD
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawInv`. -/
theorem pf_rawInv : PF rawInv 1401 20 251 8 := by
  have h := ((pf_zipIdx (α := ℕ)).pair pf_rangeLength).comp (PF.mapParamB pf_rawInvLookup).pf
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawIsPerm`. -/
theorem pf_rawIsPerm : PF rawIsPerm 858 6 3 0 := by
  have hmem := (PF.ite (((PF.snd (α := RawPerm) (β := ℕ)).pair PF.fst).comp pf_natListMem)
    (PF.const (α := RawPerm × ℕ) false) (PF.const (α := RawPerm × ℕ) true)).of_eq
      (g := fun p : RawPerm × ℕ => (!decide (p.2 ∈ p.1) : Bool))
      (fun p => by by_cases h : p.2 ∈ p.1 <;> simp [h])
  have h := (((PF.id (α := RawPerm)).pair pf_rangeLength).comp
    (PF.filterParamB hmem).pf).comp pf_isEmpty
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawPermEq`. -/
theorem pf_rawPermEq : PF rawPermEq 414 2 3 0 := by
  have h := pf_listNatEq
  exact h

/-- `Algo.polyFun_capPerm`. -/
theorem pf_capPerm : PF capPerm 1176 10 139 4 := by
  have hstep := ((((PF.fst (α := RawPerm × ℕ) (β := ℕ)).comp PF.fst).pair PF.snd).comp
    pf_rawGet).pair ((PF.fst (α := RawPerm × ℕ) (β := ℕ)).comp PF.snd) |>.comp pf_min
  have hin := ((PF.snd (α := RawStr) (β := RawPerm)).pair
    ((((PF.fst (α := RawStr) (β := RawPerm)).comp pf_length).pair
      (PF.const (α := RawStr × RawPerm) (1 : ℕ))).comp pf_sub)).pair
    ((PF.fst (α := RawStr) (β := RawPerm)).comp pf_rawOne)
  have h := hin.comp (PF.mapParamB hstep).pf
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_normPerm`. -/
theorem pf_normPerm : PF normPerm 1709 24 163 4 := by
  have h := PF.ite (pf_capPerm.comp pf_rawIsPerm) pf_capPerm
    ((PF.fst (α := RawStr) (β := RawPerm)).comp pf_rawOne)
  exact h.of_eq (fun p => by
    by_cases h : rawIsPerm (capPerm p) = true <;> simp [normPerm, h])

/-- `Algo.polyFun_normGens`. -/
theorem pf_normGens : PF normGens 8181 121 222 5 := by
  have h := (PF.mapParamB pf_normPerm).pf
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawLetterIndex`. -/
theorem pf_rawLetterIndex : PF rawLetterIndex 620 8 122 4 := by
  have h := (((PF.fst (α := RawStr) (β := ℕ)).comp pf_zipIdx).pair PF.snd).comp pf_rawInvLookup
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawRenameStr`. -/
theorem pf_rawRenameStr : PF rawRenameStr 2945 41 181 5 := by
  have h := (PF.mapParamB pf_rawLetterIndex).pf
  exact h.of_eq (fun _ => rfl)

end Explicit
