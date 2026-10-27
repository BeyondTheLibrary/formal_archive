/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: lookup, zip and
flatten with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFParam
import Workspace.Machine.ListOps3

/-!
# Lookup, zip and flatten, with explicit constants

The `Explicit.PF` forms of `RAM.polyFun_lookup` (at natural keys, the only keys the entry
routine uses), `RAM.polyFun_listLookup`, `RAM.polyFun_zip`, `RAM.polyFun_zipIdx` and
`RAM.polyFun_flatten`, proved as the machine lemmas.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `RAM.polyFun_lookupStep` at natural keys. -/
theorem pf_natLookupStep : PF (lookupStep : (ℕ × Option β) × (ℕ × β) → ℕ × Option β) 73 1 17 1 := by
  have hg := (PF.ite ((((PF.snd (α := ℕ) (β := ℕ × β)).comp PF.fst).pair PF.fst).comp pf_natEq)
    (((PF.snd (α := ℕ) (β := ℕ × β)).comp PF.snd).comp pf_some)
    (PF.const (α := ℕ × (ℕ × β)) (none : Option β))).of_eq
      (g := fun z : ℕ × (ℕ × β) => (if z.2.1 = z.1 then some z.2.2 else none : Option β))
      (fun z => by by_cases h : z.2.1 = z.1 <;> simp [h])
  have hh := (PF.fst (α := β) (β := ℕ × (ℕ × β))).comp pf_some
  have hin := ((PF.fst (α := ℕ × Option β) (β := ℕ × β)).comp PF.snd).pair
    (((PF.fst (α := ℕ × Option β) (β := ℕ × β)).comp PF.fst).pair PF.snd)
  have h := ((PF.fst (α := ℕ × Option β) (β := ℕ × β)).comp PF.fst).pair
    (hin.comp (PF.optionElim hg hh))
  exact h.of_eq (fun s => by
    obtain ⟨⟨k, o⟩, a⟩ := s
    cases o <;> rfl)

/-- `RAM.polyFun_lookup` at natural keys. -/
theorem pf_natLookup : PF (fun p : List (ℕ × β) × ℕ =>
    (p.1.find? (fun q => decide (q.1 = p.2))).map Prod.snd) 405 2 16 1 := by
  have hfold := PF.foldl (ka := 3) (da := 1) (pf_natLookupStep (β := β)) (fun x r j => by
    have := lookupStep_size_bound x r j
    rw [pow_one]
    omega)
  have hin := ((PF.snd (α := List (ℕ × β)) (β := ℕ)).pair
    (PF.const (α := List (ℕ × β) × ℕ) (none : Option β))).pair PF.fst
  have h := (hin.comp hfold).comp PF.snd
  exact h.of_eq (fun p => by
    show (List.foldl (fun y a => lookupStep (y, a)) ((p.2, none) : ℕ × Option β) p.1).2 = _
    rw [lookupStep_result])

/-- `RAM.polyFun_natLookup`, for any value type. -/
theorem pf_natListLookup : PF (fun p : List (ℕ × β) × ℕ => p.1.lookup p.2) 405 2 16 1 := by
  have h := pf_natLookup (β := β)
  exact h.of_eq (fun p => (lookup_eq_find? p.2 p.1).symm)

/-- `RAM.polyFun_zipStep`. -/
theorem pf_zipStep :
    PF (zipStep : (List (α × β) × List β) × α → List (α × β) × List β) 61 1 20 1 := by
  have hg := (PF.fst (α := List (α × β)) (β := α)).pair
    (PF.const (α := List (α × β) × α) ([] : List β))
  have hh := ((((PF.snd (α := β × List β) (β := List (α × β) × α)).comp PF.snd).pair
    ((PF.fst (α := β × List β) (β := List (α × β) × α)).comp PF.fst)).pair
      ((PF.snd (α := β × List β) (β := List (α × β) × α)).comp PF.fst)).comp
        (pf_cons (β := α × β)) |>.pair
    ((PF.fst (α := β × List β) (β := List (α × β) × α)).comp PF.snd)
  have hin := ((PF.fst (α := List (α × β) × List β) (β := α)).comp PF.snd).pair
    (((PF.fst (α := List (α × β) × List β) (β := α)).comp PF.fst).pair PF.snd)
  have h := hin.comp (PF.listCases hg hh)
  exact h.of_eq (g := (zipStep : (List (α × β) × List β) × α → List (α × β) × List β))
    (fun s => by
    obtain ⟨⟨acc, m⟩, a⟩ := s
    cases m <;> rfl)

/-- `RAM.polyFun_zip`. -/
theorem pf_zip : PF (fun p : List α × List β => p.1.zip p.2) 406 4 33 2 := by
  have hfold := PF.foldl (ka := 4) (da := 2) (pf_zipStep (α := α) (β := β)) (fun x r j => by
    have := zipStep_size_bound x r j
    set N := Enc.size ((x, r) : (List (α × β) × List β) × List α)
    have e1 : 2 ^ 4 * (N + 1) ^ 2 = 16 * (N * N) + 32 * N + 16 := by ring
    have e2 : N * (8 * N + 1) = 8 * (N * N) + N := by ring
    rw [e1]
    omega)
  have hin := (((PF.const (α := List α × List β) ([] : List (α × β))).pair PF.snd).pair PF.fst)
  have h := ((hin.comp hfold).comp PF.fst).comp pf_reverse
  exact h.of_eq (fun p => by
    show (List.foldl (fun y a => zipStep (y, a))
      ((([] : List (α × β)), p.2) : List (α × β) × List β) p.1).1.reverse = _
    rw [zipStep_result]
    simp)

/-- `RAM.polyFun_zipIdx`. -/
theorem pf_zipIdx : PF (fun l : List α => l.zipIdx) 531 8 95 4 := by
  have h := ((PF.id (α := List α)).pair pf_rangeLength).comp pf_zip
  exact h.of_eq (fun l => by simp [List.zipIdx_eq_zip_range', List.range_eq_range'])

/-- `RAM.polyFun_flatten`. -/
theorem pf_flatten : PF (fun l : List (List α) => l.flatten) 692 5 14 2 := by
  have hfold := PF.foldl (ka := 1) (da := 2) (σ := List α) (α := List α) pf_append
    (fun x r j => by
      show Enc.size (List.foldl (fun y a => y ++ a) x (r.take j)) ≤ _
      rw [foldl_append_eq]
      set N := Enc.size ((x, r) : List α × List (List α)) with hN
      have hx : Enc.size x ≤ N := Combine.size_fst_le x r
      have hr : Enc.size r ≤ N := Combine.size_snd_le x r
      have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
      have happ := size_append_le x ((r.take j).flatten)
      have hf := size_flatten_le (r.take j)
      have hmono : Enc.size (r.take j) * (2 * Enc.size (r.take j) + 1) ≤ N * (2 * N + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e1 : 2 ^ 1 * (N + 1) ^ 2 = 2 * (N * N) + 4 * N + 2 := by ring
      have e2 : N * (2 * N + 1) = 2 * (N * N) + N := by ring
      rw [e1]
      omega)
  have h := ((PF.const (α := List (List α)) ([] : List α)).pair PF.id).comp hfold
  exact h.of_eq (fun l => by
    show List.foldl (fun y a => y ++ a) ([] : List α) l = l.flatten
    rw [foldl_append_eq, List.nil_append])

end Explicit
