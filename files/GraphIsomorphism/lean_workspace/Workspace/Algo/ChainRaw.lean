/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: sifting through a table, on raw data.
-/
import Workspace.Algo.Chain
import Workspace.Algo.Orbits

/-!
# Sifting on raw data

`Workspace/Algo/Chain.lean` has the mathematics of the point stabilizer chain and of its
sifting table.  This file is the routine: the table as raw data, the sifting loop, its
specification against the mathematics, and its `RAM.PolyFun`.  It is the first half of work
package A4 of `Workspace/Algo/DESIGN.md`; the construction of the table by the closure loop,
the membership test, the order and the transversals follow in the next sessions.

## The raw table

A row is an association list from the image point `j` to the permutation stored at `(i, j)`,
so a row is `List (ℕ × RawPerm)` and the table is a list of rows.  Lookup is
`RAM.polyFun_getD` for the row and `RAM.polyFun_natLookup` for the entry, both already
available.  A position that is not listed is empty, so the raw table needs no `Option` of its
own and no padding.

## The loop

`Algo.rawSift (t, σ)` folds over `List.range σ.length`, one round per level.  The accumulator
is an `Option RawPerm`: `none` once a level has no entry, and otherwise the residue.  The
round count arrives as the length of a list, never as a machine natural, for the reason
recorded at the end of `Workspace/Machine/DESIGN.md`; here the natural list is the
permutation being sifted, whose length is the degree.

## Main definitions and results

* `Algo.rawSiftStep`, `Algo.rawSift`;
* `Algo.decTable` — the table a raw table describes, and `Algo.RawTable.WF`;
* `Algo.rawSift_spec` — `Algo.rawSift` computes `Algo.sift` of the decoded table;
* `Algo.polyFun_rawSift` — the routine is a `RAM.PolyFun`.

Every routine is total: on raw data that is not well formed it answers junk, and no
specification lemma claims anything about that answer.  No axiom, no `sorry`, no running-time
claim outside `RAM.PolyFun`.
-/

namespace Algo

open RAM

/-! ## The raw table -/

/-- One row of a raw table: the permutations stored at the positions `(i, j)`, listed by `j`. -/
abbrev RawRow := List (ℕ × RawPerm)

/-- A raw sifting table: one row per level. -/
abbrev RawTable := List RawRow

/-- The entry of a raw table at the position `(i, j)`, if there is one. -/
def rawTableGet (p : RawTable × (ℕ × ℕ)) : Option RawPerm :=
  (p.1.getD p.2.1 []).lookup p.2.2

/-- **The table a raw table describes.** -/
noncomputable def decTable (n : ℕ) (t : RawTable) : Table n := fun i j =>
  (rawTableGet (t, (i, j))).map (decPerm n)

/-- A raw table is **well formed** for the degree `n` when every permutation it stores is. -/
def RawTable.WF (n : ℕ) (t : RawTable) : Prop := ∀ row ∈ t, ∀ q ∈ row, RawPerm.WF n q.2

/-- `τ` is stored somewhere in the table. -/
def TableEntry (t : RawTable) (τ : RawPerm) : Prop := ∃ i j, rawTableGet (t, (i, j)) = some τ

/-! ### Lookup

Two facts about `List.lookup` that the specification and the size bound need: a successful
lookup returns an entry of the list, and the row read at a level is a row of the table. -/

theorem mem_of_lookup_eq_some {α β : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (a : α) (b : β), l.lookup a = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro a b h; exact absurd h (by simp [List.lookup])
  | cons q t ih =>
      intro a b h
      obtain ⟨k, v⟩ := q
      by_cases hq : a = k
      · subst hq
        have hb : b = v := by simpa [List.lookup] using h.symm
        subst hb
        exact List.mem_cons_self ..
      · have hbeq : (a == k) = false := by simpa using hq
        have h' : t.lookup a = some b := by simpa [List.lookup, hbeq] using h
        exact List.mem_cons_of_mem _ (ih a b h')

/-- The size of an entry is at most the size of the table. -/
theorem size_le_of_tableEntry {t : RawTable} {τ : RawPerm} (h : TableEntry t τ) :
    Enc.size τ ≤ Enc.size t := by
  obtain ⟨i, j, hij⟩ := h
  rw [rawTableGet] at hij
  have hrow : t.getD i [] ∈ t := by
    by_cases hi : i < t.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hij
      exact absurd hij (by simp [List.lookup])
  have hmem : (j, τ) ∈ t.getD i [] := mem_of_lookup_eq_some _ _ _ hij
  have h1 : Enc.size τ ≤ Enc.size ((j, τ) : ℕ × RawPerm) := Combine.size_snd_le j τ
  have h2 : Enc.size ((j, τ) : ℕ × RawPerm) ≤ Enc.size (t.getD i []) := size_mem_le hmem
  have h3 : Enc.size (t.getD i []) ≤ Enc.size t := size_mem_le hrow
  omega

/-- An entry of a well-formed table is a well-formed permutation. -/
theorem wf_of_tableEntry {n : ℕ} {t : RawTable} (ht : RawTable.WF n t) {τ : RawPerm}
    (h : TableEntry t τ) : RawPerm.WF n τ := by
  obtain ⟨i, j, hij⟩ := h
  rw [rawTableGet] at hij
  have hrow : t.getD i [] ∈ t := by
    by_cases hi : i < t.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hij
      exact absurd hij (by simp [List.lookup])
  exact ht _ hrow _ (mem_of_lookup_eq_some _ _ _ hij)

/-! ## The loop -/

/-- **One round of sifting.**  The accumulator is the residue so far, or `none` once a level has
had no entry. -/
def rawSiftStep (p : RawTable × (Option RawPerm × ℕ)) : Option RawPerm :=
  match p.2.1 with
  | none => none
  | some r =>
      match rawTableGet (p.1, (p.2.2, rawApply (r, p.2.2))) with
      | none => none
      | some τ => some (rawMul (rawInv τ, r))

/-- **Sifting on raw data.**  One round per level; the degree is the length of the permutation
being sifted. -/
def rawSift (p : RawTable × RawPerm) : Option RawPerm :=
  List.foldl (fun acc i => rawSiftStep (p.1, (acc, i))) (some p.2) (List.range p.2.length)

theorem rawSiftStep_none (t : RawTable) (i : ℕ) : rawSiftStep (t, (none, i)) = none := rfl

theorem rawSiftFold_none (t : RawTable) :
    ∀ l : List ℕ, List.foldl (fun acc i => rawSiftStep (t, (acc, i))) none l = none := by
  intro l
  induction l with
  | nil => rfl
  | cons a s ih => rw [List.foldl_cons, rawSiftStep_none]; exact ih

/-! ## The specification

The raw loop walks the levels `0, 1, …, n−1` in order, which is `List.range' 0 n`; the
mathematical `Algo.siftAux` walks the same levels with a fuel.  The induction is on the fuel,
with the starting level and the residue general. -/

/-- Applying a raw permutation at a level is reading the decoded one there.  Past the domain
both sides are the level itself, so no hypothesis is needed. -/
theorem rawApply_encPerm_eq_evalAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) :
    rawApply (encPerm n σ, i) = evalAt σ i := by
  by_cases h : i < n
  · rw [rawApply_encPerm n σ h, evalAt_of_lt σ h]
  · rw [rawApply_of_length_le (by rw [length_encPerm]; omega), evalAt_of_le σ (by omega)]

theorem rawSiftFold_spec {n : ℕ} {t : RawTable} (ht : RawTable.WF n t) :
    ∀ (k i : ℕ) (r : Equiv.Perm (Fin n)),
      List.foldl (fun acc j => rawSiftStep (t, (acc, j))) (some (encPerm n r))
          (List.range' i k)
        = (siftAux (decTable n t) k i r).map (encPerm n) := by
  intro k
  induction k with
  | zero => intro i r; rfl
  | succ k ih =>
      intro i r
      have hlist : List.range' i (k + 1) = i :: List.range' (i + 1) k := rfl
      rw [hlist, List.foldl_cons]
      have hstep : rawSiftStep (t, (some (encPerm n r), i))
          = (rawTableGet (t, (i, evalAt r i))).map (fun τ => rawMul (rawInv τ, encPerm n r)) := by
        show (match rawTableGet (t, (i, rawApply (encPerm n r, i))) with
            | none => none
            | some τ => some (rawMul (rawInv τ, encPerm n r))) = _
        rw [rawApply_encPerm_eq_evalAt]
        rcases rawTableGet (t, (i, evalAt r i)) with _ | τ <;> rfl
      rcases hlook : rawTableGet (t, (i, evalAt r i)) with _ | τ
      · rw [hstep, hlook]
        simp only [Option.map_none]
        rw [rawSiftFold_none t]
        have : decTable n t i (evalAt r i) = none := by rw [decTable, hlook]; rfl
        rw [siftAux_succ_of_none this]
        rfl
      · have hwf : RawPerm.WF n τ := wf_of_tableEntry ht ⟨i, evalAt r i, hlook⟩
        have hdec : decTable n t i (evalAt r i) = some (decPerm n τ) := by
          rw [decTable, hlook]; rfl
        rw [hstep, hlook]
        simp only [Option.map_some]
        have hres : rawMul (rawInv τ, encPerm n r) = encPerm n ((decPerm n τ)⁻¹ * r) := by
          rw [rawInv_of_wf hwf, rawMul_encPerm]
        rw [hres, ih (i + 1) ((decPerm n τ)⁻¹ * r), siftAux_succ_of_some hdec]

/-- **The specification of `Algo.rawSift`.**  On a well-formed table, the raw loop computes the
sift of the decoded table. -/
theorem rawSift_spec {n : ℕ} {t : RawTable} (ht : RawTable.WF n t) (σ : Equiv.Perm (Fin n)) :
    rawSift (t, encPerm n σ) = (sift (decTable n t) σ).map (encPerm n) := by
  rw [rawSift, sift]
  show List.foldl (fun acc i => rawSiftStep (t, (acc, i))) (some (encPerm n σ))
      (List.range (encPerm n σ).length) = _
  rw [length_encPerm, List.range_eq_range']
  exact rawSiftFold_spec ht n 0 σ

/-- **Sifting to the identity** is what the mathematics calls it: the raw answer is the raw
identity exactly when the decoded sift is the identity. -/
theorem rawSift_eq_one_iff {n : ℕ} {t : RawTable} (ht : RawTable.WF n t)
    (σ : Equiv.Perm (Fin n)) :
    rawSift (t, encPerm n σ) = some (rawOne (encPerm n σ)) ↔ sift (decTable n t) σ = some 1 := by
  rw [rawSift_spec ht σ, rawOne_eq, length_encPerm]
  rcases h : sift (decTable n t) σ with _ | r
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro hr
      rw [encPerm_injective n hr]
    · intro hr; rw [hr]

/-! ## The shape of the accumulator

`RAM.PolyFun.foldlParam` bounds the accumulator from an **arbitrary** start, so the bound
cannot be read off the intended start `some σ`.  What saves it is the same structure lemma as
for the orbit loop: whatever the start, the residue has the length of the start and every one
of its entries is an entry of the start or an entry of the inverse of a table entry. -/

theorem mem_rawMul {a b : RawPerm} {x : ℕ} (h : x ∈ rawMul (a, b)) : x ∈ a ∨ x ∈ b := by
  rw [rawMul, List.mem_map] at h
  obtain ⟨j, hj, hx⟩ := h
  by_cases hlt : j < a.length
  · left
    rw [← hx]
    show a.getD j j ∈ a
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  · right
    have : x = j := by
      rw [← hx]
      show a.getD j j = j
      exact List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
    rw [this]
    exact hj

/-- **The shape of the accumulator along the sifting loop.** -/
theorem rawSiftFold_struct (t : RawTable) :
    ∀ (l : List ℕ) (r : RawPerm),
      List.foldl (fun acc i => rawSiftStep (t, (acc, i))) (some r) l = none ∨
      ∃ r', List.foldl (fun acc i => rawSiftStep (t, (acc, i))) (some r) l = some r' ∧
        r'.length = r.length ∧
        ∀ x ∈ r', x ∈ r ∨ ∃ τ, TableEntry t τ ∧ x ∈ rawInv τ := by
  intro l
  induction l with
  | nil => intro r; exact Or.inr ⟨r, rfl, rfl, fun x hx => Or.inl hx⟩
  | cons a s ih =>
      intro r
      rw [List.foldl_cons]
      rcases hstep : rawSiftStep (t, (some r, a)) with _ | r₁
      · left; exact rawSiftFold_none t s
      · have hr₁ : ∃ τ, TableEntry t τ ∧ r₁ = rawMul (rawInv τ, r) := by
          rcases hlook : rawTableGet (t, (a, rawApply (r, a))) with _ | τ
          · exfalso
            have : rawSiftStep (t, (some r, a)) = none := by
              show (match rawTableGet (t, (a, rawApply (r, a))) with
                  | none => none
                  | some τ => some (rawMul (rawInv τ, r))) = none
              rw [hlook]
            rw [this] at hstep
            exact absurd hstep (by simp)
          · refine ⟨τ, ⟨a, rawApply (r, a), hlook⟩, ?_⟩
            have : rawSiftStep (t, (some r, a)) = some (rawMul (rawInv τ, r)) := by
              show (match rawTableGet (t, (a, rawApply (r, a))) with
                  | none => none
                  | some τ => some (rawMul (rawInv τ, r))) = _
              rw [hlook]
            rw [this] at hstep
            exact (Option.some.inj hstep).symm
        obtain ⟨τ, hτ, hr₁eq⟩ := hr₁
        have hlen : r₁.length = r.length := by rw [hr₁eq, length_rawMul]
        have hmem : ∀ x ∈ r₁, x ∈ r ∨ ∃ τ, TableEntry t τ ∧ x ∈ rawInv τ := by
          intro x hx
          rw [hr₁eq] at hx
          rcases mem_rawMul hx with h | h
          · exact Or.inr ⟨τ, hτ, h⟩
          · exact Or.inl h
        rcases ih r₁ with h | ⟨r', hr', hlen', hmem'⟩
        · exact Or.inl h
        · refine Or.inr ⟨r', hr', by omega, ?_⟩
          intro x hx
          rcases hmem' x hx with h | h
          · exact hmem x h
          · exact Or.inr h

/-! ## The `PolyFun` statements -/

theorem polyFun_rawTableGet : PolyFun rawTableGet := by
  have hrow : PolyFun (fun p : RawTable × (ℕ × ℕ) => p.1.getD p.2.1 ([] : RawRow)) :=
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair
      (polyFun_nil (β := ℕ × RawPerm))).comp (polyFun_getD (α := RawRow))
  exact ((hrow.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_natLookup).of_eq (fun _ => rfl)

theorem polyFun_rawSiftStep : PolyFun rawSiftStep := by
  -- the inner case analysis: the table entry at the current position
  have hinner : PolyFun (fun z : RawPerm × (RawTable × ℕ) =>
      match rawTableGet (z.2.1, (z.2.2, rawApply (z.1, z.2.2))) with
      | none => none
      | some τ => some (rawMul (rawInv τ, z.1))) := by
    have hlook : PolyFun (fun z : RawPerm × (RawTable × ℕ) =>
        rawTableGet (z.2.1, (z.2.2, rawApply (z.1, z.2.2)))) :=
      ((polyFun_snd.comp polyFun_fst).pair
        ((polyFun_snd.comp polyFun_snd).pair
          ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawApply))).comp
        polyFun_rawTableGet
    have hsome : PolyFun (fun w : RawPerm × (RawPerm × (RawTable × ℕ)) =>
        (some (rawMul (rawInv w.1, w.2.1)) : Option RawPerm)) :=
      (((polyFun_fst.comp polyFun_rawInv).pair (polyFun_snd.comp polyFun_fst)).comp
        polyFun_rawMul).comp polyFun_some
    refine ((hlook.pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_none (β := RawPerm)) hsome)).of_eq (fun z => ?_)
    rcases rawTableGet (z.2.1, (z.2.2, rawApply (z.1, z.2.2))) with _ | τ <;> simp
  have hin : PolyFun (fun p : RawTable × (Option RawPerm × ℕ) =>
      ((p.2.1, ((p.1, p.2.2) : RawTable × ℕ)) : Option RawPerm × (RawTable × ℕ))) :=
    (polyFun_snd.comp polyFun_fst).pair (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))
  refine (hin.comp (PolyFun.optionElim (polyFun_none (β := RawPerm)) hinner)).of_eq
    (fun p => ?_)
  obtain ⟨t, o, i⟩ := p
  cases o <;> rfl

set_option maxHeartbeats 1000000 in
/-- **Sifting is a `RAM.PolyFun`.**  The accumulator is bounded by `Algo.rawSiftFold_struct`:
the residue is as long as the start, and its entries are entries of the start or of the inverse
of a table entry, whose size is bounded by the size bound of `Algo.rawInv`. -/
theorem polyFun_rawSift : PolyFun rawSift := by
  obtain ⟨c, d, hc⟩ := polyFun_rawInv.size
  have hacc : ∀ (cc : RawTable) (x : Option RawPerm) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawSiftStep (cc, (y, a))) x (r.take j))
        ≤ (fun m => 3 + m * (2 * (m + c * (m + 1) ^ d) + 1))
            (Enc.size ((cc, (x, r)) : RawTable × (Option RawPerm × List ℕ))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) : RawTable × (Option RawPerm × List ℕ)) with hN
    have hcc : Enc.size cc ≤ N := Combine.size_fst_le cc ((x, r) : Option RawPerm × List ℕ)
    have hxr : Enc.size ((x, r) : Option RawPerm × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : Option RawPerm × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hS : ∀ τ : RawPerm, TableEntry cc τ → ∀ y ∈ rawInv τ,
        Enc.size y ≤ N + c * (N + 1) ^ d := by
      intro τ hτ y hy
      have h1 : Enc.size y ≤ Enc.size (rawInv τ) := size_mem_le hy
      have h2 : Enc.size (rawInv τ) ≤ c * (Enc.size τ + 1) ^ d := hc τ
      have h3 : Enc.size τ ≤ N := le_trans (size_le_of_tableEntry hτ) hcc
      have h4 : (Enc.size τ + 1) ^ d ≤ (N + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      have h5 := Nat.mul_le_mul_left c h4
      omega
    rcases x with _ | r₀
    · rw [rawSiftFold_none]
      have : Enc.size (none : Option RawPerm) = 2 := size_none
      dsimp only
      omega
    · have hr₀ : Enc.size r₀ ≤ N := by
        have := size_some_eq r₀
        omega
      rcases rawSiftFold_struct cc (r.take j) r₀ with h | ⟨r', h, hlen, hmem⟩
      · rw [h]
        have : Enc.size (none : Option RawPerm) = 2 := size_none
        dsimp only
        omega
      · rw [h]
        have hentry : ∀ y ∈ r', Enc.size y ≤ N + c * (N + 1) ^ d := by
          intro y hy
          rcases hmem y hy with hy' | ⟨τ, hτ, hy'⟩
          · have h1 : Enc.size y ≤ Enc.size r₀ := size_mem_le hy'
            omega
          · exact hS τ hτ y hy'
        have hsize := size_list_le_of_entries r' (N + c * (N + 1) ^ d) hentry
        have hlen2 : r'.length ≤ N := by
          have h1 : r₀.length ≤ Enc.size r₀ := length_le_size r₀
          omega
        have hmul : r'.length * (2 * (N + c * (N + 1) ^ d) + 1)
            ≤ N * (2 * (N + c * (N + 1) ^ d) + 1) := Nat.mul_le_mul_right _ hlen2
        have hsome := size_some_eq r'
        dsimp only
        omega
  have hfold := PolyFun.foldlParam polyFun_rawSiftStep
    (p := fun m => 3 + m * (2 * (m + c * (m + 1) ^ d) + 1))
    ((polyBound_const 3).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_witness c d))).add
        (polyBound_const 1))))
    hacc
  have hin : PolyFun (fun p : RawTable × RawPerm =>
      ((p.1, ((some p.2 : Option RawPerm), List.range p.2.length)) :
        RawTable × (Option RawPerm × List ℕ))) :=
    polyFun_fst.pair ((polyFun_snd.comp polyFun_some).pair
      (polyFun_snd.comp polyFun_rangeLength))
  exact (hin.comp hfold).of_eq (fun p => rfl)

end Algo
