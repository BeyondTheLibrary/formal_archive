/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: building a complete sifting table (Schreier–Sims), as mathematics.
-/
import Workspace.Algo.ChainRaw

/-!
# Building a complete table

`Workspace/Algo/Chain.lean` proves the three textbook facts about a sifting table (membership,
the order, and the closure criterion `Algo.complete_of_closed`), and
`Workspace/Algo/ChainRaw.lean` runs the sifting loop on raw data.  What is still missing is the
table itself: the paper's Sec. 2.2.3 uses membership testing, the order and the transversals of
a permutation group as a black box ("A few well-known facts, cf. [Se]"), and
`Workspace/Algo/DESIGN.md`, item 2, class D, requires them to be **proved**, since the paper
cites no theorem.  This file is the second session of work package A4: the closure loop that
builds a complete table from a list of generators, as mathematics.  The same loop on raw data,
its `RAM.PolyFun`, and the membership test are in `Workspace/Algo/ChainBuildRaw.lean`.

## The table as a list

`Algo.Chain` works with a table as a *function* `Table n = ℕ → ℕ → Option (Equiv.Perm (Fin n))`.
A loop has to store one, so this file works with the same shape the raw routines use: a list of
rows, each row an association list from the image point to the permutation stored there
(`Algo.MTable n`), read by `Algo.tableOf`.  The insertion `Algo.insertRow` is defined on lists
of lists of *anything*, so the raw loop can reuse it verbatim and the simulation lemma of
`ChainBuildRaw` is an induction with no content.

## The loop

The work list holds permutations whose obligation to sift to the identity is not yet
discharged.  One round pops one of them, sifts it (`Algo.siftStuck`, which — unlike
`Algo.sift` — reports *where* the sift got stuck and with which residue), and:

* if it sifts through, the obligation is discharged and nothing else happens;
* if it gets stuck at level `i` with residue `ρ`, then `ρ` goes into the empty position
  `(i, ρ i)`, and the products of `ρ` with every entry of the new table, in both orders, go on
  the work list — these are exactly the new instances of the hypothesis `hprod` of
  `Algo.complete_of_closed`.

The loop stops when the work list is empty.  Sifting to the identity is **monotone** under
filling empty positions (`Algo.sift_mono`), so a discharged obligation stays discharged, and
the popped element itself is discharged by the very insertion that the round makes
(`Algo.siftAux_eq_one_of_insert`).

## Termination

Each insertion fills one position of an `n × n` grid, so there are at most `n²` of them, and
each adds at most `2n²` items to the work list.  The potential
`Algo.potential = (n² − #entries) · (2n² + 1) + #work` therefore drops at every round with a
nonempty work list, and `Algo.buildFuel n m = n²(2n² + 1) + m` rounds suffice
(`Algo.work_eq_nil_of_potential_le`).  The fuel is a *number of rounds*, not a bound proved
after the fact: the loop is literally `Algo.buildRound^[Algo.buildFuel n gens.length]`.

## Main results

* `Algo.isTable_buildTable`, `Algo.diag_buildTable` — the invariant;
* `Algo.complete_buildTable` — the table built is complete for `⟨gens⟩`;
* `Algo.mem_iff_sift_buildTable` — membership by sifting through it;
* `Algo.card_eq_prod_row_card_buildTable` — the order, from `Algo.card_eq_prod_row_card`.

No axiom, no `sorry`, and no running-time claim: that is `ChainBuildRaw.lean`.
-/

namespace Algo

open Equiv (Perm)
open RAM RAM.Targets

variable {n : ℕ}

/-! ## Insertion into a list of lists

`Algo.insertRow i M q` puts `q` at the front of the `i`-th row of `M`, creating the row (and the
rows before it) if `M` is too short.  It is stated for an arbitrary entry type so that the raw
loop can use the very same function. -/

/-- **Insertion into a list of lists.**  `insertRow i M q` puts `q` at the front of row `i`,
extending `M` with empty rows if it is too short. -/
def insertRow {β : Type*} : ℕ → List (List β) → β → List (List β)
  | 0, M, q => (q :: M.headD []) :: M.tail
  | (i + 1), M, q => M.headD [] :: insertRow i M.tail q

section InsertRow

variable {β : Type*}

theorem headD_append_tail_flatten (M : List (List β)) :
    M.headD [] ++ M.tail.flatten = M.flatten := by
  cases M with
  | nil => rfl
  | cons a l => rfl

theorem headD_eq_getD (M : List (List β)) : M.headD [] = M.getD 0 [] := by
  cases M with
  | nil => rfl
  | cons a l => rfl

theorem tail_getD (M : List (List β)) (i : ℕ) : M.tail.getD i [] = M.getD (i + 1) [] := by
  cases M with
  | nil => rfl
  | cons a l => rfl

/-- **What insertion does to the rows.** -/
theorem insertRow_getD (q : β) : ∀ (i i' : ℕ) (M : List (List β)),
    (insertRow i M q).getD i' [] = if i' = i then q :: M.getD i [] else M.getD i' [] := by
  intro i
  induction i with
  | zero =>
      intro i' M
      cases i' with
      | zero => rw [insertRow, List.getD_cons_zero, if_pos rfl, headD_eq_getD]
      | succ m =>
          rw [insertRow, List.getD_cons_succ, if_neg (by omega), tail_getD]
  | succ i ih =>
      intro i' M
      cases i' with
      | zero =>
          rw [insertRow, List.getD_cons_zero, if_neg (by omega), headD_eq_getD]
      | succ m =>
          rw [insertRow, List.getD_cons_succ, ih m M.tail, tail_getD, tail_getD]
          by_cases h : m = i
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]

/-- Insertion adds exactly one entry. -/
theorem length_flatten_insertRow (q : β) : ∀ (i : ℕ) (M : List (List β)),
    (insertRow i M q).flatten.length = M.flatten.length + 1 := by
  intro i
  induction i with
  | zero =>
      intro M
      show ((q :: M.headD []) ++ M.tail.flatten).length = _
      rw [← headD_append_tail_flatten M]
      simp only [List.length_append, List.length_cons]
      omega
  | succ i ih =>
      intro M
      show (M.headD [] ++ (insertRow i M.tail q).flatten).length = _
      rw [List.length_append, ih M.tail, ← headD_append_tail_flatten M]
      simp only [List.length_append]
      omega

/-- Insertion adds exactly one entry, as a membership statement. -/
theorem mem_flatten_insertRow {q : β} {x : β} : ∀ (i : ℕ) (M : List (List β)),
    x ∈ (insertRow i M q).flatten ↔ x = q ∨ x ∈ M.flatten := by
  intro i
  induction i with
  | zero =>
      intro M
      show x ∈ ((q :: M.headD []) ++ M.tail.flatten) ↔ _
      rw [List.mem_append, List.mem_cons, ← headD_append_tail_flatten M, List.mem_append]
      tauto
  | succ i ih =>
      intro M
      show x ∈ (M.headD [] ++ (insertRow i M.tail q).flatten) ↔ _
      rw [List.mem_append, ih M.tail, ← headD_append_tail_flatten M, List.mem_append]
      tauto

/-- Insertion never shortens the table. -/
theorem length_le_insertRow (q : β) : ∀ (i : ℕ) (M : List (List β)),
    M.length ≤ (insertRow i M q).length := by
  intro i
  induction i with
  | zero =>
      intro M
      show M.length ≤ M.tail.length + 1
      cases M with
      | nil => simp
      | cons a l => simp
  | succ i ih =>
      intro M
      show M.length ≤ (insertRow i M.tail q).length + 1
      have h1 := ih M.tail
      cases M with
      | nil => simp
      | cons a l => simp at h1 ⊢; omega

/-- Insertion creates at most the rows up to `i`. -/
theorem length_insertRow (q : β) : ∀ (i : ℕ) (M : List (List β)),
    (insertRow i M q).length ≤ max M.length (i + 1) := by
  intro i
  induction i with
  | zero =>
      intro M
      show (M.tail.length + 1) ≤ _
      cases M with
      | nil => simp
      | cons a l => simp
  | succ i ih =>
      intro M
      show ((insertRow i M.tail q).length + 1) ≤ _
      have := ih M.tail
      cases M with
      | nil => simp at this ⊢; omega
      | cons a l => simp at this ⊢; omega

/-- **Insertion into an existing row does not change the number of rows.**  This is what makes
the raw loop implementable without a recursion on a machine natural: see
`Algo.rawInsert_eq` in `Workspace/Algo/ChainBuildRaw.lean`. -/
theorem length_insertRow_eq (q : β) (i : ℕ) (M : List (List β)) (h : i < M.length) :
    (insertRow i M q).length = M.length := by
  have h1 := length_insertRow q i M
  have h2 := length_le_insertRow q i M
  have h3 : max M.length (i + 1) = M.length := by omega
  omega

/-- A row of the new table is the new row, a row of the old one, or an empty row created on the
way (which is why the empty case cannot be dropped: `insertRow 1 [] q = [[], [q]]`). -/
theorem mem_insertRow (q : β) : ∀ (i : ℕ) (M : List (List β)) (r : List β),
    r ∈ insertRow i M q → r = q :: M.getD i [] ∨ r ∈ M ∨ r = [] := by
  intro i
  induction i with
  | zero =>
      intro M r hr
      rw [insertRow, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Or.inl (by rw [headD_eq_getD])
      · exact Or.inr (Or.inl (List.mem_of_mem_tail hr))
  | succ i ih =>
      intro M r hr
      rw [insertRow, List.mem_cons] at hr
      rcases hr with rfl | hr
      · cases M with
        | nil => exact Or.inr (Or.inr rfl)
        | cons a l => exact Or.inr (Or.inl (List.mem_cons_self ..))
      · rcases ih M.tail r hr with h | h | h
        · exact Or.inl (by rw [h, tail_getD])
        · exact Or.inr (Or.inl (List.mem_of_mem_tail h))
        · exact Or.inr (Or.inr h)

end InsertRow

/-! ## The table as a list of association lists -/

/-- One row of a table, as stored: the permutations at the positions `(i, j)`, listed by `j`. -/
abbrev MRow (n : ℕ) := List (ℕ × Perm (Fin n))

/-- A stored table: one row per level. -/
abbrev MTable (n : ℕ) := List (MRow n)

/-- **The table a stored table describes.** -/
def tableOf (M : MTable n) : Table n := fun i j => (M.getD i []).lookup j

/-- The list of the permutations stored in a table. -/
def entriesList (M : MTable n) : List (Perm (Fin n)) := M.flatten.map Prod.snd

theorem mem_entriesList {M : MTable n} {τ : Perm (Fin n)} {j : ℕ} (h : (j, τ) ∈ M.flatten) :
    τ ∈ entriesList M := List.mem_map.2 ⟨(j, τ), h, rfl⟩

theorem lookup_mem {M : MTable n} {i j : ℕ} {τ : Perm (Fin n)} (h : tableOf M i j = some τ) :
    (j, τ) ∈ M.flatten := by
  have h1 : (j, τ) ∈ M.getD i ([] : MRow n) := mem_of_lookup_eq_some _ _ _ h
  have h2 : M.getD i ([] : MRow n) ∈ M := by
    by_cases hi : i < M.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at h1
      exact absurd h1 (by simp)
  exact List.mem_flatten.2 ⟨_, h2, h1⟩

/-- Every entry the table *shows* is stored in it. -/
theorem allEntries_subset_entriesList {M : MTable n} {τ : Perm (Fin n)}
    (h : τ ∈ AllEntries (tableOf M)) : τ ∈ entriesList M := by
  obtain ⟨i, j, hij⟩ := h
  exact mem_entriesList (lookup_mem hij)

/-! ### Insertion

The two facts the loop needs: the new position shows the new entry, and every other position is
unchanged. -/

theorem tableOf_insertRow_self (M : MTable n) (i j : ℕ) (τ : Perm (Fin n)) :
    tableOf (insertRow i M (j, τ)) i j = some τ := by
  rw [tableOf, insertRow_getD, if_pos rfl]
  simp [List.lookup]

theorem tableOf_insertRow_other (M : MTable n) {i j : ℕ} (τ : Perm (Fin n)) {i' j' : ℕ}
    (h : ¬(i' = i ∧ j' = j)) : tableOf (insertRow i M (j, τ)) i' j' = tableOf M i' j' := by
  rw [tableOf, tableOf, insertRow_getD]
  by_cases hi : i' = i
  · subst hi
    rw [if_pos rfl]
    have hj : ¬ (j' = j) := fun hj => h ⟨rfl, hj⟩
    have hbeq : (j' == j) = false := by simpa using hj
    show (List.lookup j' ((j, τ) :: M.getD i' [])) = _
    simp [List.lookup, hbeq]
  · rw [if_neg hi]

/-- The entry of the new table at a position is the new one, or the old entry there. -/
theorem tableOf_insertRow_eq_some {M : MTable n} {i j : ℕ} {τ : Perm (Fin n)} {i' j' : ℕ}
    {σ : Perm (Fin n)} (h : tableOf (insertRow i M (j, τ)) i' j' = some σ) :
    σ = τ ∨ tableOf M i' j' = some σ := by
  by_cases hc : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := hc
    rw [tableOf_insertRow_self] at h
    exact Or.inl (Option.some.inj h).symm
  · rw [tableOf_insertRow_other M τ hc] at h
    exact Or.inr h

/-! ## Monotonicity of sifting

Filling an empty position never changes the result of a sift that already succeeded: the path a
successful sift takes only visits filled positions, and those are unchanged. -/

/-- `T'` **extends** `T`: every filled position of `T` is filled the same way in `T'`. -/
def Extends (T T' : Table n) : Prop := ∀ i j τ, T i j = some τ → T' i j = some τ

theorem extends_refl (T : Table n) : Extends T T := fun _ _ _ h => h

/-- **Sifting is monotone under extension.** -/
theorem siftAux_mono {T T' : Table n} (h : Extends T T') :
    ∀ (k i : ℕ) (r x : Perm (Fin n)), siftAux T k i r = some x → siftAux T' k i r = some x := by
  intro k
  induction k with
  | zero => intro i r x h'; exact h'
  | succ k ih =>
      intro i r x h'
      rcases hT : T i (evalAt r i) with _ | τ
      · rw [siftAux_succ_of_none hT] at h'; exact absurd h' (by simp)
      · rw [siftAux_succ_of_some hT] at h'
        rw [siftAux_succ_of_some (h _ _ _ hT)]
        exact ih (i + 1) _ x h'

theorem sift_mono {T T' : Table n} (h : Extends T T') {σ : Perm (Fin n)}
    (hσ : sift T σ = some 1) : sift T' σ = some 1 := siftAux_mono h n 0 σ 1 hσ

/-- Inserting into an empty position extends the table. -/
theorem extends_insertRow (M : MTable n) {i j : ℕ} (hij : tableOf M i j = none)
    (τ : Perm (Fin n)) : Extends (tableOf M) (tableOf (insertRow i M (j, τ))) := by
  intro i' j' σ h
  by_cases hc : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := hc
    rw [hij] at h
    exact absurd h (by simp)
  · rw [tableOf_insertRow_other M τ hc]
    exact h

/-! ## Sifting that reports where it got stuck

`Algo.sift` answers `none` when a position is empty, which is all the *criterion* needs.  The
loop needs more: the level at which the sift stopped and the residue there, because that residue
is what is inserted.  Point 2 of the note of work package A4, session 1, in
`Workspace/Algo/DESIGN.md` explains why `Algo.sift` may not return the residue itself. -/

/-- **Sifting with a report.**  `none` means the sift went through; `some (i, ρ)` means it
stopped at the level `i` with residue `ρ`, at an empty position. -/
def siftStuckAux (T : Table n) : ℕ → ℕ → Perm (Fin n) → Option (ℕ × Perm (Fin n))
  | 0, _, _ => none
  | (k + 1), i, r =>
      match T i (evalAt r i) with
      | none => some (i, r)
      | some τ => siftStuckAux T k (i + 1) (τ⁻¹ * r)

/-- **Sifting with a report**, all `n` levels from the level `0`. -/
def siftStuck (T : Table n) (σ : Perm (Fin n)) : Option (ℕ × Perm (Fin n)) :=
  siftStuckAux T n 0 σ

theorem siftStuckAux_succ_of_none {T : Table n} {k i : ℕ} {r : Perm (Fin n)}
    (h : T i (evalAt r i) = none) : siftStuckAux T (k + 1) i r = some (i, r) := by
  show (match T i (evalAt r i) with
      | none => some (i, r)
      | some τ => siftStuckAux T k (i + 1) (τ⁻¹ * r)) = _
  rw [h]

theorem siftStuckAux_succ_of_some {T : Table n} {k i : ℕ} {r τ : Perm (Fin n)}
    (h : T i (evalAt r i) = some τ) :
    siftStuckAux T (k + 1) i r = siftStuckAux T k (i + 1) (τ⁻¹ * r) := by
  show (match T i (evalAt r i) with
      | none => some (i, r)
      | some τ => siftStuckAux T k (i + 1) (τ⁻¹ * r)) = _
  rw [h]

/-- **A sift that reports nothing is a sift that goes through.** -/
theorem siftAux_ne_none_of_siftStuckAux_none {T : Table n} :
    ∀ (k i : ℕ) (r : Perm (Fin n)), siftStuckAux T k i r = none → siftAux T k i r ≠ none := by
  intro k
  induction k with
  | zero => intro i r _; simp [siftAux]
  | succ k ih =>
      intro i r h
      rcases hT : T i (evalAt r i) with _ | τ
      · rw [siftStuckAux_succ_of_none hT] at h; exact absurd h (by simp)
      · rw [siftStuckAux_succ_of_some hT] at h
        rw [siftAux_succ_of_some hT]
        exact ih (i + 1) _ h

/-- **What the report says.**  The reported position is empty, the reported level is within the
range walked, the residue differs from the input by an element of the group generated by the
entries, and the residue fixes every level below the reported one. -/
theorem siftStuckAux_spec {T : Table n} :
    ∀ (k i : ℕ) (r : Perm (Fin n)) (i' : ℕ) (ρ : Perm (Fin n)),
      siftStuckAux T k i r = some (i', ρ) →
        T i' (evalAt ρ i') = none ∧ i ≤ i' ∧ i' < i + k ∧
          (∃ p ∈ Subgroup.closure (AllEntries T), ρ = p * r) := by
  intro k
  induction k with
  | zero => intro i r i' ρ h; exact absurd h (by simp [siftStuckAux])
  | succ k ih =>
      intro i r i' ρ h
      rcases hT : T i (evalAt r i) with _ | τ
      · rw [siftStuckAux_succ_of_none hT] at h
        obtain ⟨hi, hr⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
        subst hi; subst hr
        exact ⟨hT, le_refl _, by omega, 1, Subgroup.one_mem _, by simp⟩
      · rw [siftStuckAux_succ_of_some hT] at h
        obtain ⟨h1, h2, h3, p, hp, hρ⟩ := ih (i + 1) _ i' ρ h
        refine ⟨h1, by omega, by omega, p * τ⁻¹, ?_, ?_⟩
        · exact Subgroup.mul_mem _ hp
            (Subgroup.inv_mem _ (Subgroup.subset_closure (mem_allEntries hT)))
        · rw [hρ, mul_assoc]

/-- The residue fixes every level below the one where the sift stopped. -/
theorem siftStuckAux_fixes {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G) :
    ∀ (k i : ℕ) (r : Perm (Fin n)) (i' : ℕ) (ρ : Perm (Fin n)), Fixes i r →
      siftStuckAux T k i r = some (i', ρ) → Fixes i' ρ := by
  intro k
  induction k with
  | zero => intro i r i' ρ _ h; exact absurd h (by simp [siftStuckAux])
  | succ k ih =>
      intro i r i' ρ hfix h
      rcases hT2 : T i (evalAt r i) with _ | τ
      · rw [siftStuckAux_succ_of_none hT2] at h
        obtain ⟨hi, hr⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
        subst hi; subst hr; exact hfix
      · rw [siftStuckAux_succ_of_some hT2] at h
        refine ih (i + 1) _ i' ρ ?_ h
        refine fixes_of_evalAt ?_
        intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm' | rfl
        · rw [evalAt_mul, hfix.evalAt hm', (hT.fixes hT2).inv.evalAt hm']
        · rw [evalAt_mul, ← hT.img hT2, evalAt_inv_left]

/-- **The insertion discharges the obligation of the element that caused it.**  If the sift of
`r` stops at the level `i'` with residue `ρ`, and the new table has `ρ` at the position where it
stopped (and the identity on its diagonal), then `r` sifts to the identity through the new
table. -/
theorem siftAux_eq_one_of_insert {T T' : Table n} (hext : Extends T T')
    (hdiag : ∀ m < n, T' m m = some 1) :
    ∀ (k i : ℕ), i + k ≤ n → ∀ (r : Perm (Fin n)) (i' : ℕ) (ρ : Perm (Fin n)),
      siftStuckAux T k i r = some (i', ρ) → T' i' (evalAt ρ i') = some ρ →
        siftAux T' k i r = some 1 := by
  intro k
  induction k with
  | zero => intro i _ r i' ρ h _; exact absurd h (by simp [siftStuckAux])
  | succ k ih =>
      intro i hi r i' ρ h hnew
      rcases hT : T i (evalAt r i) with _ | τ
      · rw [siftStuckAux_succ_of_none hT] at h
        obtain ⟨hii, hrr⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
        subst hii; subst hrr
        rw [siftAux_succ_of_some hnew, inv_mul_cancel]
        exact one_mem_sifted hdiag k (i + 1) (by omega)
      · rw [siftStuckAux_succ_of_some hT] at h
        rw [siftAux_succ_of_some (hext _ _ _ hT)]
        exact ih (i + 1) (by omega) _ i' ρ h hnew

/-! ## The state of the loop, and its invariants -/

/-- The state of the closure loop: the table built so far, and the work list of permutations
whose obligation to sift to the identity is not yet discharged. -/
abbrev BuildState (n : ℕ) := MTable n × List (Perm (Fin n))

/-- **The shape invariant**, which is what bounds the size of the table: at most `n` rows, the
keys of a row pairwise distinct and below `n`. -/
structure Shape (n : ℕ) (M : MTable n) : Prop where
  rows : M.length ≤ n
  nodup : ∀ r ∈ M, (r.map Prod.fst).Nodup
  keys : ∀ r ∈ M, ∀ q ∈ r, q.1 < n

/-- **The mathematical invariant.**  `S` is the generating set. -/
structure Good (G : Subgroup (Perm (Fin n))) (S : Set (Perm (Fin n))) (st : BuildState n) :
    Prop where
  isTable : IsTable (tableOf st.1) G
  diag : ∀ i < n, tableOf st.1 i i = some 1
  entriesMem : ∀ e ∈ entriesList st.1, e ∈ G
  workMem : ∀ g ∈ st.2, g ∈ G
  gens : ∀ g ∈ S, sift (tableOf st.1) g = some 1 ∨ g ∈ st.2
  prods : ∀ τ ∈ AllEntries (tableOf st.1), ∀ ρ ∈ AllEntries (tableOf st.1),
    sift (tableOf st.1) (τ * ρ) = some 1 ∨ τ * ρ ∈ st.2

/-! ## The round -/

/-- The products of a new entry with every entry of the table, in both orders: exactly the new
instances of the hypothesis `hprod` of `Algo.complete_of_closed`. -/
def newItems (M : MTable n) (ρ : Perm (Fin n)) : List (Perm (Fin n)) :=
  (entriesList M).flatMap (fun e => [ρ * e, e * ρ])

theorem length_flatMap_pair {α β : Type*} (f g : α → β) : ∀ l : List α,
    (l.flatMap (fun e => [f e, g e])).length = 2 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      simp
      omega

theorem length_newItems (M : MTable n) (ρ : Perm (Fin n)) :
    (newItems M ρ).length = 2 * M.flatten.length := by
  rw [newItems, length_flatMap_pair, entriesList, List.length_map]

theorem mem_newItems {M : MTable n} {ρ x : Perm (Fin n)} (h : x ∈ newItems M ρ) :
    ∃ e ∈ entriesList M, x = ρ * e ∨ x = e * ρ := by
  rw [newItems, List.mem_flatMap] at h
  obtain ⟨e, he, hx⟩ := h
  refine ⟨e, he, ?_⟩
  rcases List.mem_cons.1 hx with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

theorem mem_newItems_of {M : MTable n} {ρ e : Perm (Fin n)} (he : e ∈ entriesList M) :
    ρ * e ∈ newItems M ρ ∧ e * ρ ∈ newItems M ρ :=
  ⟨List.mem_flatMap.2 ⟨e, he, by simp⟩, List.mem_flatMap.2 ⟨e, he, by simp⟩⟩

/-- **One round of the closure loop.** -/
def buildRound (st : BuildState n) : BuildState n :=
  match st.2 with
  | [] => st
  | g :: rest =>
      match siftStuck (tableOf st.1) g with
      | none => (st.1, rest)
      | some (i, ρ) =>
          let M' := insertRow i st.1 (evalAt ρ i, ρ)
          (M', rest ++ newItems M' ρ)

theorem buildRound_nil (M : MTable n) : buildRound (M, ([] : List (Perm (Fin n)))) = (M, []) :=
  rfl

theorem buildRound_cons_none {M : MTable n} {g : Perm (Fin n)} {rest : List (Perm (Fin n))}
    (h : siftStuck (tableOf M) g = none) : buildRound (M, g :: rest) = (M, rest) := by
  show (match siftStuck (tableOf M) g with
      | none => (M, rest)
      | some (i, ρ) => (insertRow i M (evalAt ρ i, ρ),
          rest ++ newItems (insertRow i M (evalAt ρ i, ρ)) ρ)) = _
  rw [h]

theorem buildRound_cons_some {M : MTable n} {g : Perm (Fin n)} {rest : List (Perm (Fin n))}
    {i : ℕ} {ρ : Perm (Fin n)} (h : siftStuck (tableOf M) g = some (i, ρ)) :
    buildRound (M, g :: rest)
      = (insertRow i M (evalAt ρ i, ρ),
          rest ++ newItems (insertRow i M (evalAt ρ i, ρ)) ρ) := by
  show (match siftStuck (tableOf M) g with
      | none => (M, rest)
      | some (i, ρ) => (insertRow i M (evalAt ρ i, ρ),
          rest ++ newItems (insertRow i M (evalAt ρ i, ρ)) ρ)) = _
  rw [h]

/-! ## Reading the report of `Algo.siftStuck` -/

section Report

variable {G : Subgroup (Perm (Fin n))} {S : Set (Perm (Fin n))}

/-- The report of a full sift: the reported position is empty, the reported level is below the
degree, and the residue lies in `G` whenever the input does. -/
theorem siftStuck_spec {T : Table n} {σ : Perm (Fin n)} {i : ℕ} {ρ : Perm (Fin n)}
    (h : siftStuck T σ = some (i, ρ)) :
    T i (evalAt ρ i) = none ∧ i < n ∧ ∃ p ∈ Subgroup.closure (AllEntries T), ρ = p * σ := by
  obtain ⟨h1, _, h3, hp⟩ := siftStuckAux_spec n 0 σ i ρ h
  exact ⟨h1, by omega, hp⟩

theorem siftStuck_mem {T : Table n} (hT : IsTable T G) {σ : Perm (Fin n)} (hσ : σ ∈ G) {i : ℕ}
    {ρ : Perm (Fin n)} (h : siftStuck T σ = some (i, ρ)) : ρ ∈ G := by
  obtain ⟨-, -, p, hp, hρ⟩ := siftStuck_spec h
  rw [hρ]
  exact G.mul_mem (closure_allEntries_le hT hp) hσ

theorem siftStuck_fixes {T : Table n} (hT : IsTable T G) {σ : Perm (Fin n)} {i : ℕ}
    {ρ : Perm (Fin n)} (h : siftStuck T σ = some (i, ρ)) : Fixes i ρ :=
  siftStuckAux_fixes hT n 0 σ i ρ (fun k hk => absurd hk (by omega)) h

/-- **A sift that reports nothing is a sift to the identity.** -/
theorem sift_eq_one_of_siftStuck_none {T : Table n} (hT : IsTable T G) {σ : Perm (Fin n)}
    (h : siftStuck T σ = none) : sift T σ = some 1 := by
  have h1 : siftAux T n 0 σ ≠ none := siftAux_ne_none_of_siftStuckAux_none n 0 σ h
  rcases hs : sift T σ with _ | r
  · exact absurd hs h1
  · rw [sift_eq_some_eq_one hT hs]

end Report

/-! ## The shape invariant -/

theorem key_ne_of_lookup_none : ∀ (l : MRow n) (j : ℕ), l.lookup j = none → ∀ q ∈ l, q.1 ≠ j := by
  intro l
  induction l with
  | nil => intro j _ q hq; exact absurd hq (by simp)
  | cons a t ih =>
      intro j h q hq
      obtain ⟨k, v⟩ := a
      by_cases hjk : j = k
      · subst hjk
        exact absurd h (by simp [List.lookup])
      · have hbeq : (j == k) = false := by simpa using hjk
        have h' : t.lookup j = none := by simpa [List.lookup, hbeq] using h
        rcases List.mem_cons.1 hq with rfl | hq'
        · exact fun hc => hjk hc.symm
        · exact ih j h' q hq'

theorem getD_mem_or_nil (M : MTable n) (i : ℕ) :
    M.getD i ([] : MRow n) ∈ M ∨ M.getD i ([] : MRow n) = [] := by
  by_cases hi : i < M.length
  · left; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · right; exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)

theorem length_le_of_nodup_lt {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  classical
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  have h2 : l.toFinset ⊆ Finset.range n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.2 (hlt x hx)
  have h3 := Finset.card_le_card h2
  rw [h1, Finset.card_range] at h3
  exact h3

theorem length_flatten_le_mul : ∀ (M : MTable n), (∀ r ∈ M, r.length ≤ n) →
    M.flatten.length ≤ M.length * n := by
  intro M
  induction M with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      have h1 : a.length ≤ n := h a (List.mem_cons_self ..)
      have h2 := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      show (a ++ l.flatten).length ≤ _
      rw [List.length_append, List.length_cons]
      have : (l.length + 1) * n = l.length * n + n := by ring
      omega

/-- **The shape invariant bounds the number of entries** by `n²`. -/
theorem length_flatten_le_of_shape {M : MTable n} (h : Shape n M) : M.flatten.length ≤ n * n := by
  have hrow : ∀ r ∈ M, r.length ≤ n := by
    intro r hr
    have hnd := h.nodup r hr
    have hlt : ∀ x ∈ r.map Prod.fst, x < n := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h.keys r hr q hq
    have := length_le_of_nodup_lt hnd hlt
    rwa [List.length_map] at this
  have h1 := length_flatten_le_mul M hrow
  have h2 : M.length * n ≤ n * n := Nat.mul_le_mul_right n h.rows
  omega

/-- **Inserting at an empty position preserves the shape.** -/
theorem shape_insertRow {M : MTable n} (hM : Shape n M) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hnone : tableOf M i j = none) (τ : Perm (Fin n)) : Shape n (insertRow i M (j, τ)) := by
  have hkey : ∀ q ∈ M.getD i ([] : MRow n), q.1 ≠ j := key_ne_of_lookup_none _ j hnone
  have hold : ∀ q ∈ M.getD i ([] : MRow n), q.1 < n := by
    intro q hq
    rcases getD_mem_or_nil M i with h | h
    · exact hM.keys _ h q hq
    · rw [h] at hq; exact absurd hq (by simp)
  refine ⟨?_, ?_, ?_⟩
  · have h1 := length_insertRow ((j, τ) : ℕ × Perm (Fin n)) i M
    have h2 := hM.rows
    omega
  · intro r hr
    rcases mem_insertRow ((j, τ) : ℕ × Perm (Fin n)) i M r hr with rfl | h | rfl
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hmem
        obtain ⟨q, hq, hq2⟩ := List.mem_map.1 hmem
        exact hkey q hq hq2
      · rcases getD_mem_or_nil M i with h | h
        · exact hM.nodup _ h
        · rw [h]; simp
    · exact hM.nodup r h
    · simp
  · intro r hr q hq
    rcases mem_insertRow ((j, τ) : ℕ × Perm (Fin n)) i M r hr with rfl | h | rfl
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact hj
      · exact hold q hq'
    · exact hM.keys r h q hq
    · exact absurd hq (by simp)

/-- **The round preserves the shape.** -/
theorem shape_buildRound (M : MTable n) (w : List (Perm (Fin n))) (hsh : Shape n M) :
    Shape n (buildRound (M, w)).1 := by
  cases w with
  | nil => rw [buildRound_nil]; exact hsh
  | cons g rest =>
      rcases hst : siftStuck (tableOf M) g with _ | ⟨i, ρ⟩
      · rw [buildRound_cons_none hst]; exact hsh
      · rw [buildRound_cons_some hst]
        obtain ⟨hnone, hi, -⟩ := siftStuck_spec hst
        exact shape_insertRow hsh hi (evalAt_lt ρ hi) hnone ρ

/-- **The number of rows never changes.**  It is `n` from the start (`Algo.initTable`), and the
loop only ever inserts at a level below `n`.  The raw loop needs this: its insertion is a `map`
over the rows, which cannot create a row. -/
theorem length_buildRound (M : MTable n) (w : List (Perm (Fin n))) (h : M.length = n) :
    (buildRound (M, w)).1.length = n := by
  cases w with
  | nil => rw [buildRound_nil]; exact h
  | cons g rest =>
      rcases hst : siftStuck (tableOf M) g with _ | ⟨i, ρ⟩
      · rw [buildRound_cons_none hst]; exact h
      · rw [buildRound_cons_some hst]
        obtain ⟨-, hi, -⟩ := siftStuck_spec hst
        show (insertRow i M ((evalAt ρ i, ρ) : ℕ × Perm (Fin n))).length = n
        rw [length_insertRow_eq _ i M (by omega)]
        exact h

theorem length_buildRound_iterate : ∀ (f : ℕ) (M : MTable n) (w : List (Perm (Fin n))),
    M.length = n → (buildRound^[f] (M, w)).1.length = n := by
  intro f
  induction f with
  | zero => intro M w h; exact h
  | succ f ih =>
      intro M w h
      rw [Function.iterate_succ_apply]
      exact ih (buildRound (M, w)).1 (buildRound (M, w)).2 (length_buildRound M w h)

/-! ## The round preserves the mathematical invariant -/

section Good

variable {G : Subgroup (Perm (Fin n))} {S : Set (Perm (Fin n))}

theorem mem_entriesList_insertRow {M : MTable n} {i j : ℕ} {τ e : Perm (Fin n)}
    (h : e ∈ entriesList (insertRow i M (j, τ))) : e = τ ∨ e ∈ entriesList M := by
  rw [entriesList, List.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  rcases mem_flatten_insertRow i M |>.1 hq with rfl | hq'
  · exact Or.inl rfl
  · exact Or.inr (mem_entriesList hq')

/-- **The round preserves the invariant.** -/
theorem good_buildRound {M : MTable n} {w : List (Perm (Fin n))} (hg : Good G S (M, w)) :
    Good G S (buildRound (M, w)) := by
  cases w with
  | nil => rw [buildRound_nil]; exact hg
  | cons g rest =>
      have hT : IsTable (tableOf M) G := hg.isTable
      have hgG : g ∈ G := hg.workMem g (List.mem_cons_self ..)
      rcases hst : siftStuck (tableOf M) g with _ | ⟨i, ρ⟩
      · -- the popped element sifts through: its obligation is discharged
        rw [buildRound_cons_none hst]
        have hgs : sift (tableOf M) g = some 1 := sift_eq_one_of_siftStuck_none hT hst
        refine ⟨hg.isTable, hg.diag, hg.entriesMem, ?_, ?_, ?_⟩
        · exact fun x hx => hg.workMem x (List.mem_cons_of_mem _ hx)
        · intro x hx
          rcases hg.gens x hx with h | h
          · exact Or.inl h
          · rcases List.mem_cons.1 h with rfl | h'
            · exact Or.inl hgs
            · exact Or.inr h'
        · intro τ hτ ρ hρ
          rcases hg.prods τ hτ ρ hρ with h | h
          · exact Or.inl h
          · rcases List.mem_cons.1 h with h' | h'
            · exact Or.inl (by rw [h']; exact hgs)
            · exact Or.inr h'
      · -- the popped element gets stuck: insert the residue
        rw [buildRound_cons_some hst]
        obtain ⟨hnone, hi, -⟩ := siftStuck_spec hst
        have hρG : ρ ∈ G := siftStuck_mem hT hgG hst
        have hfix : Fixes i ρ := siftStuck_fixes hT hst
        have hjn : evalAt ρ i < n := evalAt_lt ρ hi
        obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = evalAt ρ i := ⟨_, rfl⟩
        rw [← hjdef]
        rw [← hjdef] at hnone hjn
        obtain ⟨M', hM'⟩ : ∃ M' : MTable n, M' = insertRow i M (j, ρ) := ⟨_, rfl⟩
        rw [← hM']
        have hext : Extends (tableOf M) (tableOf M') := by
          rw [hM']; exact extends_insertRow M hnone ρ
        have hself : tableOf M' i j = some ρ := by
          rw [hM']; exact tableOf_insertRow_self M i j ρ
        have hother : ∀ (i' j' : ℕ), ¬(i' = i ∧ j' = j) →
            tableOf M' i' j' = tableOf M i' j' := by
          intro i' j' hc
          rw [hM']; exact tableOf_insertRow_other M ρ hc
        -- the diagonal survives: the filled position is off the diagonal
        have hoff : j ≠ i := by
          intro hc
          have hdi : tableOf M i i = some (1 : Perm (Fin n)) := hg.diag i hi
          rw [hc, hdi] at hnone
          exact absurd hnone (by simp)
        have hdiag' : ∀ m < n, tableOf M' m m = some 1 := by
          intro m hm
          have hc : ¬(m = i ∧ m = j) := by
            rintro ⟨h1, h2⟩
            exact hoff (h2.symm.trans h1)
          rw [hother m m hc]
          exact hg.diag m hm
        -- the new table is a table for `G`
        have hkey : ∀ (i' j' : ℕ) (σ' : Perm (Fin n)), tableOf M' i' j' = some σ' →
            σ' ∈ G ∧ Fixes i' σ' ∧ evalAt σ' i' = j' := by
          intro i' j' σ' h
          by_cases hc : i' = i ∧ j' = j
          · obtain ⟨rfl, rfl⟩ := hc
            rw [hself] at h
            have : σ' = ρ := (Option.some.inj h).symm
            subst this
            exact ⟨hρG, hfix, hjdef.symm⟩
          · rw [hother i' j' hc] at h
            exact ⟨hT.mem h, hT.fixes h, hT.img h⟩
        have hT' : IsTable (tableOf M') G :=
          ⟨fun h => (hkey _ _ _ h).1, fun h => (hkey _ _ _ h).2.1, fun h => (hkey _ _ _ h).2.2⟩
        -- the popped element now sifts through
        have hgsift : sift (tableOf M') g = some 1 :=
          siftAux_eq_one_of_insert hext hdiag' n 0 (by omega) g i ρ hst
            (by rw [← hjdef]; exact hself)
        have hentries : ∀ e ∈ entriesList M', e ∈ G := by
          intro e he
          rw [hM'] at he
          rcases mem_entriesList_insertRow he with rfl | he'
          · exact hρG
          · exact hg.entriesMem e he'
        refine ⟨hT', hdiag', hentries, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with h | h
          · exact hg.workMem x (List.mem_cons_of_mem _ h)
          · obtain ⟨e, he, hx'⟩ := mem_newItems h
            rcases hx' with rfl | rfl
            · exact G.mul_mem hρG (hentries e he)
            · exact G.mul_mem (hentries e he) hρG
        · intro x hx
          rcases hg.gens x hx with h | h
          · exact Or.inl (sift_mono hext h)
          · rcases List.mem_cons.1 h with rfl | h'
            · exact Or.inl hgsift
            · exact Or.inr (List.mem_append_left _ h')
        · intro τ hτ ρ' hρ'
          by_cases hcτ : τ = ρ
          · subst hcτ
            exact Or.inr (List.mem_append_right _
              (mem_newItems_of (allEntries_subset_entriesList hρ')).1)
          · by_cases hcρ : ρ' = ρ
            · subst hcρ
              exact Or.inr (List.mem_append_right _
                (mem_newItems_of (allEntries_subset_entriesList hτ)).2)
            · obtain ⟨i₁, j₁, h₁⟩ := hτ
              obtain ⟨i₂, j₂, h₂⟩ := hρ'
              rw [hM'] at h₁ h₂
              have hτ' : τ ∈ AllEntries (tableOf M) := by
                rcases tableOf_insertRow_eq_some h₁ with h | h
                · exact absurd h hcτ
                · exact ⟨i₁, j₁, h⟩
              have hρ'' : ρ' ∈ AllEntries (tableOf M) := by
                rcases tableOf_insertRow_eq_some h₂ with h | h
                · exact absurd h hcρ
                · exact ⟨i₂, j₂, h⟩
              rcases hg.prods τ hτ' ρ' hρ'' with h | h
              · exact Or.inl (sift_mono hext h)
              · rcases List.mem_cons.1 h with h' | h'
                · exact Or.inl (by rw [h']; exact hgsift)
                · exact Or.inr (List.mem_append_left _ h')

end Good

/-! ## Termination

The potential drops at every round with a nonempty work list: either the work list shrinks by
one, or one of the at most `n²` positions is filled, which pays for the at most `2n²` products
that go on the work list. -/

/-- The potential of a state: the positions still to fill, weighted so that one insertion pays
for the products it creates, plus the length of the work list. -/
def potential (n : ℕ) (st : BuildState n) : ℕ :=
  (n * n - st.1.flatten.length) * (2 * (n * n) + 1) + st.2.length

theorem potential_mk (M : MTable n) (w : List (Perm (Fin n))) :
    potential n (M, w) = (n * n - M.flatten.length) * (2 * (n * n) + 1) + w.length := rfl

theorem potential_arith {A L r : ℕ} (h : L + 1 ≤ A) :
    (A - (L + 1)) * (2 * A + 1) + (r + 2 * (L + 1)) < (A - L) * (2 * A + 1) + (r + 1) := by
  have h1 : A - L = (A - (L + 1)) + 1 := by omega
  rw [h1, add_mul, one_mul]
  have h2 : 2 * (L + 1) ≤ 2 * A := by omega
  generalize (A - (L + 1)) * (2 * A + 1) = X
  omega

/-- **One round strictly lowers the potential**, as long as there is work left. -/
theorem potential_buildRound_lt {M : MTable n} {w : List (Perm (Fin n))} (hsh : Shape n M)
    (hne : w ≠ []) : potential n (buildRound (M, w)) < potential n (M, w) := by
  cases w with
  | nil => exact absurd rfl hne
  | cons g rest =>
      rcases hst : siftStuck (tableOf M) g with _ | ⟨i, ρ⟩
      · rw [buildRound_cons_none hst, potential_mk, potential_mk, List.length_cons]
        omega
      · rw [buildRound_cons_some hst, potential_mk, potential_mk]
        obtain ⟨hnone, hi, -⟩ := siftStuck_spec hst
        set j : ℕ := evalAt ρ i with hj
        set M' : MTable n := insertRow i M (j, ρ) with hM'
        have hsh' : Shape n M' := shape_insertRow hsh hi (evalAt_lt ρ hi) hnone ρ
        have hlen : M'.flatten.length = M.flatten.length + 1 :=
          length_flatten_insertRow ((j, ρ) : ℕ × Perm (Fin n)) i M
        have hbound : M.flatten.length + 1 ≤ n * n := by
          have := length_flatten_le_of_shape hsh'
          omega
        have hw : (rest ++ newItems M' ρ).length = rest.length + 2 * (M.flatten.length + 1) := by
          rw [List.length_append, length_newItems, hlen]
        show (n * n - M'.flatten.length) * (2 * (n * n) + 1) + (rest ++ newItems M' ρ).length
          < (n * n - M.flatten.length) * (2 * (n * n) + 1) + (g :: rest).length
        rw [hw, hlen, List.length_cons]
        exact potential_arith hbound

theorem buildRound_iterate_nil (M : MTable n) :
    ∀ f : ℕ, buildRound^[f] (M, ([] : List (Perm (Fin n)))) = (M, []) := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih => rw [Function.iterate_succ_apply, buildRound_nil, ih]

/-- **The loop finishes within the fuel.**  If the potential is at most `f`, then after `f`
rounds the work list is empty. -/
theorem work_eq_nil_of_potential_le : ∀ (f : ℕ) (st : BuildState n), Shape n st.1 →
    potential n st ≤ f → (buildRound^[f] st).2 = [] := by
  intro f
  induction f with
  | zero =>
      rintro ⟨M, w⟩ _ h
      rw [potential_mk] at h
      have hw : w = [] := List.length_eq_zero_iff.1 (by omega)
      show w = []
      exact hw
  | succ f ih =>
      rintro ⟨M, w⟩ hsh h
      by_cases hw : w = []
      · subst hw
        rw [buildRound_iterate_nil]
      · have hlt : potential n (buildRound (M, w)) < potential n (M, w) :=
          potential_buildRound_lt hsh hw
        have h' : potential n (M, w) ≤ f + 1 := h
        rw [Function.iterate_succ_apply]
        exact ih (buildRound (M, w)) (shape_buildRound M w hsh) (by omega)

/-! ## The initial table -/

/-- **The table the loop starts from**: the identity on the diagonal, nothing else. -/
def initTable (n : ℕ) : MTable n := (List.range n).map (fun i => [(i, (1 : Perm (Fin n)))])

theorem length_initTable (n : ℕ) : (initTable n).length = n := by
  rw [initTable, List.length_map, List.length_range]

theorem getD_initTable (n i : ℕ) :
    (initTable n).getD i ([] : MRow n) = if i < n then [(i, (1 : Perm (Fin n)))] else [] := by
  by_cases hi : i < n
  · rw [if_pos hi, List.getD_eq_getElem _ _ (by rw [length_initTable]; exact hi)]
    simp [initTable]
  · rw [if_neg hi, List.getD_eq_default _ _ (by rw [length_initTable]; omega)]

theorem tableOf_initTable (n i j : ℕ) :
    tableOf (initTable n) i j = if i < n ∧ j = i then some (1 : Perm (Fin n)) else none := by
  rw [tableOf, getD_initTable]
  by_cases hi : i < n
  · rw [if_pos hi]
    by_cases hj : j = i
    · subst hj
      rw [if_pos ⟨hi, rfl⟩]
      simp [List.lookup]
    · rw [if_neg (by tauto)]
      have hbeq : (j == i) = false := by simpa using hj
      simp [List.lookup, hbeq]
  · rw [if_neg hi, if_neg (by tauto)]
    rfl

theorem flatten_initTable (n : ℕ) :
    (initTable n).flatten = (List.range n).map (fun i => (i, (1 : Perm (Fin n)))) := by
  have key : ∀ l : List ℕ,
      (l.map (fun i => [(i, (1 : Perm (Fin n)))])).flatten
        = l.map (fun i => (i, (1 : Perm (Fin n)))) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, List.flatten_cons, ih, List.map_cons, List.singleton_append]
  exact key _

theorem entriesList_initTable {n : ℕ} {e : Perm (Fin n)} (h : e ∈ entriesList (initTable n)) :
    e = 1 := by
  rw [entriesList, flatten_initTable, List.map_map, List.mem_map] at h
  obtain ⟨i, -, hi⟩ := h
  exact hi.symm

theorem shape_initTable (n : ℕ) : Shape n (initTable n) := by
  refine ⟨by rw [length_initTable], ?_, ?_⟩
  · intro r hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
    simp
  · intro r hr q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    rw [List.mem_singleton] at hq
    subst hq
    exact List.mem_range.1 hi

theorem good_initTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Good (genGroup gens) {g | g ∈ gens} (initTable n, gens) := by
  have hdiag : ∀ i < n, tableOf (initTable n) i i = some (1 : Perm (Fin n)) := by
    intro i hi
    rw [tableOf_initTable, if_pos ⟨hi, rfl⟩]
  have hone : ∀ (i j : ℕ) (τ : Perm (Fin n)), tableOf (initTable n) i j = some τ →
      τ = 1 ∧ j = i ∧ i < n := by
    intro i j τ h
    rw [tableOf_initTable] at h
    by_cases hc : i < n ∧ j = i
    · rw [if_pos hc] at h
      exact ⟨(Option.some.inj h).symm, hc.2, hc.1⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  have hIT : IsTable (tableOf (initTable n)) (genGroup gens) :=
    { mem := fun {i j τ} h => by rw [(hone i j τ h).1]; exact Subgroup.one_mem _
      fixes := fun {i j τ} h => by rw [(hone i j τ h).1]; exact fixes_one i
      img := fun {i j τ} h => by
        obtain ⟨h1, h2, -⟩ := hone i j τ h
        rw [h1, h2, evalAt_one] }
  refine ⟨hIT, hdiag, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [entriesList_initTable he]
    exact Subgroup.one_mem _
  · intro g hg
    exact Subgroup.subset_closure hg
  · intro g hg
    exact Or.inr hg
  · intro τ hτ ρ' hρ'
    obtain ⟨i₁, j₁, h₁⟩ := hτ
    obtain ⟨i₂, j₂, h₂⟩ := hρ'
    refine Or.inl ?_
    rw [(hone i₁ j₁ τ h₁).1, (hone i₂ j₂ ρ' h₂).1, one_mul]
    exact one_mem_sifted hdiag n 0 (by omega)

/-! ## The construction -/

/-- **The fuel of the closure loop**: `n²` insertions, each paying for `2n²` products, plus the
generators themselves.  This is a number of *rounds*, and the loop is literally that many
iterations of `Algo.buildRound`. -/
def buildFuel (n m : ℕ) : ℕ := n * n * (2 * (n * n) + 1) + m

/-- **The complete table built from a list of generators** (Schreier–Sims). -/
def buildTable (n : ℕ) (gens : List (Perm (Fin n))) : MTable n :=
  (buildRound^[buildFuel n gens.length] (initTable n, gens)).1

theorem potential_init (n : ℕ) (gens : List (Perm (Fin n))) :
    potential n (initTable n, gens) ≤ buildFuel n gens.length := by
  rw [potential_mk, buildFuel]
  have h1 : (n * n - (initTable n).flatten.length) * (2 * (n * n) + 1)
      ≤ n * n * (2 * (n * n) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem good_iterate {G : Subgroup (Perm (Fin n))} {S : Set (Perm (Fin n))} :
    ∀ (f : ℕ) (st : BuildState n), Good G S st → Good G S (buildRound^[f] st) := by
  intro f
  induction f with
  | zero => intro st h; exact h
  | succ f ih =>
      rintro ⟨M, w⟩ h
      rw [Function.iterate_succ_apply]
      exact ih _ (good_buildRound h)

theorem shape_iterate : ∀ (f : ℕ) (st : BuildState n), Shape n st.1 →
    Shape n (buildRound^[f] st).1 := by
  intro f
  induction f with
  | zero => intro st h; exact h
  | succ f ih =>
      rintro ⟨M, w⟩ h
      rw [Function.iterate_succ_apply]
      exact ih _ (shape_buildRound M w h)

theorem good_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Good (genGroup gens) {g | g ∈ gens}
      (buildRound^[buildFuel n gens.length] (initTable n, gens)) :=
  good_iterate _ _ (good_initTable n gens)

theorem work_buildTable_eq_nil (n : ℕ) (gens : List (Perm (Fin n))) :
    (buildRound^[buildFuel n gens.length] (initTable n, gens)).2 = [] :=
  work_eq_nil_of_potential_le _ _ (shape_initTable n) (potential_init n gens)

/-- **The table built is a table for `⟨gens⟩`.** -/
theorem isTable_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    IsTable (tableOf (buildTable n gens)) (genGroup gens) := (good_buildTable n gens).isTable

/-- **The table built has the identity on its diagonal.** -/
theorem diag_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ i < n, tableOf (buildTable n gens) i i = some 1 := (good_buildTable n gens).diag

/-- **The shape of the table built**: at most `n` rows, at most `n` entries in each. -/
theorem shape_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Shape n (buildTable n gens) := shape_iterate _ _ (shape_initTable n)

/-- **The table built is complete for `⟨gens⟩`** (the closure criterion
`Algo.complete_of_closed`). -/
theorem complete_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Complete (tableOf (buildTable n gens)) (genGroup gens) := by
  have hgood := good_buildTable n gens
  have hnil := work_buildTable_eq_nil n gens
  refine complete_of_closed (isTable_buildTable n gens) (diag_buildTable n gens)
    (S := {g | g ∈ gens}) rfl ?_ ?_
  · intro g hg
    rcases hgood.gens g hg with h | h
    · exact h
    · rw [hnil] at h; exact absurd h (by simp)
  · intro τ hτ ρ hρ
    rcases hgood.prods τ hτ ρ hρ with h | h
    · exact h
    · rw [hnil] at h; exact absurd h (by simp)

/-- **Membership by sifting through the table built.** -/
theorem mem_iff_sift_buildTable (n : ℕ) (gens : List (Perm (Fin n))) (σ : Perm (Fin n)) :
    σ ∈ genGroup gens ↔ sift (tableOf (buildTable n gens)) σ = some 1 :=
  mem_iff_sift_eq_one (isTable_buildTable n gens) (complete_buildTable n gens) σ

/-- **The order of `⟨gens⟩`** is the product of the row sizes of the table built. -/
theorem card_eq_prod_row_card_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Nat.card (genGroup gens)
      = ∏ i ∈ Finset.range n, (row (tableOf (buildTable n gens)) i).card :=
  card_eq_prod_row_card (isTable_buildTable n gens) (complete_buildTable n gens)

end Algo
