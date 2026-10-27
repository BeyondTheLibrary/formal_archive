/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: building a complete sifting table on raw data, and the membership test.
-/
import Workspace.Algo.ChainBuild

/-!
# Schreier–Sims on raw data

`Workspace/Algo/ChainBuild.lean` builds a complete sifting table for `⟨gens⟩` by the closure
loop, as mathematics.  This file runs the same loop on raw data and reads off the membership
test, which is the class-D row "membership test in a permutation group" of
`Workspace/Algo/DESIGN.md`, item 2.

## The degree comes as a list

Every routine here takes a *domain witness* `dom : List ℕ` of length `n` beside its real
argument, exactly as `Algo.rawOne` does, because `List.range n` for a machine natural `n` is not
a `RAM.PolyFun` (the note of 2026-09-21 at the end of `Workspace/Machine/DESIGN.md`, and point 1
of the note on work package A3).  The loop needs the degree twice: for the initial diagonal
table, and for the number of rounds, which is `Algo.buildFuel n |gens|` and therefore has to
arrive as the length of a list (`Algo.rawFuelList`, built from `dom` by two squarings).

## Specifications are stated on encoded input

As everywhere in this layer, a routine is total and its specification speaks about well-formed
input only.  Here it is convenient to state the loop's specification in the *encoding*
direction: the raw loop run on `Algo.encMTable n M` is the encoding of the mathematical loop run
on `M` (`Algo.rawBuildRound_enc`).  Nothing is assumed about the raw data then, since encoded
data is well formed by construction.

## Main definitions and results

* `Algo.rawSiftStuck` — sifting with a report, the raw copy of `Algo.siftStuck`;
* `Algo.rawBuildRound`, `Algo.rawBuildTable` — the closure loop;
* `Algo.rawBuildTable_spec` — the raw table built is the encoding of `Algo.buildTable`;
* `Algo.decTable_rawBuildTable` — so its decoding is the mathematical table;
* `Algo.rawMem`, `Algo.rawMem_spec` — the membership test and its correctness.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Sifting with a report, on raw data

The accumulator carries the report (`none` until the sift gets stuck) and the current residue.
Once the report is set the remaining rounds do nothing, which is `Algo.rawStuckFold_frozen`. -/

/-- **One round of sifting with a report.** -/
def rawStuckStep (p : RawTable × ((Option (ℕ × RawPerm) × RawPerm) × ℕ)) :
    Option (ℕ × RawPerm) × RawPerm :=
  match p.2.1.1 with
  | some x => (some x, p.2.1.2)
  | none =>
      match rawTableGet (p.1, (p.2.2, rawApply (p.2.1.2, p.2.2))) with
      | none => (some (p.2.2, p.2.1.2), p.2.1.2)
      | some τ => (none, rawMul (rawInv τ, p.2.1.2))

/-- **Sifting with a report**, one round per level. -/
def rawSiftStuck (p : RawTable × RawPerm) : Option (ℕ × RawPerm) :=
  (List.foldl (fun acc i => rawStuckStep (p.1, (acc, i)))
    ((none, p.2) : Option (ℕ × RawPerm) × RawPerm) (List.range p.2.length)).1

theorem rawStuckStep_some (t : RawTable) (x : ℕ × RawPerm) (r : RawPerm) (i : ℕ) :
    rawStuckStep (t, (((some x : Option (ℕ × RawPerm)), r), i)) = (some x, r) := rfl

theorem rawStuckFold_frozen (t : RawTable) (x : ℕ × RawPerm) (r : RawPerm) :
    ∀ l : List ℕ,
      List.foldl (fun acc i => rawStuckStep (t, (acc, i))) ((some x, r)) l = (some x, r) := by
  intro l
  induction l with
  | nil => rfl
  | cons a s ih => rw [List.foldl_cons, rawStuckStep_some]; exact ih

/-- **The specification of the loop**, level by level. -/
theorem rawStuckFold_spec {n : ℕ} {t : RawTable} (ht : RawTable.WF n t) :
    ∀ (k i : ℕ) (r : Perm (Fin n)),
      (List.foldl (fun acc j => rawStuckStep (t, (acc, j)))
          (((none : Option (ℕ × RawPerm)), encPerm n r)) (List.range' i k)).1
        = (siftStuckAux (decTable n t) k i r).map (fun z => (z.1, encPerm n z.2)) := by
  intro k
  induction k with
  | zero => intro i r; rfl
  | succ k ih =>
      intro i r
      have hlist : List.range' i (k + 1) = i :: List.range' (i + 1) k := rfl
      rw [hlist, List.foldl_cons]
      have hstep : rawStuckStep (t, (((none : Option (ℕ × RawPerm)), encPerm n r), i))
          = (match rawTableGet (t, (i, evalAt r i)) with
             | none => (some (i, encPerm n r), encPerm n r)
             | some τ => (none, rawMul (rawInv τ, encPerm n r))) := by
        show (match rawTableGet (t, (i, rawApply (encPerm n r, i))) with
            | none => (some (i, encPerm n r), encPerm n r)
            | some τ => ((none : Option (ℕ × RawPerm)), rawMul (rawInv τ, encPerm n r))) = _
        rw [rawApply_encPerm_eq_evalAt]
      rcases hlook : rawTableGet (t, (i, evalAt r i)) with _ | τ
      · have hdec : decTable n t i (evalAt r i) = none := by rw [decTable, hlook]; rfl
        rw [hstep, hlook]
        simp only
        rw [rawStuckFold_frozen, siftStuckAux_succ_of_none hdec]
        rfl
      · have hwf : RawPerm.WF n τ := wf_of_tableEntry ht ⟨i, evalAt r i, hlook⟩
        have hdec : decTable n t i (evalAt r i) = some (decPerm n τ) := by
          rw [decTable, hlook]; rfl
        rw [hstep, hlook]
        simp only
        have hres : rawMul (rawInv τ, encPerm n r) = encPerm n ((decPerm n τ)⁻¹ * r) := by
          rw [rawInv_of_wf hwf, rawMul_encPerm]
        rw [hres, ih (i + 1) ((decPerm n τ)⁻¹ * r), siftStuckAux_succ_of_some hdec]

/-- **The specification of `Algo.rawSiftStuck`.** -/
theorem rawSiftStuck_spec {n : ℕ} {t : RawTable} (ht : RawTable.WF n t) (σ : Perm (Fin n)) :
    rawSiftStuck (t, encPerm n σ)
      = (siftStuck (decTable n t) σ).map (fun z => (z.1, encPerm n z.2)) := by
  rw [rawSiftStuck, siftStuck]
  show (List.foldl (fun acc i => rawStuckStep (t, (acc, i)))
      (((none : Option (ℕ × RawPerm)), encPerm n σ)) (List.range (encPerm n σ).length)).1 = _
  rw [length_encPerm, List.range_eq_range']
  exact rawStuckFold_spec ht n 0 σ

/-! ## Encoding a stored table -/

/-- **The raw form of a stored table.** -/
def encMTable (n : ℕ) (M : MTable n) : RawTable :=
  M.map (fun row => row.map (fun q => (q.1, encPerm n q.2)))

theorem lookup_map_snd {α β : Type*} (f : α → β) : ∀ (l : List (ℕ × α)) (j : ℕ),
    (l.map (fun q => (q.1, f q.2))).lookup j = (l.lookup j).map f := by
  intro l
  induction l with
  | nil => intro j; rfl
  | cons a t ih =>
      intro j
      obtain ⟨k, v⟩ := a
      by_cases hjk : j = k
      · subst hjk
        simp [List.lookup]
      · have hbeq : (j == k) = false := by simpa using hjk
        simp [List.lookup, hbeq, ih j]

theorem getD_map_nil {α β : Type*} (f : List α → List β) (hf : f [] = []) :
    ∀ (M : List (List α)) (i : ℕ), (M.map f).getD i [] = f (M.getD i []) := by
  intro M i
  by_cases hi : i < M.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
      List.getD_eq_getElem _ _ hi, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hi), hf]

theorem rawTableGet_encMTable {n : ℕ} (M : MTable n) (i j : ℕ) :
    rawTableGet (encMTable n M, (i, j)) = (tableOf M i j).map (encPerm n) := by
  rw [rawTableGet, encMTable, tableOf]
  show ((M.map (fun row => row.map (fun q => (q.1, encPerm n q.2)))).getD i []).lookup j = _
  rw [getD_map_nil _ rfl, lookup_map_snd]

theorem decTable_encMTable (n : ℕ) (M : MTable n) : decTable n (encMTable n M) = tableOf M := by
  funext i j
  rw [decTable, rawTableGet_encMTable, Option.map_map]
  rcases tableOf M i j with _ | τ
  · rfl
  · simp

theorem wf_encMTable (n : ℕ) (M : MTable n) : RawTable.WF n (encMTable n M) := by
  intro row hrow q hq
  rw [encMTable, List.mem_map] at hrow
  obtain ⟨r, -, rfl⟩ := hrow
  rw [List.mem_map] at hq
  obtain ⟨p, -, rfl⟩ := hq
  exact wf_encPerm n p.2

/-! ### Encoding commutes with insertion and with the entries -/

theorem map_insertRow {β γ : Type*} (f : β → γ) : ∀ (i : ℕ) (M : List (List β)) (q : β),
    (insertRow i M q).map (List.map f) = insertRow i (M.map (List.map f)) (f q) := by
  intro i
  induction i with
  | zero =>
      intro M q
      cases M with
      | nil => rfl
      | cons a l => rfl
  | succ i ih =>
      intro M q
      cases M with
      | nil =>
          show ([] : List γ) :: (insertRow i [] q).map (List.map f) = _
          rw [ih [] q]; rfl
      | cons a l =>
          show (a.map f) :: (insertRow i l q).map (List.map f) = _
          rw [ih l q]; rfl

theorem encMTable_insertRow (n : ℕ) (M : MTable n) (i j : ℕ) (τ : Perm (Fin n)) :
    encMTable n (insertRow i M (j, τ)) = insertRow i (encMTable n M) (j, encPerm n τ) :=
  map_insertRow (fun q : ℕ × Perm (Fin n) => (q.1, encPerm n q.2)) i M (j, τ)

/-- The list of the raw permutations stored in a raw table. -/
def rawEntries (t : RawTable) : List RawPerm := t.flatten.map Prod.snd

theorem flatten_map_map {α β : Type*} (f : α → β) : ∀ M : List (List α),
    (M.map (List.map f)).flatten = M.flatten.map f := by
  intro M
  induction M with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.flatten_cons, ih, List.flatten_cons, List.map_append]

theorem rawEntries_encMTable (n : ℕ) (M : MTable n) :
    rawEntries (encMTable n M) = (entriesList M).map (encPerm n) := by
  rw [rawEntries, encMTable, flatten_map_map, entriesList, List.map_map, List.map_map]
  rfl

/-- The products of a new entry with every entry of a raw table, in both orders. -/
def rawNewItems (t : RawTable) (ρ : RawPerm) : List RawPerm :=
  (rawEntries t).flatMap (fun e => [rawMul (ρ, e), rawMul (e, ρ)])

theorem map_flatMap_pair {α β γ : Type*} (f g : α → β) (h : β → γ) : ∀ l : List α,
    (l.flatMap (fun e => [f e, g e])).map h = l.flatMap (fun e => [h (f e), h (g e)]) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons]; rfl

theorem rawNewItems_encMTable (n : ℕ) (M : MTable n) (ρ : Perm (Fin n)) :
    rawNewItems (encMTable n M) (encPerm n ρ) = (newItems M ρ).map (encPerm n) := by
  rw [rawNewItems, rawEntries_encMTable, List.flatMap_map, newItems,
    map_flatMap_pair (fun e => ρ * e) (fun e => e * ρ) (encPerm n)]
  refine List.flatMap_congr ?_
  intro e _
  rw [rawMul_encPerm, rawMul_encPerm]

/-! ## Insertion on raw data

`Algo.insertRow` recurses on the level, which is a machine natural, so it is not a routine (the
same obstruction as `List.range n`, see the header).  On a table that already has a row at that
level — which is the only case the loop meets, since the table has `n` rows from the start —
insertion is a `map` over the rows with the level as a parameter, and that *is* a routine. -/

/-- **Insertion at an existing row**: the machine form of `Algo.insertRow`. -/
def rawInsert (p : (ℕ × RawPerm) × (RawTable × ℕ)) : RawTable :=
  p.2.1.zipIdx.map (fun z => if z.2 = p.2.2 then p.1 :: z.1 else z.1)

/-- **The two insertions agree** as soon as the row exists. -/
theorem rawInsert_eq {β : Type*} (q : β) (i : ℕ) (M : List (List β)) (h : i < M.length) :
    M.zipIdx.map (fun z => if z.2 = i then q :: z.1 else z.1) = insertRow i M q := by
  have hlen : (insertRow i M q).length = M.length := length_insertRow_eq q i M h
  refine List.ext_getElem (by simp [hlen]) ?_
  intro k h1 h2
  have hk : k < M.length := by simpa using h1
  rw [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  show (if k = i then q :: M[k] else M[k]) = _
  have hrhs : (insertRow i M q)[k] = (insertRow i M q).getD k [] :=
    (List.getD_eq_getElem _ _ h2).symm
  have hmk : M[k] = M.getD k [] := (List.getD_eq_getElem _ _ hk).symm
  rw [hrhs, insertRow_getD, hmk]
  by_cases hki : k = i <;> simp [hki]

/-! ## The closure loop on raw data -/

/-- **One round of the closure loop, on raw data.** -/
def rawBuildRound (st : RawTable × List RawPerm) : RawTable × List RawPerm :=
  match st.2 with
  | [] => st
  | g :: rest =>
      match rawSiftStuck (st.1, g) with
      | none => (st.1, rest)
      | some (i, ρ) =>
          (rawInsert ((rawApply (ρ, i), ρ), (st.1, i)),
            rest ++ rawNewItems (rawInsert ((rawApply (ρ, i), ρ), (st.1, i))) ρ)

theorem rawBuildRound_nil (t : RawTable) : rawBuildRound (t, []) = (t, []) := rfl

theorem rawBuildRound_cons_none {t : RawTable} {g : RawPerm} {rest : List RawPerm}
    (h : rawSiftStuck (t, g) = none) : rawBuildRound (t, g :: rest) = (t, rest) := by
  show (match rawSiftStuck (t, g) with
      | none => (t, rest)
      | some (i, ρ) => (rawInsert ((rawApply (ρ, i), ρ), (t, i)),
          rest ++ rawNewItems (rawInsert ((rawApply (ρ, i), ρ), (t, i))) ρ)) = _
  rw [h]

theorem rawBuildRound_cons_some {t : RawTable} {g : RawPerm} {rest : List RawPerm} {i : ℕ}
    {ρ : RawPerm} (h : rawSiftStuck (t, g) = some (i, ρ)) :
    rawBuildRound (t, g :: rest)
      = (rawInsert ((rawApply (ρ, i), ρ), (t, i)),
          rest ++ rawNewItems (rawInsert ((rawApply (ρ, i), ρ), (t, i))) ρ) := by
  show (match rawSiftStuck (t, g) with
      | none => (t, rest)
      | some (i, ρ) => (rawInsert ((rawApply (ρ, i), ρ), (t, i)),
          rest ++ rawNewItems (rawInsert ((rawApply (ρ, i), ρ), (t, i))) ρ)) = _
  rw [h]

/-- **The raw round simulates the mathematical round.**  The hypothesis is the invariant
`Algo.length_buildRound`: the table has one row per point, so the raw insertion (a `map`) does
what `Algo.insertRow` does. -/
theorem rawBuildRound_enc (n : ℕ) (M : MTable n) (hM : M.length = n)
    (w : List (Perm (Fin n))) :
    rawBuildRound (encMTable n M, w.map (encPerm n))
      = (encMTable n (buildRound (M, w)).1, (buildRound (M, w)).2.map (encPerm n)) := by
  have hdec : decTable n (encMTable n M) = tableOf M := decTable_encMTable n M
  cases w with
  | nil => rw [List.map_nil, rawBuildRound_nil, buildRound_nil]; rfl
  | cons g rest =>
      rw [List.map_cons]
      have hstuck : rawSiftStuck (encMTable n M, encPerm n g)
          = (siftStuck (tableOf M) g).map (fun z => (z.1, encPerm n z.2)) := by
        rw [rawSiftStuck_spec (wf_encMTable n M) g, hdec]
      rcases hst : siftStuck (tableOf M) g with _ | ⟨i, ρ⟩
      · rw [rawBuildRound_cons_none (by rw [hstuck, hst]; rfl), buildRound_cons_none hst]
      · obtain ⟨-, hi, -⟩ := siftStuck_spec hst
        have hlen : i < (encMTable n M).length := by
          rw [encMTable, List.length_map, hM]; exact hi
        have hins : rawInsert ((rawApply (encPerm n ρ, i), encPerm n ρ), (encMTable n M, i))
            = encMTable n (insertRow i M (evalAt ρ i, ρ)) := by
          show (encMTable n M).zipIdx.map
              (fun z => if z.2 = i then
                ((rawApply (encPerm n ρ, i), encPerm n ρ) : ℕ × RawPerm) :: z.1 else z.1) = _
          rw [rawInsert_eq ((rawApply (encPerm n ρ, i), encPerm n ρ) : ℕ × RawPerm) i _ hlen,
            rawApply_encPerm_eq_evalAt, encMTable_insertRow]
        rw [rawBuildRound_cons_some (by rw [hstuck, hst]; rfl), buildRound_cons_some hst,
          hins, rawNewItems_encMTable, ← List.map_append]

theorem rawBuildRound_iterate_enc (n : ℕ) : ∀ (f : ℕ) (M : MTable n), M.length = n →
    ∀ (w : List (Perm (Fin n))),
    rawBuildRound^[f] (encMTable n M, w.map (encPerm n))
      = (encMTable n (buildRound^[f] (M, w)).1, (buildRound^[f] (M, w)).2.map (encPerm n)) := by
  intro f
  induction f with
  | zero => intro M _ w; rfl
  | succ f ih =>
      intro M hM w
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        rawBuildRound_enc n M hM w]
      exact ih _ (length_buildRound M w hM) _

/-! ## The initial table and the fuel -/

/-- **The initial raw table**: the identity on the diagonal. -/
def rawInitTable (dom : List ℕ) : RawTable := (rawOne dom).map (fun i => [(i, rawOne dom)])

theorem rawInitTable_eq {n : ℕ} (dom : List ℕ) (h : dom.length = n) :
    rawInitTable dom = encMTable n (initTable n) := by
  rw [rawInitTable, rawOne, h, encMTable, initTable, List.map_map]
  refine List.map_congr_left ?_
  intro i _
  show [(i, List.range n)] = [(i, encPerm n 1)]
  rw [encPerm_one]

/-- A list of length `|l|²`. -/
def rawSquare (l : List ℕ) : List ℕ := (l.map (fun _ => l)).flatten

theorem length_flatten_map_const {α : Type*} (c : List ℕ) : ∀ l : List α,
    ((l.map (fun _ => c)).flatten).length = l.length * c.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
      ring

theorem length_rawSquare (l : List ℕ) : (rawSquare l).length = l.length * l.length :=
  length_flatten_map_const l l

/-- **The fuel of the raw loop**, as a list whose length is `Algo.buildFuel`. -/
def rawFuelList (p : List ℕ × List RawPerm) : List ℕ :=
  rawSquare (rawSquare p.1) ++ rawSquare (rawSquare p.1) ++ rawSquare p.1 ++
    p.2.map (fun _ => 0)

theorem length_rawFuelList (dom : List ℕ) (gens : List RawPerm) :
    (rawFuelList (dom, gens)).length = buildFuel dom.length gens.length := by
  rw [rawFuelList, buildFuel]
  show ((rawSquare (rawSquare dom) ++ rawSquare (rawSquare dom) ++ rawSquare dom ++
    gens.map (fun _ => 0))).length = _
  rw [List.length_append, List.length_append, List.length_append, List.length_map]
  simp only [length_rawSquare]
  ring

/-- **The closure loop on raw data.**  `dom` is a domain witness: any list of length `n`. -/
def rawBuildTable (p : List ℕ × List RawPerm) : RawTable :=
  (List.foldl (fun st _ => rawBuildRound st) ((rawInitTable p.1, p.2)) (rawFuelList p)).1

theorem foldl_const_eq {α σ : Type*} (f : σ → σ) : ∀ (l : List α) (x : σ),
    List.foldl (fun y (_ : α) => f y) x l = f^[l.length] x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- **The raw loop builds the encoding of the mathematical table.** -/
theorem rawBuildTable_spec {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    rawBuildTable (dom, gens.map (encPerm n)) = encMTable n (buildTable n gens) := by
  rw [rawBuildTable]
  show (List.foldl (fun st _ => rawBuildRound st)
    ((rawInitTable dom, gens.map (encPerm n))) (rawFuelList (dom, gens.map (encPerm n)))).1 = _
  rw [foldl_const_eq, length_rawFuelList, List.length_map, hdom, rawInitTable_eq dom hdom,
    rawBuildRound_iterate_enc n _ (initTable n) (length_initTable n) gens, buildTable]

/-- **The table the raw loop builds decodes to the mathematical one.** -/
theorem decTable_rawBuildTable {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    decTable n (rawBuildTable (dom, gens.map (encPerm n))) = tableOf (buildTable n gens) := by
  rw [rawBuildTable_spec dom hdom gens, decTable_encMTable]

theorem wf_rawBuildTable {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    RawTable.WF n (rawBuildTable (dom, gens.map (encPerm n))) := by
  rw [rawBuildTable_spec dom hdom gens]
  exact wf_encMTable n _

/-! ## The membership test -/

/-- **Membership in a permutation group given by generators**: build the table and sift. -/
def rawMem (p : (List ℕ × List RawPerm) × RawPerm) : Bool :=
  match rawSift (rawBuildTable p.1, p.2) with
  | none => false
  | some r => rawPermEq (r, rawOne p.2)

/-- **The membership test is correct.**  `dom` is any list of length `n`. -/
theorem rawMem_spec {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) (σ : Perm (Fin n)) :
    rawMem ((dom, gens.map (encPerm n)), encPerm n σ) = true ↔ σ ∈ genGroup gens := by
  have hsift : rawSift (rawBuildTable (dom, gens.map (encPerm n)), encPerm n σ)
      = (sift (tableOf (buildTable n gens)) σ).map (encPerm n) := by
    rw [rawSift_spec (wf_rawBuildTable dom hdom gens) σ, decTable_rawBuildTable dom hdom gens]
  rw [mem_iff_sift_buildTable n gens σ]
  show (match rawSift (rawBuildTable (dom, gens.map (encPerm n)), encPerm n σ) with
      | none => false
      | some r => rawPermEq (r, rawOne (encPerm n σ))) = true ↔ _
  rw [hsift]
  rcases h : sift (tableOf (buildTable n gens)) σ with _ | r
  · simp
  · simp only [Option.map_some]
    rw [rawPermEq, rawOne_eq, length_encPerm]
    constructor
    · intro hr
      have : encPerm n r = encPerm n 1 := of_decide_eq_true hr
      rw [encPerm_injective n this]
    · intro hr
      have : r = 1 := by
        have := Option.some.inj hr
        exact this
      rw [this]
      exact decide_eq_true rfl

/-! ## The `PolyFun` statements

The rounds themselves are `RAM.PolyFun`s by the combinators.  What does *not* follow from them
is the bound on the accumulator of a fold from an **arbitrary** start (point 2 of the note on
work package A3 in `Workspace/Algo/DESIGN.md`), and that needs a structure lemma, exactly as
`Algo.rawSiftFold_struct` did for the sifting loop. -/

theorem flatMap_eq_flatten_map {α β : Type*} (f : α → List β) : ∀ l : List α,
    l.flatMap f = (l.map f).flatten := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, ih, List.map_cons, List.flatten_cons]

/-- **The shape of the accumulator along the reporting sift.**  Whatever the start residue is,
the residue keeps its length and every one of its entries is an entry of the start or of the
inverse of a table entry; and the level reported is one of the levels walked.  This is the
statement that bounds the accumulator from an arbitrary start, as
`Algo.rawSiftFold_struct` does for `Algo.rawSift`. -/
theorem rawStuckFold_struct (t : RawTable) : ∀ (l : List ℕ) (r : RawPerm),
    ((List.foldl (fun a i => rawStuckStep (t, (a, i)))
        (((none : Option (ℕ × RawPerm)), r)) l).2.length = r.length ∧
      ∀ y ∈ (List.foldl (fun a i => rawStuckStep (t, (a, i)))
          (((none : Option (ℕ × RawPerm)), r)) l).2,
        y ∈ r ∨ ∃ τ, TableEntry t τ ∧ y ∈ rawInv τ) ∧
    ∀ i ρ, (List.foldl (fun a i => rawStuckStep (t, (a, i)))
        (((none : Option (ℕ × RawPerm)), r)) l).1 = some (i, ρ) →
      i ∈ l ∧ ρ.length = r.length ∧
        ∀ y ∈ ρ, y ∈ r ∨ ∃ τ, TableEntry t τ ∧ y ∈ rawInv τ := by
  intro l
  induction l with
  | nil =>
      intro r
      refine ⟨⟨rfl, fun y hy => Or.inl hy⟩, ?_⟩
      intro i ρ h
      exact absurd h (by simp)
  | cons a s ih =>
      intro r
      rw [List.foldl_cons]
      rcases hlook : rawTableGet (t, (a, rawApply (r, a))) with _ | τ
      · have hstep : rawStuckStep (t, (((none : Option (ℕ × RawPerm)), r), a))
            = (some (a, r), r) := by
          show (match rawTableGet (t, (a, rawApply (r, a))) with
              | none => ((some (a, r) : Option (ℕ × RawPerm)), r)
              | some τ => ((none : Option (ℕ × RawPerm)), rawMul (rawInv τ, r))) = _
          rw [hlook]
        rw [hstep, rawStuckFold_frozen]
        refine ⟨⟨rfl, fun y hy => Or.inl hy⟩, ?_⟩
        intro i ρ h
        have h' : (a, r) = (i, ρ) := Option.some.inj h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h'
        exact ⟨List.mem_cons_self .., rfl, fun y hy => Or.inl hy⟩
      · have hstep : rawStuckStep (t, (((none : Option (ℕ × RawPerm)), r), a))
            = (none, rawMul (rawInv τ, r)) := by
          show (match rawTableGet (t, (a, rawApply (r, a))) with
              | none => ((some (a, r) : Option (ℕ × RawPerm)), r)
              | some τ => ((none : Option (ℕ × RawPerm)), rawMul (rawInv τ, r))) = _
          rw [hlook]
        have hτ : TableEntry t τ := ⟨a, rawApply (r, a), hlook⟩
        set r₁ : RawPerm := rawMul (rawInv τ, r) with hr₁
        have hlen₁ : r₁.length = r.length := by rw [hr₁, length_rawMul]
        have hmem₁ : ∀ y ∈ r₁, y ∈ r ∨ ∃ τ', TableEntry t τ' ∧ y ∈ rawInv τ' := by
          intro y hy
          rw [hr₁] at hy
          rcases mem_rawMul hy with h | h
          · exact Or.inr ⟨τ, hτ, h⟩
          · exact Or.inl h
        rw [hstep]
        obtain ⟨⟨hl, hm⟩, hrep⟩ := ih r₁
        refine ⟨⟨by rw [hl, hlen₁], ?_⟩, ?_⟩
        · intro y hy
          rcases hm y hy with h | h
          · exact hmem₁ y h
          · exact Or.inr h
        · intro i ρ h
          obtain ⟨hi, hρl, hρm⟩ := hrep i ρ h
          refine ⟨List.mem_cons_of_mem _ hi, by rw [hρl, hlen₁], ?_⟩
          intro y hy
          rcases hρm y hy with h' | h'
          · exact hmem₁ y h'
          · exact Or.inr h'

theorem polyFun_rawInsert : PolyFun rawInsert := by
  have hf : PolyFun (fun w : ((ℕ × RawPerm) × ℕ) × (RawRow × ℕ) =>
      if (decide (w.2.2 = w.1.2) : Bool) then w.1.1 :: w.2.1 else w.2.1) :=
    PolyFun.ite
      (((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq)
      (((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp
        (polyFun_cons (β := ℕ × RawPerm)))
      (polyFun_snd.comp polyFun_fst)
  have hin : PolyFun (fun p : (ℕ × RawPerm) × (RawTable × ℕ) =>
      (((p.1, p.2.2) : (ℕ × RawPerm) × ℕ), p.2.1.zipIdx)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).pair
      ((polyFun_snd.comp polyFun_fst).comp polyFun_zipIdx)
  refine (hin.comp (PolyFun.mapParam hf)).of_eq (fun p => ?_)
  show (p.2.1.zipIdx).map (fun z => if (decide (z.2 = p.2.2) : Bool) then p.1 :: z.1 else z.1)
      = rawInsert p
  rw [rawInsert]
  refine List.map_congr_left ?_
  intro z _
  by_cases h : z.2 = p.2.2 <;> simp [h]

theorem polyFun_rawStuckStep : PolyFun rawStuckStep := by
  -- the inner case analysis, on the entry at the current position
  have hinner : PolyFun (fun z : RawTable × (RawPerm × ℕ) =>
      match rawTableGet (z.1, (z.2.2, rawApply (z.2.1, z.2.2))) with
      | none => ((some (z.2.2, z.2.1) : Option (ℕ × RawPerm)), z.2.1)
      | some τ => ((none : Option (ℕ × RawPerm)), rawMul (rawInv τ, z.2.1))) := by
    have hlook : PolyFun (fun z : RawTable × (RawPerm × ℕ) =>
        rawTableGet (z.1, (z.2.2, rawApply (z.2.1, z.2.2)))) :=
      (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).pair
        (((polyFun_snd.comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)).comp
          polyFun_rawApply))).comp polyFun_rawTableGet
    have hnone : PolyFun (fun z : RawTable × (RawPerm × ℕ) =>
        (((some (z.2.2, z.2.1) : Option (ℕ × RawPerm))), z.2.1)) :=
      (((polyFun_snd.comp polyFun_snd).pair (polyFun_snd.comp polyFun_fst)).comp
        polyFun_some).pair (polyFun_snd.comp polyFun_fst)
    have hsome : PolyFun (fun w : RawPerm × (RawTable × (RawPerm × ℕ)) =>
        ((none : Option (ℕ × RawPerm)), rawMul (rawInv w.1, w.2.2.1))) :=
      (polyFun_none (β := ℕ × RawPerm)).pair
        (((polyFun_fst.comp polyFun_rawInv).pair
          ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp polyFun_rawMul)
    refine ((hlook.pair polyFun_id).comp (PolyFun.optionElim hnone hsome)).of_eq (fun z => ?_)
    rcases rawTableGet (z.1, (z.2.2, rawApply (z.2.1, z.2.2))) with _ | τ <;> rfl
  -- the outer case analysis, on the report
  have houter : PolyFun (fun w : (ℕ × RawPerm) × (RawTable × (RawPerm × ℕ)) =>
      (((some w.1 : Option (ℕ × RawPerm))), w.2.2.1)) :=
    (polyFun_fst.comp polyFun_some).pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have hin : PolyFun (fun p : RawTable × ((Option (ℕ × RawPerm) × RawPerm) × ℕ) =>
      ((p.2.1.1, ((p.1, (p.2.1.2, p.2.2)) : RawTable × (RawPerm × ℕ))) :
        Option (ℕ × RawPerm) × (RawTable × (RawPerm × ℕ)))) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_fst.pair (((polyFun_snd.comp polyFun_fst).comp polyFun_snd).pair
        (polyFun_snd.comp polyFun_snd)))
  refine (hin.comp (PolyFun.optionElim hinner houter)).of_eq (fun p => ?_)
  obtain ⟨t, ⟨o, r⟩, i⟩ := p
  cases o <;> rfl

theorem polyFun_rawEntries : PolyFun rawEntries :=
  (polyFun_flatten.comp (PolyFun.map (polyFun_snd (α := ℕ) (β := RawPerm)))).of_eq
    (fun _ => rfl)

theorem polyFun_rawNewItems : PolyFun (fun p : RawTable × RawPerm => rawNewItems p.1 p.2) := by
  have hpair : PolyFun (fun w : RawPerm × RawPerm =>
      [rawMul (w.1, w.2), rawMul (w.2, w.1)]) := by
    have h2 : PolyFun (fun w : RawPerm × RawPerm => rawMul (w.2, w.1)) :=
      (polyFun_snd.pair polyFun_fst).comp polyFun_rawMul
    exact (polyFun_rawMul.pair ((h2.pair (polyFun_nil (β := RawPerm))).comp polyFun_cons)).comp
      polyFun_cons
  have hin : PolyFun (fun p : RawTable × RawPerm =>
      ((p.2, rawEntries p.1) : RawPerm × List RawPerm)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_rawEntries)
  refine ((hin.comp (PolyFun.mapParam hpair)).comp polyFun_flatten).of_eq (fun p => ?_)
  show ((rawEntries p.1).map (fun e => [rawMul (p.2, e), rawMul (e, p.2)])).flatten
      = rawNewItems p.1 p.2
  rw [rawNewItems, flatMap_eq_flatten_map]

set_option maxHeartbeats 1000000 in
/-- **Sifting with a report is a `RAM.PolyFun`.**  The accumulator is bounded by
`Algo.rawStuckFold_struct`, exactly as `Algo.polyFun_rawSift` is bounded by
`Algo.rawSiftFold_struct`: the residue is as long as the start and its entries are entries of
the start or of the inverse of a table entry, and the reported level is one of the levels
walked, hence an entry of the list of rounds. -/
theorem polyFun_rawSiftStuck : PolyFun rawSiftStuck := by
  obtain ⟨c, d, hc⟩ := polyFun_rawInv.size
  have hacc : ∀ (cc : RawTable) (x : Option (ℕ × RawPerm) × RawPerm) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawStuckStep (cc, (y, a))) x (r.take j))
        ≤ (fun m => 4 * m + 6 * (1 + m * (2 * (m + c * (m + 1) ^ d) + 1)) + 4)
            (Enc.size ((cc, (x, r)) :
              RawTable × ((Option (ℕ × RawPerm) × RawPerm) × List ℕ))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) :
      RawTable × ((Option (ℕ × RawPerm) × RawPerm) × List ℕ)) with hN
    have hcc : Enc.size cc ≤ N :=
      Combine.size_fst_le cc ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ)
    have hxr : Enc.size ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hr : Enc.size r ≤ N := le_trans (Combine.size_snd_le x r) hxr
    have hS : ∀ τ : RawPerm, TableEntry cc τ → ∀ y ∈ rawInv τ,
        Enc.size y ≤ N + c * (N + 1) ^ d := by
      intro τ hτ y hy
      have h1 : Enc.size y ≤ Enc.size (rawInv τ) := size_mem_le hy
      have h2 : Enc.size (rawInv τ) ≤ c * (Enc.size τ + 1) ^ d := hc τ
      have h3 : Enc.size τ ≤ N := le_trans (size_le_of_tableEntry hτ) hcc
      have h4 : (Enc.size τ + 1) ^ d ≤ (N + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      have h5 := Nat.mul_le_mul_left c h4
      omega
    obtain ⟨o, r₀⟩ := x
    have hr₀ : Enc.size r₀ ≤ N :=
      le_trans (Combine.size_snd_le o r₀) hx
    cases o with
    | some z =>
        rw [rawStuckFold_frozen]
        dsimp only
        omega
    | none =>
        set F := List.foldl (fun y a => rawStuckStep (cc, (y, a)))
          (((none : Option (ℕ × RawPerm)), r₀)) (r.take j) with hF
        obtain ⟨⟨hlen, hmem⟩, hrep⟩ := rawStuckFold_struct cc (r.take j) r₀
        rw [← hF] at hlen hmem hrep
        have hentry : ∀ y ∈ F.2, Enc.size y ≤ N + c * (N + 1) ^ d := by
          intro y hy
          rcases hmem y hy with h | ⟨τ, hτ, h⟩
          · have h1 : Enc.size y ≤ Enc.size r₀ := size_mem_le h
            omega
          · exact hS τ hτ y h
        have hlen2 : F.2.length ≤ N := by
          have h1 : r₀.length ≤ Enc.size r₀ := length_le_size r₀
          omega
        have hsnd : Enc.size F.2 ≤ 1 + N * (2 * (N + c * (N + 1) ^ d) + 1) := by
          have h1 := size_list_le_of_entries F.2 (N + c * (N + 1) ^ d) hentry
          have h2 : F.2.length * (2 * (N + c * (N + 1) ^ d) + 1)
              ≤ N * (2 * (N + c * (N + 1) ^ d) + 1) := Nat.mul_le_mul_right _ hlen2
          omega
        have hfst : Enc.size F.1
            ≤ 2 * N + 2 * (1 + N * (2 * (N + c * (N + 1) ^ d) + 1)) + 2 := by
          rcases hres : F.1 with _ | ⟨i, ρ⟩
          · rw [size_none]
            omega
          · obtain ⟨hi, hρl, hρm⟩ := hrep i ρ hres
            have hiN : Enc.size i ≤ N := by
              have h1 : i ∈ r := List.take_subset j r hi
              have h2 : Enc.size i ≤ Enc.size r := size_mem_le h1
              omega
            have hρentry : ∀ y ∈ ρ, Enc.size y ≤ N + c * (N + 1) ^ d := by
              intro y hy
              rcases hρm y hy with h | ⟨τ, hτ, h⟩
              · have h1 : Enc.size y ≤ Enc.size r₀ := size_mem_le h
                omega
              · exact hS τ hτ y h
            have hρlen : ρ.length ≤ N := by
              have h1 : r₀.length ≤ Enc.size r₀ := length_le_size r₀
              omega
            have hρsize : Enc.size ρ ≤ 1 + N * (2 * (N + c * (N + 1) ^ d) + 1) := by
              have h1 := size_list_le_of_entries ρ (N + c * (N + 1) ^ d) hρentry
              have h2 : ρ.length * (2 * (N + c * (N + 1) ^ d) + 1)
                  ≤ N * (2 * (N + c * (N + 1) ^ d) + 1) := Nat.mul_le_mul_right _ hρlen
              omega
            have h3 : Enc.size ((i, ρ) : ℕ × RawPerm) ≤ 2 * Enc.size i + 2 * Enc.size ρ :=
              Combine.size_pair_le i ρ
            have h4 := size_some_eq ((i, ρ) : ℕ × RawPerm)
            omega
        have hpair : Enc.size F ≤ 2 * Enc.size F.1 + 2 * Enc.size F.2 :=
          Combine.size_pair_le F.1 F.2
        dsimp only
        omega
  have hfold := PolyFun.foldlParam polyFun_rawStuckStep
    (p := fun m => 4 * m + 6 * (1 + m * (2 * (m + c * (m + 1) ^ d) + 1)) + 4)
    (((polyBound_const 4).mul polyBound_id).add
      (((polyBound_const 6).mul ((polyBound_const 1).add
        (polyBound_id.mul (((polyBound_const 2).mul
          (polyBound_id.add (polyBound_witness c d))).add (polyBound_const 1))))).add
        (polyBound_const 4)))
    hacc
  have hin : PolyFun (fun p : RawTable × RawPerm =>
      ((p.1, ((((none : Option (ℕ × RawPerm)), p.2) : Option (ℕ × RawPerm) × RawPerm),
        List.range p.2.length)) :
        RawTable × ((Option (ℕ × RawPerm) × RawPerm) × List ℕ))) :=
    polyFun_fst.pair (((polyFun_none (β := ℕ × RawPerm)).pair polyFun_snd).pair
      (polyFun_snd.comp polyFun_rangeLength))
  exact ((hin.comp hfold).comp polyFun_fst).of_eq (fun p => rfl)

/-- **One round of the closure loop is a `RAM.PolyFun`.**  The insertion is `Algo.rawInsert`,
which is why the table must already have the row (point 2 of the note on session 2 of work
package A4 in `Workspace/Algo/DESIGN.md`). -/
theorem polyFun_rawBuildRound : PolyFun rawBuildRound := by
  -- the branch where the sift reports a level: insert, then append the products
  have hins : PolyFun (fun v : (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable) =>
      rawInsert ((rawApply (v.1.2, v.1.1), v.1.2), (v.2.2, v.1.1))) :=
    ((((polyFun_fst.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst)).comp
        polyFun_rawApply).pair (polyFun_fst.comp polyFun_snd)).pair
      ((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst))
      |>.comp polyFun_rawInsert
  have hrest : PolyFun
      (fun u : RawTable × ((ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable)) =>
        u.2.2.1.2) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_snd
  have hnew : PolyFun
      (fun u : RawTable × ((ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable)) =>
        rawNewItems u.1 u.2.1.2) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_snd)).comp
      polyFun_rawNewItems
  have hafter : PolyFun
      (fun u : RawTable × ((ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable)) =>
        ((u.1, u.2.2.1.2 ++ rawNewItems u.1 u.2.1.2) : RawTable × List RawPerm)) :=
    polyFun_fst.pair ((hrest.pair hnew).comp polyFun_append)
  have hsome : PolyFun (fun v : (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable) =>
      ((rawInsert ((rawApply (v.1.2, v.1.1), v.1.2), (v.2.2, v.1.1)),
        v.2.1.2 ++ rawNewItems (rawInsert ((rawApply (v.1.2, v.1.1), v.1.2), (v.2.2, v.1.1)))
          v.1.2) : RawTable × List RawPerm)) := by
    refine ((hins.pair polyFun_id).comp hafter).of_eq (fun v => ?_)
    rfl
  have hnone : PolyFun (fun v : (RawPerm × List RawPerm) × RawTable =>
      ((v.2, v.1.2) : RawTable × List RawPerm)) :=
    polyFun_snd.pair ((polyFun_fst.comp polyFun_snd))
  have hcons : PolyFun (fun v : (RawPerm × List RawPerm) × RawTable =>
      rawBuildRound (v.2, v.1.1 :: v.1.2)) := by
    have hlook : PolyFun (fun v : (RawPerm × List RawPerm) × RawTable =>
        rawSiftStuck (v.2, v.1.1)) :=
      (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_rawSiftStuck
    refine ((hlook.pair polyFun_id).comp (PolyFun.optionElim hnone hsome)).of_eq (fun v => ?_)
    obtain ⟨⟨g, rest⟩, t⟩ := v
    rcases hst : rawSiftStuck (t, g) with _ | ⟨i, ρ⟩
    · rw [rawBuildRound_cons_none hst]; simp [hst]
    · rw [rawBuildRound_cons_some hst]; simp [hst]
  have hnil : PolyFun (fun t : RawTable => ((t, ([] : List RawPerm)) : RawTable × List RawPerm)) :=
    polyFun_id.pair polyFun_nil
  have hcases := PolyFun.listCases (α := RawPerm) (σ := RawTable) hnil hcons
  refine ((polyFun_snd.pair polyFun_fst).comp hcases).of_eq (fun st => ?_)
  obtain ⟨t, w⟩ := st
  cases w with
  | nil => rfl
  | cons g rest => rfl

end Algo
