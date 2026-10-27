/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the running time of the Schreier–Sims closure loop.
-/
import Workspace.Algo.ChainBuildRaw

/-!
# The closure loop runs in polynomial time

`Workspace/Algo/ChainBuildRaw.lean` proves that one round of the closure loop is a
`RAM.PolyFun` (`Algo.polyFun_rawBuildRound`).  The loop itself is a `List.foldl` over
`Algo.rawFuelList`, and `RAM.PolyFun.foldl` asks for a bound on the accumulator **from an
arbitrary start state**, not only from the state the real run begins in.  That is the whole
content of this file.

## The invariant

From an arbitrary start the naive bound is exponential: one round appends two products per
stored entry to the work list, so the work list could double.  What saves it is that the two
quantities that *could* blow up — the lengths of the stored permutations and the sizes of the
numbers they contain — do not grow at all, while the two that do grow — the number of stored
entries and the length of the work list — grow by a fixed additive amount per round.  The
invariant `Algo.BuildInv B V E W` therefore has four parameters:

* `B` bounds the number of rows of the table and the length of every permutation, stored or
  pending.  One round does not change it: a residue has the length of the item it came from
  (`Algo.length_rawMul`), the insertion is a `map` over the rows, and a product has the length
  of its right factor.
* `V` bounds `Enc.size` of every *number* that occurs: a key, or a letter of a stored or
  pending permutation.  One round does not change it either, as soon as `B + 2 ≤ V`: the new
  letters come from the inverse of a stored permutation, and those are indices into it, hence
  below `B`, hence of encoding size at most `B + 2`.  Note that `V` bounds `Enc.size y` and not
  `y`: a machine natural can be exponentially large in its encoding, so no invariant of the
  form "every value is at most `N`" is available.
* `E` bounds the number of stored entries; one round adds at most one entry per row, so
  `E ↦ E + B`.
* `W` bounds the length of the work list; one round removes one item and appends two products
  per stored entry, so `W ↦ W + 2(E + B)`.

After `k` rounds this gives `E + k·B` and `W + 2k(E + k·B)`, and `k` is at most the length of
the list folded over, hence at most the size of the input.  All four are then polynomial in the
input size, and `Algo.buildSize` turns them into a bound on `Enc.size` of the state.

## Main results

* `Algo.BuildInv`, `Algo.BuildInv.rawBuildRound`, `Algo.BuildInv.iterate`;
* `Algo.size_le_of_buildInv`;
* `Algo.polyFun_rawBuildTable`, `Algo.polyFun_rawMem`.

No axiom and no `sorry`.
-/

namespace Algo

open RAM

/-! ## Where the parts of the state live

Four membership facts: a stored permutation is a second component of an entry of the flattened
table; the letters of an inverse are indices, hence small; `Algo.rawApply` returns a letter or
its own argument; and the insertion adds at most one entry per row. -/

/-- A table entry occurs in the flattened table. -/
theorem mem_flatten_of_tableEntry {t : RawTable} {τ : RawPerm} (h : TableEntry t τ) :
    ∃ k : ℕ, (k, τ) ∈ t.flatten := by
  obtain ⟨i, j, hij⟩ := h
  rw [rawTableGet] at hij
  have hrow : t.getD i [] ∈ t := by
    by_cases hi : i < t.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hij
      exact absurd hij (by simp [List.lookup])
  exact ⟨j, List.mem_flatten.2 ⟨_, hrow, mem_of_lookup_eq_some _ _ _ hij⟩⟩

/-- **The letters of an inverse are indices.**  `Algo.rawInv l` is built by looking up each
index in the table `l.zipIdx`, so each of its letters is either a position of `l` or the
default `0`. -/
theorem mem_rawInv_le {l : RawPerm} {y : ℕ} (h : y ∈ rawInv l) : y ≤ l.length := by
  rw [rawInv, List.mem_map] at h
  obtain ⟨j, -, hy⟩ := h
  rw [rawInvLookup] at hy
  rcases hl : l.zipIdx.lookup j with _ | v
  · rw [hl] at hy
    simp only [Option.getD_none] at hy
    omega
  · rw [hl] at hy
    simp only [Option.getD_some] at hy
    have hmem : (j, v) ∈ l.zipIdx := mem_of_lookup_eq_some _ _ _ hl
    have : v < l.length := List.snd_lt_of_mem_zipIdx hmem
    omega

/-- The encoding size of a natural below `B` is at most `B + 2`. -/
theorem size_nat_le_succ_succ {y B : ℕ} (h : y ≤ B) : Enc.size y ≤ B + 2 := by
  have h1 : Enc.size y = Nat.size y + 2 := Small.size_nat y
  have h2 : Nat.size y ≤ y := size_le_self y
  omega

/-- `Algo.rawApply` returns a letter of its permutation or the point itself. -/
theorem rawApply_mem_or_eq (l : RawPerm) (i : ℕ) : rawApply (l, i) ∈ l ∨ rawApply (l, i) = i := by
  by_cases hi : i < l.length
  · left
    show l.getD i i ∈ l
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · right
    exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)

/-! ## The insertion

`Algo.rawInsert` is a `map` over the rows, so it preserves the number of rows, adds at most one
entry per row, and every entry of the result is the new one or an old one. -/

theorem length_rawInsert (q : ℕ × RawPerm) (t : RawTable) (i : ℕ) :
    (rawInsert (q, (t, i))).length = t.length := by
  rw [rawInsert]
  simp

theorem mem_flatten_rawInsert {q x : ℕ × RawPerm} {t : RawTable} {i : ℕ}
    (h : x ∈ (rawInsert (q, (t, i))).flatten) : x = q ∨ x ∈ t.flatten := by
  rw [rawInsert, List.mem_flatten] at h
  obtain ⟨u, hu, hxu⟩ := h
  rw [List.mem_map] at hu
  obtain ⟨z, hz, rfl⟩ := hu
  have hz1 : z.1 ∈ t := by
    have : z.1 ∈ t.zipIdx.map Prod.fst := List.mem_map.2 ⟨z, hz, rfl⟩
    rwa [List.zipIdx_map_fst] at this
  by_cases hzi : z.2 = i
  · rw [if_pos hzi] at hxu
    rcases List.mem_cons.1 hxu with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_flatten.2 ⟨z.1, hz1, h⟩)
  · rw [if_neg hzi] at hxu
    exact Or.inr (List.mem_flatten.2 ⟨z.1, hz1, hxu⟩)

theorem length_flatten_map_ite {α : Type*} (q : α) (i : ℕ) : ∀ L : List (List α × ℕ),
    ((L.map (fun z => if z.2 = i then q :: z.1 else z.1)).flatten).length
      ≤ ((L.map Prod.fst).flatten).length + L.length := by
  intro L
  induction L with
  | nil => simp
  | cons z L ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, List.map_cons,
        List.flatten_cons, List.length_append, List.length_cons]
      by_cases hzi : z.2 = i
      · rw [if_pos hzi, List.length_cons]
        omega
      · rw [if_neg hzi]
        omega

/-- **The insertion adds at most one entry per row.**  The crude count is enough: the number of
rows never grows, so `E ↦ E + B` still gives a polynomial after polynomially many rounds. -/
theorem length_flatten_rawInsert (q : ℕ × RawPerm) (t : RawTable) (i : ℕ) :
    (rawInsert (q, (t, i))).flatten.length ≤ t.flatten.length + t.length := by
  have h := length_flatten_map_ite q i t.zipIdx
  rw [List.zipIdx_map_fst] at h
  simpa [rawInsert] using h

/-! ## The new items -/

theorem length_rawNewItems (t : RawTable) (ρ : RawPerm) :
    (rawNewItems t ρ).length = 2 * t.flatten.length := by
  rw [rawNewItems, length_flatMap_pair, rawEntries, List.length_map]

theorem mem_rawNewItems {t : RawTable} {ρ σ : RawPerm} (h : σ ∈ rawNewItems t ρ) :
    ∃ e : RawPerm, (∃ k : ℕ, (k, e) ∈ t.flatten) ∧
      (σ = rawMul (ρ, e) ∨ σ = rawMul (e, ρ)) := by
  rw [rawNewItems, List.mem_flatMap] at h
  obtain ⟨e, he, hσ⟩ := h
  rw [rawEntries, List.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  refine ⟨q.2, ⟨q.1, by simpa using hq⟩, ?_⟩
  rcases List.mem_cons.1 hσ with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

/-! ## The report of the sift

`Algo.rawStuckFold_struct` describes the accumulator of the reporting sift from an arbitrary
start.  This is the form the loop needs. -/

theorem rawSiftStuck_struct {t : RawTable} {g : RawPerm} {i : ℕ} {ρ : RawPerm}
    (h : rawSiftStuck (t, g) = some (i, ρ)) :
    i < g.length ∧ ρ.length = g.length ∧
      ∀ y ∈ ρ, y ∈ g ∨ ∃ τ, TableEntry t τ ∧ y ∈ rawInv τ := by
  obtain ⟨-, hrep⟩ := rawStuckFold_struct t (List.range g.length) g
  have h' : (List.foldl (fun a j => rawStuckStep (t, (a, j)))
      (((none : Option (ℕ × RawPerm)), g)) (List.range g.length)).1 = some (i, ρ) := h
  obtain ⟨hi, hl, hm⟩ := hrep i ρ h'
  exact ⟨List.mem_range.1 hi, hl, hm⟩

/-! ## The invariant -/

/-- **The invariant of the closure loop.**  `B` bounds the number of rows and the length of
every permutation, `V` bounds the encoding size of every number, `E` the number of stored
entries and `W` the length of the work list.  The last clause `B + 2 ≤ V` is what makes `V`
survive a round: a letter of an inverse is an index into a stored permutation. -/
structure BuildInv (B V E W : ℕ) (st : RawTable × List RawPerm) : Prop where
  rows : st.1.length ≤ B
  entries : st.1.flatten.length ≤ E
  keySize : ∀ q ∈ st.1.flatten, Enc.size q.1 ≤ V
  entryLen : ∀ q ∈ st.1.flatten, q.2.length ≤ B
  entrySize : ∀ q ∈ st.1.flatten, ∀ y ∈ q.2, Enc.size y ≤ V
  work : st.2.length ≤ W
  workLen : ∀ σ ∈ st.2, σ.length ≤ B
  workSize : ∀ σ ∈ st.2, ∀ y ∈ σ, Enc.size y ≤ V
  gap : B + 2 ≤ V

/-- The two counters may be relaxed. -/
theorem BuildInv.mono {B V E E' W W' : ℕ} {st : RawTable × List RawPerm}
    (h : BuildInv B V E W st) (hE : E ≤ E') (hW : W ≤ W') : BuildInv B V E' W' st :=
  { h with entries := le_trans h.entries hE, work := le_trans h.work hW }

/-- **The branch of a round that inserts.**  Stated separately so that the new entry is one
variable `q`, which keeps the main proof readable. -/
theorem buildInv_insert {B V E W : ℕ} {t : RawTable} {rest : List RawPerm}
    (hrows : t.length ≤ B) (hent : t.flatten.length ≤ E)
    (hkey : ∀ x ∈ t.flatten, Enc.size x.1 ≤ V) (hlen : ∀ x ∈ t.flatten, x.2.length ≤ B)
    (hsz : ∀ x ∈ t.flatten, ∀ y ∈ x.2, Enc.size y ≤ V)
    (hw : rest.length + 1 ≤ W) (hwl : ∀ σ ∈ rest, σ.length ≤ B)
    (hws : ∀ σ ∈ rest, ∀ y ∈ σ, Enc.size y ≤ V) (hgap : B + 2 ≤ V)
    (q : ℕ × RawPerm) (i : ℕ)
    (hqk : Enc.size q.1 ≤ V) (hql : q.2.length ≤ B) (hqs : ∀ y ∈ q.2, Enc.size y ≤ V) :
    BuildInv B V (E + B) (W + 2 * (E + B))
      (rawInsert (q, (t, i)), rest ++ rawNewItems (rawInsert (q, (t, i))) q.2) := by
  have hflat : ∀ x ∈ (rawInsert (q, (t, i))).flatten,
      Enc.size x.1 ≤ V ∧ x.2.length ≤ B ∧ ∀ y ∈ x.2, Enc.size y ≤ V := by
    intro x hx
    rcases mem_flatten_rawInsert hx with rfl | hx'
    · exact ⟨hqk, hql, hqs⟩
    · exact ⟨hkey x hx', hlen x hx', hsz x hx'⟩
  have hEB : (rawInsert (q, (t, i))).flatten.length ≤ E + B := by
    have h1 := length_flatten_rawInsert q t i
    omega
  refine
    { rows := ?_
      entries := hEB
      keySize := fun x hx => (hflat x hx).1
      entryLen := fun x hx => (hflat x hx).2.1
      entrySize := fun x hx => (hflat x hx).2.2
      work := ?_
      workLen := ?_
      workSize := ?_
      gap := hgap }
  · show (rawInsert (q, (t, i))).length ≤ B
    rw [length_rawInsert]; exact hrows
  · show (rest ++ rawNewItems (rawInsert (q, (t, i))) q.2).length ≤ W + 2 * (E + B)
    rw [List.length_append, length_rawNewItems]
    omega
  · intro σ hσ
    rcases List.mem_append.1 hσ with hσ' | hσ'
    · exact hwl σ hσ'
    · obtain ⟨e, ⟨k, hk⟩, hor⟩ := mem_rawNewItems hσ'
      rcases hor with rfl | rfl
      · rw [length_rawMul]; exact (hflat (k, e) hk).2.1
      · rw [length_rawMul]; exact hql
  · intro σ hσ y hy
    rcases List.mem_append.1 hσ with hσ' | hσ'
    · exact hws σ hσ' y hy
    · obtain ⟨e, ⟨k, hk⟩, hor⟩ := mem_rawNewItems hσ'
      rcases hor with rfl | rfl
      · rcases mem_rawMul hy with hy' | hy'
        · exact hqs y hy'
        · exact (hflat (k, e) hk).2.2 y hy'
      · rcases mem_rawMul hy with hy' | hy'
        · exact (hflat (k, e) hk).2.2 y hy'
        · exact hqs y hy'

/-- **One round preserves the invariant**, with `E ↦ E + B` and `W ↦ W + 2(E + B)`. -/
theorem BuildInv.round {B V E W : ℕ} {st : RawTable × List RawPerm} (h : BuildInv B V E W st) :
    BuildInv B V (E + B) (W + 2 * (E + B)) (rawBuildRound st) := by
  obtain ⟨t, w⟩ := st
  cases w with
  | nil =>
      rw [rawBuildRound_nil]
      exact h.mono (by omega) (by omega)
  | cons g rest =>
      rcases hst : rawSiftStuck (t, g) with _ | ⟨i, ρ⟩
      · rw [rawBuildRound_cons_none hst]
        have hw : (g :: rest).length ≤ W := h.work
        rw [List.length_cons] at hw
        exact
          { rows := h.rows
            entries := le_trans h.entries (by omega)
            keySize := h.keySize
            entryLen := h.entryLen
            entrySize := h.entrySize
            work := by show rest.length ≤ W + 2 * (E + B); omega
            workLen := fun σ hσ => h.workLen σ (List.mem_cons_of_mem _ hσ)
            workSize := fun σ hσ => h.workSize σ (List.mem_cons_of_mem _ hσ)
            gap := h.gap }
      · rw [rawBuildRound_cons_some hst]
        obtain ⟨hi, hρlen, hρmem⟩ := rawSiftStuck_struct hst
        have hgmem : g ∈ g :: rest := List.mem_cons_self ..
        have hgB : g.length ≤ B := h.workLen g hgmem
        have hρB : ρ.length ≤ B := by omega
        have hρV : ∀ y ∈ ρ, Enc.size y ≤ V := by
          intro y hy
          rcases hρmem y hy with hy' | ⟨τ, hτ, hy'⟩
          · exact h.workSize g hgmem y hy'
          · obtain ⟨k, hk⟩ := mem_flatten_of_tableEntry hτ
            have h1 : y ≤ τ.length := mem_rawInv_le hy'
            have h2 : τ.length ≤ B := h.entryLen (k, τ) hk
            have h3 := size_nat_le_succ_succ (le_trans h1 h2)
            have h4 := h.gap
            omega
        have hkeyV : Enc.size (rawApply (ρ, i)) ≤ V := by
          rcases rawApply_mem_or_eq ρ i with hm | hm
          · exact hρV _ hm
          · rw [hm]
            have h3 := size_nat_le_succ_succ (le_of_lt (lt_of_lt_of_le hi hgB))
            have h4 := h.gap
            omega
        have hw : (g :: rest).length ≤ W := h.work
        rw [List.length_cons] at hw
        exact buildInv_insert h.rows h.entries h.keySize h.entryLen h.entrySize
          (by omega) (fun σ hσ => h.workLen σ (List.mem_cons_of_mem _ hσ))
          (fun σ hσ => h.workSize σ (List.mem_cons_of_mem _ hσ)) h.gap
          (rawApply (ρ, i), ρ) i hkeyV hρB hρV

/-- **The invariant after `k` rounds.** -/
theorem BuildInv.iterate {B V E W : ℕ} {st : RawTable × List RawPerm} (h : BuildInv B V E W st) :
    ∀ k : ℕ, BuildInv B V (E + k * B) (W + 2 * k * (E + k * B)) (rawBuildRound^[k] st) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hsucc : (k + 1) * B = k * B + B := by ring
      refine ih.round.mono (by omega) ?_
      have hexp : 2 * (k + 1) * (E + (k + 1) * B)
          = 2 * k * (E + k * B) + (2 * (k * B) + 2 * (E + k * B + B)) := by ring
      omega

/-! ## From the invariant to a bound on the encoding size -/

/-- A row of a list of lists is no longer than the flattened list. -/
theorem row_length_le_length_flatten {α : Type*} {row : List α} : ∀ {l : List (List α)},
    row ∈ l → row.length ≤ l.flatten.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons a s ih =>
      intro h
      rw [List.flatten_cons, List.length_append]
      rcases List.mem_cons.1 h with rfl | h'
      · omega
      · have := ih h'
        omega

/-- **The size of a state that satisfies the invariant.**  A permutation has at most `B`
letters of size at most `V`, an entry is a pair of a key and a permutation, a row holds at most
`E` entries, the table has at most `B` rows, and the work list holds at most `W`
permutations. -/
def buildSize (B V E W : ℕ) : ℕ :=
  2 * (1 + B * (2 * (1 + E * (2 * (2 * V + 2 * (1 + B * (2 * V + 1))) + 1)) + 1)) +
    2 * (1 + W * (2 * (1 + B * (2 * V + 1)) + 1))

theorem buildSize_mono {B V E W B' V' E' W' : ℕ} (hB : B ≤ B') (hV : V ≤ V') (hE : E ≤ E')
    (hW : W ≤ W') : buildSize B V E W ≤ buildSize B' V' E' W' := by
  unfold buildSize
  gcongr

theorem size_le_of_buildInv {B V E W : ℕ} {st : RawTable × List RawPerm}
    (h : BuildInv B V E W st) : Enc.size st ≤ buildSize B V E W := by
  unfold buildSize
  set P := 1 + B * (2 * V + 1) with hP
  have hperm : ∀ τ : RawPerm, τ.length ≤ B → (∀ y ∈ τ, Enc.size y ≤ V) → Enc.size τ ≤ P := by
    intro τ hl hs
    have h1 := size_list_le_of_entries τ V hs
    have h2 : τ.length * (2 * V + 1) ≤ B * (2 * V + 1) := Nat.mul_le_mul_right _ hl
    omega
  have hentry : ∀ q ∈ st.1.flatten, Enc.size q ≤ 2 * V + 2 * P := by
    intro q hq
    have h1 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := Combine.size_pair_le q.1 q.2
    have h2 : Enc.size q.2 ≤ P := hperm q.2 (h.entryLen q hq) (h.entrySize q hq)
    have h3 : Enc.size q.1 ≤ V := h.keySize q hq
    omega
  have hrow : ∀ row ∈ st.1, Enc.size row ≤ 1 + E * (2 * (2 * V + 2 * P) + 1) := by
    intro row hrow
    have hsub : ∀ q ∈ row, Enc.size q ≤ 2 * V + 2 * P := fun q hq =>
      hentry q (List.mem_flatten.2 ⟨row, hrow, hq⟩)
    have h1 := size_list_le_of_entries row (2 * V + 2 * P) hsub
    have h2 : row.length ≤ E := le_trans (row_length_le_length_flatten hrow) h.entries
    have h3 : row.length * (2 * (2 * V + 2 * P) + 1) ≤ E * (2 * (2 * V + 2 * P) + 1) :=
      Nat.mul_le_mul_right _ h2
    omega
  have htable : Enc.size st.1 ≤ 1 + B * (2 * (1 + E * (2 * (2 * V + 2 * P) + 1)) + 1) := by
    have h1 := size_list_le_of_entries st.1 (1 + E * (2 * (2 * V + 2 * P) + 1)) hrow
    have h2 : st.1.length * (2 * (1 + E * (2 * (2 * V + 2 * P) + 1)) + 1)
        ≤ B * (2 * (1 + E * (2 * (2 * V + 2 * P) + 1)) + 1) := Nat.mul_le_mul_right _ h.rows
    omega
  have hwork : Enc.size st.2 ≤ 1 + W * (2 * P + 1) := by
    have hsub : ∀ σ ∈ st.2, Enc.size σ ≤ P := fun σ hσ =>
      hperm σ (h.workLen σ hσ) (h.workSize σ hσ)
    have h1 := size_list_le_of_entries st.2 P hsub
    have h2 : st.2.length * (2 * P + 1) ≤ W * (2 * P + 1) := Nat.mul_le_mul_right _ h.work
    omega
  have hpair : Enc.size st ≤ 2 * Enc.size st.1 + 2 * Enc.size st.2 :=
    Combine.size_pair_le st.1 st.2
  omega

/-! ## The bound along the loop

The start state is arbitrary, so every parameter of the invariant is read off the input size
`N`: at most `N` rows and letters, encodings of size at most `N + 2`, at most `N` entries and
at most `N` pending items.  The number of rounds is the length of the list folded over, hence
again at most `N`. -/

/-- **Every state of size at most `N` satisfies the invariant with the four parameters read off
`N`.** -/
theorem buildInv_start {t : RawTable} {w : List RawPerm} {N : ℕ}
    (h : Enc.size ((t, w) : RawTable × List RawPerm) ≤ N) : BuildInv N (N + 2) N N (t, w) := by
  have ht : Enc.size t ≤ N := le_trans (Combine.size_fst_le t w) h
  have hw : Enc.size w ≤ N := le_trans (Combine.size_snd_le t w) h
  have hq : ∀ q ∈ t.flatten, Enc.size q ≤ N := by
    intro q hq
    rw [List.mem_flatten] at hq
    obtain ⟨row, hrow, hqrow⟩ := hq
    exact le_trans (le_trans (size_mem_le hqrow) (size_mem_le hrow)) ht
  have hσ : ∀ σ ∈ w, Enc.size σ ≤ N := fun σ hs => le_trans (size_mem_le hs) hw
  refine
    { rows := le_trans (length_le_size t) ht
      entries := le_trans (length_flatten_le_size t) ht
      keySize := ?_
      entryLen := ?_
      entrySize := ?_
      work := le_trans (length_le_size w) hw
      workLen := ?_
      workSize := ?_
      gap := le_refl _ }
  · intro q hqm
    have h1 : Enc.size q.1 ≤ Enc.size q := Combine.size_fst_le q.1 q.2
    have h2 := hq q hqm
    omega
  · intro q hqm
    have h1 : Enc.size q.2 ≤ Enc.size q := Combine.size_snd_le q.1 q.2
    have h2 := hq q hqm
    have h3 := length_le_size q.2
    omega
  · intro q hqm y hy
    have h1 : Enc.size q.2 ≤ Enc.size q := Combine.size_snd_le q.1 q.2
    have h2 := hq q hqm
    have h3 := size_mem_le hy
    omega
  · intro σ hs
    have h1 := hσ σ hs
    have h2 := length_le_size σ
    omega
  · intro σ hs y hy
    have h1 := hσ σ hs
    have h2 := size_mem_le hy
    omega

/-- The bound on the accumulator of the loop, as a function of the input size. -/
def buildBound (N : ℕ) : ℕ := buildSize N (N + 2) (N + N * N) (N + 2 * N * (N + N * N))

theorem polyBound_buildBound : PolyBound buildBound := by
  have hN : PolyBound (fun N : ℕ => N) := polyBound_id
  have hV : PolyBound (fun N : ℕ => N + 2) := hN.add (polyBound_const 2)
  have hE : PolyBound (fun N : ℕ => N + N * N) := hN.add (hN.mul hN)
  have hW : PolyBound (fun N : ℕ => N + 2 * N * (N + N * N)) :=
    hN.add (((polyBound_const 2).mul hN).mul hE)
  have hP : PolyBound (fun N : ℕ => 1 + N * (2 * (N + 2) + 1)) :=
    (polyBound_const 1).add (hN.mul (((polyBound_const 2).mul hV).add (polyBound_const 1)))
  have hQ : PolyBound (fun N : ℕ => 2 * (N + 2) + 2 * (1 + N * (2 * (N + 2) + 1))) :=
    ((polyBound_const 2).mul hV).add ((polyBound_const 2).mul hP)
  have hR : PolyBound (fun N : ℕ =>
      1 + (N + N * N) * (2 * (2 * (N + 2) + 2 * (1 + N * (2 * (N + 2) + 1))) + 1)) :=
    (polyBound_const 1).add (hE.mul (((polyBound_const 2).mul hQ).add (polyBound_const 1)))
  unfold buildBound buildSize
  exact ((polyBound_const 2).mul ((polyBound_const 1).add
      (hN.mul (((polyBound_const 2).mul hR).add (polyBound_const 1))))).add
    ((polyBound_const 2).mul ((polyBound_const 1).add
      (hW.mul (((polyBound_const 2).mul hP).add (polyBound_const 1)))))

/-- **The accumulator of the loop is polynomially bounded from an arbitrary start.**  This is
the hypothesis `RAM.PolyFun.foldl` asks for. -/
theorem size_foldl_rawBuildRound_le (x : RawTable × List RawPerm) (r : List ℕ) (j : ℕ) :
    Enc.size (List.foldl (fun y (_ : ℕ) => rawBuildRound y) x (r.take j))
      ≤ buildBound (Enc.size ((x, r) : (RawTable × List RawPerm) × List ℕ)) := by
  obtain ⟨t, w⟩ := x
  set N := Enc.size ((((t, w) : RawTable × List RawPerm), r) :
    (RawTable × List RawPerm) × List ℕ) with hN
  have hx : Enc.size ((t, w) : RawTable × List RawPerm) ≤ N := Combine.size_fst_le _ r
  have hr : Enc.size r ≤ N := Combine.size_snd_le _ r
  rw [foldl_const_eq]
  have hkN : (r.take j).length ≤ N := by
    have h1 : (r.take j).length ≤ r.length := List.length_take_le' j r
    have h2 : r.length ≤ Enc.size r := length_le_size r
    omega
  have hiter := (buildInv_start hx).iterate (r.take j).length
  have h1 : (r.take j).length * N ≤ N * N := Nat.mul_le_mul_right N hkN
  have h3 : N + (r.take j).length * N ≤ N + N * N := by omega
  have h4 : 2 * (r.take j).length * (N + (r.take j).length * N) ≤ 2 * N * (N + N * N) :=
    Nat.mul_le_mul (by omega) h3
  exact size_le_of_buildInv (hiter.mono h3 (by omega))

/-! ## The routines -/

theorem polyFun_rawBuildRoundFold :
    PolyFun (fun s : (RawTable × List RawPerm) × List ℕ =>
      List.foldl (fun y (_ : ℕ) => rawBuildRound y) s.1 s.2) :=
  PolyFun.foldl (f := fun z : (RawTable × List RawPerm) × ℕ => rawBuildRound z.1)
    (polyFun_fst.comp polyFun_rawBuildRound) polyBound_buildBound size_foldl_rawBuildRound_le

theorem polyFun_rawInitTable : PolyFun rawInitTable := by
  have hf : PolyFun (fun z : RawPerm × ℕ => [((z.2, z.1) : ℕ × RawPerm)]) :=
    ((polyFun_snd.pair polyFun_fst).pair (polyFun_nil (β := ℕ × RawPerm))).comp polyFun_cons
  exact ((polyFun_rawOne.pair polyFun_rawOne).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

theorem polyFun_rawSquare : PolyFun rawSquare :=
  (((polyFun_id.pair polyFun_id).comp
    (PolyFun.mapParam (polyFun_fst (α := List ℕ) (β := ℕ)))).comp polyFun_flatten).of_eq
    (fun _ => rfl)

theorem polyFun_rawFuelList : PolyFun rawFuelList := by
  have hsq : PolyFun (fun p : List ℕ × List RawPerm => rawSquare p.1) :=
    polyFun_fst.comp polyFun_rawSquare
  have hsq2 : PolyFun (fun p : List ℕ × List RawPerm => rawSquare (rawSquare p.1)) :=
    hsq.comp polyFun_rawSquare
  have hmap : PolyFun (fun p : List ℕ × List RawPerm => p.2.map (fun _ => (0 : ℕ))) :=
    polyFun_snd.comp (PolyFun.map (polyFun_const (α := RawPerm) 0))
  have h1 : PolyFun (fun p : List ℕ × List RawPerm =>
      rawSquare (rawSquare p.1) ++ rawSquare (rawSquare p.1)) :=
    (hsq2.pair hsq2).comp polyFun_append
  have h2 : PolyFun (fun p : List ℕ × List RawPerm =>
      rawSquare (rawSquare p.1) ++ rawSquare (rawSquare p.1) ++ rawSquare p.1) :=
    (h1.pair hsq).comp polyFun_append
  exact ((h2.pair hmap).comp polyFun_append).of_eq (fun _ => by rfl)

/-- **The closure loop is a `RAM.PolyFun`.**  This is the running time of Schreier–Sims: the
loop runs `Algo.buildFuel` rounds, each round is `Algo.polyFun_rawBuildRound`, and the
accumulator stays polynomially small by `Algo.size_foldl_rawBuildRound_le`. -/
theorem polyFun_rawBuildTable : PolyFun rawBuildTable := by
  have hin : PolyFun (fun p : List ℕ × List RawPerm =>
      ((((rawInitTable p.1, p.2) : RawTable × List RawPerm), rawFuelList p) :
        (RawTable × List RawPerm) × List ℕ)) :=
    ((polyFun_fst.comp polyFun_rawInitTable).pair polyFun_snd).pair polyFun_rawFuelList
  exact ((hin.comp polyFun_rawBuildRoundFold).comp polyFun_fst).of_eq (fun _ => rfl)

/-- **The membership test is a `RAM.PolyFun`.**  With `Algo.rawMem_spec` this closes the
class-D row "membership test in a permutation group" of `Workspace/Algo/DESIGN.md`, item 2. -/
theorem polyFun_rawMem : PolyFun rawMem := by
  have hsift : PolyFun (fun p : (List ℕ × List RawPerm) × RawPerm =>
      rawSift (rawBuildTable p.1, p.2)) :=
    ((polyFun_fst.comp polyFun_rawBuildTable).pair polyFun_snd).comp polyFun_rawSift
  have hnone : PolyFun (fun _ : (List ℕ × List RawPerm) × RawPerm => false) := polyFun_const false
  have hsome : PolyFun (fun v : RawPerm × ((List ℕ × List RawPerm) × RawPerm) =>
      rawPermEq (v.1, rawOne v.2.2)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_rawOne)).comp polyFun_rawPermEq
  refine ((hsift.pair polyFun_id).comp (PolyFun.optionElim hnone hsome)).of_eq (fun p => ?_)
  show _ = rawMem p
  rw [rawMem]
  rcases rawSift (rawBuildTable p.1, p.2) with _ | r <;> rfl

end Algo
