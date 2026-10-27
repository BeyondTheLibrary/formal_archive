import Workspace.Machine.ListOps

/-!
# More list routines

`Workspace/Machine/ListOps.lean` builds the fold (`RAM.PolyFun.foldl`) and the three traversals
that need no parameter: `map`, `filter`, membership.  This file adds the operations the
algorithmic layer asks for in Sec. 4.7 of `Workspace/Algo/DESIGN.md`, item 2: indexing at an
index given as a machine natural, equality of two lists, lookup in a list of pairs, and the
traversals with a parameter.  Then the three index-building routines `range`, `zip` and `zipIdx`.

Every one of them is one instance of `RAM.PolyFun.foldl`: a `def` for one round, a closed form
for the fold, a bound on the accumulator, and the assembly.  The only new work each time is the
bound, because `RAM.PolyFun.foldl` will not take a fold whose accumulator may grow.

## A warning about `List.range`

`List.range n` for a machine natural `n` is **not** a `RAM.PolyFun`, and no statement below says
it is.  `RAM.Enc` encodes a natural `n` as the one-register list `[n]`, so
`Enc.size n = Nat.size n + 2`, about `log n` bits, while the encoding of `List.range n` occupies
more than `n` registers.  A routine producing it would write exponentially many registers in the
size of its input.  So the length has to arrive in a form that is already that long: a list.
`RAM.polyFun_rangeLength` takes `List.range l.length`, and `RAM.polyFun_rangeTake` takes
`List.range (min k l.length)`, where the cut-off `k` may be a machine natural because the answer
is never longer than `l`.  The same remark applies to `List.zipIdx`, which is built from
`RAM.polyFun_rangeLength` and so needs no bound at all.

## Main results

* sizes: `RAM.size_append_eq`, `RAM.size_reverse`, `RAM.size_list_le_of_entries`,
  `RAM.length_le_size`, `RAM.size_nat_le_of_le`, `RAM.size_zip_le`;
* indexing: `RAM.polyFun_getElem?`, `RAM.polyFun_optionGetD`, `RAM.polyFun_getD`;
* prefixes: `RAM.polyFun_take`;
* equality: `RAM.polyFun_listEq`, `RAM.polyFun_listNatEq`, `RAM.polyFun_listListNatEq`;
* lookup: `RAM.polyFun_lookup`, `RAM.polyFun_listLookup`;
* traversals with a parameter: `RAM.PolyFun.mapParam`, `RAM.PolyFun.filterParam`,
  `RAM.PolyFun.foldlParam`;
* indices: `RAM.polyFun_rangeLength`, `RAM.polyFun_rangeTake`, `RAM.polyFun_zip`,
  `RAM.polyFun_zipIdx`.
-/

namespace RAM

variable {α β γ σ : Type*}

/-! ## Sizes

Three facts used everywhere below: concatenation adds the sizes (minus the one length field that
is shared), reversal does not change the size, and a list of `n` entries of size at most `S` has
size at most `1 + n * (2 * S + 1)`. -/

theorem size_append_eq [Enc α] (u v : List α) :
    Enc.size (u ++ v) = Enc.size u + Enc.size v - 1 := by
  show listSize (encList Enc.encode (u ++ v)) = _
  rw [encList_append, listSize_append]
  rfl

theorem size_reverse [Enc α] (l : List α) : Enc.size l.reverse = Enc.size l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have h1 : Enc.size (t.reverse ++ [a]) = Enc.size t.reverse + Enc.size ([a] : List α) - 1 :=
        size_append_eq _ _
      have h2 : Enc.size (([a] : List α) ++ t) = Enc.size ([a] : List α) + Enc.size t - 1 :=
        size_append_eq _ _
      have h3 := one_le_size (([a] : List α))
      have h4 := one_le_size t
      have h5 : ([a] : List α) ++ t = a :: t := rfl
      rw [h5] at h2
      rw [List.reverse_cons, h1, ih]
      omega

/-- A list is at most as long as its encoding. -/
theorem length_le_size [Enc α] (l : List α) : l.length ≤ Enc.size l := by
  have h1 := length_le_rawLength l
  have h2 := rawLength_lt_size l
  omega

/-- A list of `n` entries, each of size at most `S`, has size at most `1 + n * (2 * S + 1)`. -/
theorem size_list_le_of_entries [Enc α] (l : List α) (S : ℕ) (h : ∀ a ∈ l, Enc.size a ≤ S) :
    Enc.size l ≤ 1 + l.length * (2 * S + 1) := by
  have hmain := listSize_encList_le l S h
  have hss : Nat.size S ≤ S := size_le_self S
  have hstep : l.length * (S + Nat.size S + 1) ≤ l.length * (2 * S + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hsz : Enc.size l = listSize (encList Enc.encode l) := rfl
  omega

/-- Encodings of naturals grow with the number. -/
theorem size_nat_le_of_le {a b : ℕ} (h : a ≤ b) : Enc.size a ≤ Enc.size b := by
  have h1 : Enc.size a = Nat.size a + 2 := Small.size_nat a
  have h2 : Enc.size b = Nat.size b + 2 := Small.size_nat b
  have h3 : Nat.size a ≤ Nat.size b := Nat.size_le_size h
  omega

theorem size_none [Enc α] : Enc.size (none : Option α) = 2 := by
  show listSize [0] = 2
  simp [listSize]

/-- The first and the second component of a pair are no larger than the pair. -/
theorem size_fst_le' [Enc α] [Enc β] (p : α × β) : Enc.size p.1 ≤ Enc.size p := by
  have := Combine.size_fst_le p.1 p.2
  simpa using this

theorem size_snd_le' [Enc α] [Enc β] (p : α × β) : Enc.size p.2 ≤ Enc.size p := by
  have := Combine.size_snd_le p.1 p.2
  simpa using this

theorem size_pair_le' [Enc α] [Enc β] (p : α × β) :
    Enc.size p ≤ 2 * Enc.size p.1 + 2 * Enc.size p.2 := by
  have := Combine.size_pair_le p.1 p.2
  simpa using this

/-! ## Indexing at a machine natural

The counter starts at `i + 1` and is decreased by one at each entry; the entry at which it
reaches `1` is the answer, and the counter then stays at `0`.  So the round is a single
conditional, and the accumulator is a natural no larger than `i + 1` together with an `Option`
holding either nothing or an entry of the list. -/

/-- One round of the search for the entry at a given index. -/
def getStep {α : Type*} (s : (ℕ × Option α) × α) : ℕ × Option α :=
  if s.1.1 = 1 then (0, some s.2) else (s.1.1 - 1, s.1.2)

theorem getStep_eq {α : Type*} (x : ℕ × Option α) (a : α) :
    getStep (x, a) = if x.1 = 1 then ((0 : ℕ), some a) else (x.1 - 1, x.2) := rfl

/-- Once the counter is `0` nothing changes any more. -/
theorem getStep_zero {α : Type*} : ∀ (l : List α) (o : Option α),
    List.foldl (fun y a => getStep (y, a)) ((0, o) : ℕ × Option α) l = (0, o) := by
  intro l
  induction l with
  | nil => intro o; rfl
  | cons a t ih =>
      intro o
      rw [List.foldl_cons, getStep_eq]
      simp only [if_neg (by decide : ¬ (0 : ℕ) = 1)]
      exact ih o

/-- **The closed form.**  Started at `i + 1` with no answer, the fold returns `l[i]?`. -/
theorem getStep_result {α : Type*} : ∀ (l : List α) (i : ℕ),
    (List.foldl (fun y a => getStep (y, a)) ((i + 1, (none : Option α)) : ℕ × Option α) l).2
      = l[i]? := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
      intro i
      rw [List.foldl_cons, getStep_eq]
      cases i with
      | zero =>
          have hif : (if (0 : ℕ) + 1 = 1 then ((0 : ℕ), some a)
              else ((0 : ℕ) + 1 - 1, (none : Option α))) = ((0 : ℕ), some a) := if_pos rfl
          rw [hif, getStep_zero]
          simp
      | succ j =>
          simp only [if_neg (by omega : ¬ j + 1 + 1 = 1)]
          simpa using ih j

/-- The counter never grows, and the answer is either the one it started with or an entry of the
list.  This is what bounds the accumulator. -/
theorem getStep_inv {α : Type*} : ∀ (l : List α) (x : ℕ × Option α),
    (List.foldl (fun y a => getStep (y, a)) x l).1 ≤ x.1 ∧
      ((List.foldl (fun y a => getStep (y, a)) x l).2 = x.2 ∨
        ∃ a ∈ l, (List.foldl (fun y a => getStep (y, a)) x l).2 = some a) := by
  intro l
  induction l with
  | nil => intro x; exact ⟨le_refl _, Or.inl rfl⟩
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, getStep_eq]
      by_cases hx : x.1 = 1
      · rw [if_pos hx]
        obtain ⟨h1, h2⟩ := ih ((0 : ℕ), some a)
        refine ⟨by simp only at h1; omega, ?_⟩
        rcases h2 with h2 | ⟨b, hb, h2⟩
        · exact Or.inr ⟨a, List.mem_cons_self .., h2⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, h2⟩
      · rw [if_neg hx]
        obtain ⟨h1, h2⟩ := ih (x.1 - 1, x.2)
        refine ⟨by simp only at h1; omega, ?_⟩
        rcases h2 with h2 | ⟨b, hb, h2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, h2⟩

theorem getStep_size_bound [Enc α] (x : ℕ × Option α) (r : List α) (j : ℕ) :
    Enc.size (List.foldl (fun y a => getStep (y, a)) x (r.take j))
      ≤ 6 * Enc.size ((x, r) : (ℕ × Option α) × List α) + 4 := by
  obtain ⟨hk, ho⟩ := getStep_inv (r.take j) x
  set F := List.foldl (fun y a => getStep (y, a)) x (r.take j) with hF
  have hpair := size_pair_le' F
  have hsz1 : Enc.size F.1 ≤ Enc.size x.1 := size_nat_le_of_le hk
  have hx1 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
  have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
  have hA : Enc.size x ≤ Enc.size ((x, r) : (ℕ × Option α) × List α) := Combine.size_fst_le x r
  have hB : Enc.size r ≤ Enc.size ((x, r) : (ℕ × Option α) × List α) := Combine.size_snd_le x r
  have hsz2 : Enc.size F.2 ≤ Enc.size x.2 + Enc.size r + 2 := by
    rcases ho with h | ⟨a, ha, h⟩
    · rw [h]; omega
    · rw [h, size_some_eq]
      have h1 : Enc.size a ≤ Enc.size (r.take j) := size_mem_le ha
      have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
      omega
  omega

theorem polyFun_getStep [Enc α] : PolyFun (getStep : (ℕ × Option α) × α → ℕ × Option α) := by
  have hcond : PolyFun (fun s : (ℕ × Option α) × α => decide (s.1.1 = 1)) :=
    (polyFun_fst.comp polyFun_fst).natEq (polyFun_const 1)
  have ht : PolyFun (fun s : (ℕ × Option α) × α => (((0 : ℕ), some s.2) : ℕ × Option α)) :=
    (polyFun_const 0).pair (polyFun_snd.comp polyFun_some)
  have he : PolyFun (fun s : (ℕ × Option α) × α => ((s.1.1 - 1, s.1.2) : ℕ × Option α)) :=
    ((polyFun_fst.comp polyFun_fst).sub (polyFun_const 1)).pair (polyFun_fst.comp polyFun_snd)
  refine (PolyFun.ite hcond ht he).of_eq (fun s => ?_)
  by_cases h : s.1.1 = 1 <;> simp [getStep, h]

/-- **Indexing a list at an index given as a machine natural is a `PolyFun`.** -/
theorem polyFun_getElem? [Enc α] : PolyFun (fun p : List α × ℕ => p.1[p.2]?) := by
  have hfold := PolyFun.foldl (polyFun_getStep (α := α)) (p := fun n => 6 * n + 4)
    (((polyBound_const 6).mul polyBound_id).add (polyBound_const 4))
    (fun x r j => getStep_size_bound x r j)
  have hin : PolyFun (fun p : List α × ℕ =>
      (((p.2 + 1, (none : Option α)) : ℕ × Option α), p.1)) :=
    ((polyFun_snd.add (polyFun_const 1)).pair (polyFun_const none)).pair polyFun_fst
  refine ((hin.comp hfold).comp polyFun_snd).of_eq (fun p => ?_)
  exact getStep_result p.1 p.2

/-- The default value of an `Option`. -/
theorem polyFun_optionGetD [Enc α] : PolyFun (fun q : Option α × α => q.1.getD q.2) := by
  refine (PolyFun.optionElim (g := (id : α → α)) (h := (Prod.fst : α × α → α))
    polyFun_id polyFun_fst).of_eq (fun q => ?_)
  obtain ⟨o, a⟩ := q
  cases o <;> rfl

/-- **Indexing with a default value.** -/
theorem polyFun_getD [Enc α] : PolyFun (fun p : (List α × ℕ) × α => p.1.1.getD p.1.2 p.2) := by
  refine (((polyFun_fst.comp polyFun_getElem?).pair polyFun_snd).comp
    polyFun_optionGetD).of_eq (fun p => ?_)
  simp [List.getD]

/-! ## Taking a prefix at a machine natural

The counter starts at `k` and stops the copying when it reaches `0`. -/

/-- One round of `take`. -/
def takeStep {α : Type*} (s : (ℕ × List α) × α) : ℕ × List α :=
  if s.1.1 = 0 then s.1 else (s.1.1 - 1, s.2 :: s.1.2)

theorem takeStep_eq {α : Type*} (x : ℕ × List α) (a : α) :
    takeStep (x, a) = if x.1 = 0 then x else (x.1 - 1, a :: x.2) := rfl

/-- **The closed form**: the prefix, reversed, on top of the accumulator. -/
theorem takeStep_result {α : Type*} : ∀ (l : List α) (k : ℕ) (acc : List α),
    List.foldl (fun y a => takeStep (y, a)) ((k, acc) : ℕ × List α) l
      = (k - l.length, (l.take k).reverse ++ acc) := by
  intro l
  induction l with
  | nil => intro k acc; simp
  | cons a t ih =>
      intro k acc
      rw [List.foldl_cons, takeStep_eq]
      cases k with
      | zero => rw [if_pos rfl, ih]; simp
      | succ k =>
          rw [if_neg (by omega : ¬ k + 1 = 0), ih]
          simp

theorem takeStep_size_bound [Enc α] (x : ℕ × List α) (r : List α) (j : ℕ) :
    Enc.size (List.foldl (fun y a => takeStep (y, a)) x (r.take j))
      ≤ 6 * Enc.size ((x, r) : (ℕ × List α) × List α) := by
  obtain ⟨k, acc⟩ := x
  rw [takeStep_result]
  have hpair := Combine.size_pair_le (k - (r.take j).length)
    (((r.take j).take k).reverse ++ acc)
  have hk : Enc.size (k - (r.take j).length) ≤ Enc.size k :=
    size_nat_le_of_le (Nat.sub_le _ _)
  have hacc : Enc.size (((r.take j).take k).reverse ++ acc)
      ≤ Enc.size (((r.take j).take k).reverse) + Enc.size acc := size_append_le _ _
  have hrev : Enc.size (((r.take j).take k).reverse) = Enc.size ((r.take j).take k) :=
    size_reverse _
  have h1 : Enc.size ((r.take j).take k) ≤ Enc.size (r.take j) := size_take_le k _
  have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
  have hk' : Enc.size k ≤ Enc.size ((k, acc) : ℕ × List α) :=
    Combine.size_fst_le k acc
  have hacc' : Enc.size acc ≤ Enc.size ((k, acc) : ℕ × List α) :=
    Combine.size_snd_le k acc
  have hA : Enc.size ((k, acc) : ℕ × List α)
      ≤ Enc.size (((k, acc), r) : (ℕ × List α) × List α) := Combine.size_fst_le _ r
  have hB : Enc.size r ≤ Enc.size (((k, acc), r) : (ℕ × List α) × List α) :=
    Combine.size_snd_le _ r
  omega

theorem polyFun_takeStep [Enc α] : PolyFun (takeStep : (ℕ × List α) × α → ℕ × List α) := by
  have hcond : PolyFun (fun s : (ℕ × List α) × α => decide (s.1.1 = 0)) :=
    (polyFun_fst.comp polyFun_fst).natEq (polyFun_const 0)
  have he : PolyFun (fun s : (ℕ × List α) × α => ((s.1.1 - 1, s.2 :: s.1.2) : ℕ × List α)) :=
    ((polyFun_fst.comp polyFun_fst).sub (polyFun_const 1)).pair
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_cons)
  refine (PolyFun.ite hcond polyFun_fst he).of_eq (fun s => ?_)
  by_cases h : s.1.1 = 0 <;> simp [takeStep, h]

/-- **Taking a prefix, at a length given as a machine natural, is a `PolyFun`.** -/
theorem polyFun_take [Enc α] : PolyFun (fun p : List α × ℕ => p.1.take p.2) := by
  have hfold := PolyFun.foldl (polyFun_takeStep (α := α)) (p := fun n => 6 * n)
    ((polyBound_const 6).mul polyBound_id) (fun x r j => takeStep_size_bound x r j)
  have hin : PolyFun (fun p : List α × ℕ => (((p.2, ([] : List α)) : ℕ × List α), p.1)) :=
    (polyFun_snd.pair polyFun_nil).pair polyFun_fst
  refine (((hin.comp hfold).comp polyFun_snd).comp polyFun_reverse).of_eq (fun p => ?_)
  rw [takeStep_result]
  simp


/-! ## Equality of two lists

The state of the traversal is a bit (the lists agree so far) together with what is left of the
second list.  The round takes the head of the second list off; when the second list is already
empty the bit is cleared, because the first list is then the longer one.  At the end the answer
is the bit together with the test that the rest of the second list is empty. -/

/-- One round of the comparison of two lists. -/
def eqStep {α : Type*} [DecidableEq α] (s : (Bool × List α) × α) : Bool × List α :=
  match s.1.2 with
  | [] => (false, [])
  | c :: m => ((s.1.1 && decide (s.2 = c)), m)

/-- **The closed form.**  What the traversal computes is exactly the equality test. -/
theorem eqStep_result {α : Type*} [DecidableEq α] : ∀ (l₁ l₂ : List α) (b : Bool),
    ((List.foldl (fun y a => eqStep (y, a)) ((b, l₂) : Bool × List α) l₁).1 &&
        (List.foldl (fun y a => eqStep (y, a)) ((b, l₂) : Bool × List α) l₁).2.isEmpty)
      = (b && decide (l₁ = l₂)) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ b; cases l₂ <;> simp
  | cons a t ih =>
      intro l₂ b
      cases l₂ with
      | nil =>
          have h : eqStep (((b, ([] : List α)), a)) = (false, ([] : List α)) := rfl
          rw [List.foldl_cons, h, ih [] false]
          simp
      | cons c m =>
          have h : eqStep (((b, c :: m), a)) = ((b && decide (a = c)), m) := rfl
          rw [List.foldl_cons, h, ih m (b && decide (a = c))]
          by_cases h1 : a = c <;> by_cases h2 : t = m <;> simp [h1, h2]

/-- The second component of the state only shrinks. -/
theorem eqStep_tail_size [Enc α] [DecidableEq α] : ∀ (l : List α) (x : Bool × List α),
    Enc.size (List.foldl (fun y a => eqStep (y, a)) x l).2 ≤ Enc.size x.2 := by
  intro l
  induction l with
  | nil => intro x; exact le_refl _
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      refine le_trans (ih (eqStep (x, a))) ?_
      obtain ⟨b, m⟩ := x
      cases m with
      | nil => exact le_refl _
      | cons c m' => exact size_tail_le (c :: m')

theorem eqStep_size_bound [Enc α] [DecidableEq α] (x : Bool × List α) (r : List α) (j : ℕ) :
    Enc.size (List.foldl (fun y a => eqStep (y, a)) x (r.take j))
      ≤ 2 * Enc.size ((x, r) : (Bool × List α) × List α) + 6 := by
  have h1 := eqStep_tail_size (r.take j) x
  set F := List.foldl (fun y a => eqStep (y, a)) x (r.take j) with hF
  have hpair := size_pair_le' F
  have hb : Enc.size F.1 ≤ 3 := Combine.size_bool_le _
  have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
  have hA : Enc.size x ≤ Enc.size ((x, r) : (Bool × List α) × List α) := Combine.size_fst_le x r
  omega

theorem polyFun_eqStep [Enc α] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (eqStep : (Bool × List α) × α → Bool × List α) := by
  have hg : PolyFun (fun _ : Bool × α => ((false, ([] : List α)) : Bool × List α)) :=
    polyFun_const _
  have hbit : PolyFun (fun q : (α × List α) × (Bool × α) =>
      (if q.2.1 then decide (q.2.2 = q.1.1) else false : Bool)) :=
    PolyFun.ite (polyFun_snd.comp polyFun_fst)
      (((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst)).comp heq)
      (polyFun_const false)
  have hh : PolyFun (fun q : (α × List α) × (Bool × α) =>
      (((q.2.1 && decide (q.2.2 = q.1.1) : Bool), q.1.2) : Bool × List α)) :=
    (hbit.pair (polyFun_fst.comp polyFun_snd)).of_eq (fun q => by
      cases h : q.2.1 <;> simp [h])
  have hin : PolyFun (fun s : (Bool × List α) × α =>
      ((s.1.2, ((s.1.1, s.2) : Bool × α)) : List α × (Bool × α))) :=
    (polyFun_fst.comp polyFun_snd).pair ((polyFun_fst.comp polyFun_fst).pair polyFun_snd)
  refine (hin.comp (PolyFun.listCases hg hh)).of_eq (fun s => ?_)
  obtain ⟨⟨b, m⟩, a⟩ := s
  cases m <;> rfl

/-- The test that a list is empty. -/
theorem polyFun_isEmpty [Enc α] : PolyFun (fun l : List α => l.isEmpty) := by
  have h := PolyFun.listCases (α := α) (σ := ℕ) (γ := Bool)
    (polyFun_const true) (polyFun_const false)
  refine ((polyFun_id.pair (polyFun_const (0 : ℕ))).comp h).of_eq (fun l => ?_)
  cases l <;> rfl

/-- **Equality of two lists is a `PolyFun`**, for an entry type with a `PolyFun` equality
test. -/
theorem polyFun_listEq [Enc α] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (fun p : List α × List α => decide (p.1 = p.2)) := by
  have hfold := PolyFun.foldl (polyFun_eqStep heq) (p := fun n => 2 * n + 6)
    (((polyBound_const 2).mul polyBound_id).add (polyBound_const 6))
    (fun x r j => eqStep_size_bound x r j)
  have hin : PolyFun (fun p : List α × List α => (((true, p.2) : Bool × List α), p.1)) :=
    ((polyFun_const true).pair polyFun_snd).pair polyFun_fst
  have hand : PolyFun (fun z : Bool × List α => (z.1 && z.2.isEmpty : Bool)) :=
    (PolyFun.ite polyFun_fst (polyFun_snd.comp polyFun_isEmpty)
      (polyFun_const false)).of_eq (fun z => by cases h : z.1 <;> simp [h])
  refine ((hin.comp hfold).comp hand).of_eq (fun p => ?_)
  have h := eqStep_result p.1 p.2 true
  simpa using h

/-- Equality of two lists of naturals. -/
theorem polyFun_listNatEq : PolyFun (fun p : List ℕ × List ℕ => decide (p.1 = p.2)) :=
  polyFun_listEq polyFun_natEq

/-- Equality of two lists of lists of naturals: a raw permutation list, a raw set, a raw
partition all live at these types. -/
theorem polyFun_listListNatEq :
    PolyFun (fun p : List (List ℕ) × List (List ℕ) => decide (p.1 = p.2)) :=
  polyFun_listEq polyFun_listNatEq

/-- Membership in a list of naturals. -/
theorem polyFun_natListMem : PolyFun (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2)) :=
  polyFun_listMem polyFun_natEq

/-! ## Lookup in a list of pairs

The state is the key together with the answer found so far.  Once an answer is found it is kept,
so the answer is the one belonging to the *first* matching key, which is what `List.find?` and
`List.lookup` return. -/

/-- One round of the lookup. -/
def lookupStep {α β : Type*} [DecidableEq α] (s : (α × Option β) × (α × β)) : α × Option β :=
  (s.1.1, match s.1.2 with
    | some b => some b
    | none => if s.2.1 = s.1.1 then some s.2.2 else none)

/-- **The closed form.** -/
theorem lookupStep_result {α β : Type*} [DecidableEq α] : ∀ (l : List (α × β)) (k : α)
    (o : Option β),
    List.foldl (fun y a => lookupStep (y, a)) ((k, o) : α × Option β) l
      = (k, match o with
            | some b => some b
            | none => (l.find? (fun q => decide (q.1 = k))).map Prod.snd) := by
  intro l
  induction l with
  | nil => intro k o; cases o <;> simp
  | cons a t ih =>
      intro k o
      rw [List.foldl_cons]
      cases o with
      | some b =>
          have h : lookupStep (((k, some b), a)) = (k, some b) := rfl
          rw [h, ih k (some b)]
      | none =>
          by_cases hk : a.1 = k
          · have h : lookupStep (((k, (none : Option β)), a)) = (k, some a.2) := by
              simp [lookupStep, hk]
            rw [h, ih k (some a.2)]
            simp [List.find?_cons, hk]
          · have h : lookupStep (((k, (none : Option β)), a)) = (k, (none : Option β)) := by
              simp [lookupStep, hk]
            rw [h, ih k none]
            simp [List.find?_cons, hk]

theorem lookupStep_size_bound [Enc α] [Enc β] [DecidableEq α] (x : α × Option β)
    (r : List (α × β)) (j : ℕ) :
    Enc.size (List.foldl (fun y a => lookupStep (y, a)) x (r.take j))
      ≤ 4 * Enc.size ((x, r) : (α × Option β) × List (α × β)) + 4 := by
  obtain ⟨k, o⟩ := x
  have hA : Enc.size ((k, o) : α × Option β)
      ≤ Enc.size (((k, o), r) : (α × Option β) × List (α × β)) := Combine.size_fst_le _ r
  have hB : Enc.size r ≤ Enc.size (((k, o), r) : (α × Option β) × List (α × β)) :=
    Combine.size_snd_le _ r
  have hk : Enc.size k ≤ Enc.size ((k, o) : α × Option β) := Combine.size_fst_le k o
  rw [lookupStep_result]
  cases o with
  | some b =>
      show Enc.size ((k, some b) : α × Option β) ≤ _
      omega
  | none =>
      simp only
      cases hfind : ((r.take j).find? (fun q => decide (q.1 = k))) with
      | none =>
          have hpair := Combine.size_pair_le k (none : Option β)
          have hnone : Enc.size (none : Option β) = 2 := size_none
          simp only [Option.map_none]
          omega
      | some a =>
          have hmem : a ∈ r.take j := List.mem_of_find?_eq_some hfind
          have h1 : Enc.size a ≤ Enc.size (r.take j) := size_mem_le hmem
          have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
          have h3 : Enc.size a.2 ≤ Enc.size a := size_snd_le' a
          have hpair := Combine.size_pair_le k (some a.2)
          have hsome : Enc.size (some a.2) = Enc.size a.2 + 2 := size_some_eq a.2
          simp only [Option.map_some]
          omega

theorem polyFun_lookupStep [Enc α] [Enc β] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (lookupStep : (α × Option β) × (α × β) → α × Option β) := by
  have hg : PolyFun (fun z : α × (α × β) =>
      (if z.2.1 = z.1 then some z.2.2 else none : Option β)) :=
    (PolyFun.ite (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp heq)
      ((polyFun_snd.comp polyFun_snd).comp polyFun_some) (polyFun_const none)).of_eq
      (fun z => by by_cases h : z.2.1 = z.1 <;> simp [h])
  have hh : PolyFun (fun z : β × (α × (α × β)) => (some z.1 : Option β)) :=
    polyFun_fst.comp polyFun_some
  have hin : PolyFun (fun s : (α × Option β) × (α × β) =>
      ((s.1.2, ((s.1.1, s.2) : α × (α × β))) : Option β × (α × (α × β)))) :=
    (polyFun_fst.comp polyFun_snd).pair ((polyFun_fst.comp polyFun_fst).pair polyFun_snd)
  refine ((polyFun_fst.comp polyFun_fst).pair
    (hin.comp (PolyFun.optionElim hg hh))).of_eq (fun s => ?_)
  obtain ⟨⟨k, o⟩, a⟩ := s
  cases o <;> rfl

/-- **Lookup in a list of pairs is a `PolyFun`**, for a key type with a `PolyFun` equality
test.  The answer is the value belonging to the first matching key. -/
theorem polyFun_lookup [Enc α] [Enc β] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (fun p : List (α × β) × α =>
      (p.1.find? (fun q => decide (q.1 = p.2))).map Prod.snd) := by
  have hfold := PolyFun.foldl (polyFun_lookupStep (β := β) heq) (p := fun n => 4 * n + 4)
    (((polyBound_const 4).mul polyBound_id).add (polyBound_const 4))
    (fun x r j => lookupStep_size_bound x r j)
  have hin : PolyFun (fun p : List (α × β) × α =>
      (((p.2, (none : Option β)) : α × Option β), p.1)) :=
    (polyFun_snd.pair (polyFun_const none)).pair polyFun_fst
  refine ((hin.comp hfold).comp polyFun_snd).of_eq (fun p => ?_)
  rw [lookupStep_result]

/-- `List.lookup` is the same function. -/
theorem lookup_eq_find? {α β : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (k : α) :
    ∀ l : List (α × β), l.lookup k = (l.find? (fun q => decide (q.1 = k))).map Prod.snd := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨c, b⟩ := a
      by_cases h : c = k
      · simp [List.lookup, List.find?_cons, h]
      · have hb : (k == c) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
        simp [List.lookup, hb, List.find?_cons, h, ih]

/-- **`List.lookup` is a `PolyFun`.** -/
theorem polyFun_listLookup [Enc α] [Enc β] [DecidableEq α] [BEq α] [LawfulBEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (fun p : List (α × β) × α => p.1.lookup p.2) :=
  (polyFun_lookup (β := β) heq).of_eq (fun p => (lookup_eq_find? p.2 p.1).symm)


/-- **A concrete instance**: a table with natural keys and list values, which is the shape a
lookup table of the algorithmic layer has.  Both `ℕ` and `List ℕ` are nonempty, so this
statement is not vacuous. -/
theorem polyFun_natLookup : PolyFun (fun p : List (ℕ × List ℕ) × ℕ => p.1.lookup p.2) :=
  polyFun_listLookup polyFun_natEq

/-! ## Traversals with a parameter

A routine of the paper almost never maps a fixed function over a list: it maps a function of the
list entry *and* of some data fixed for the whole call — the domain size, the current window, the
group.  The fold of `Workspace/Machine/ListOps.lean` takes only a fixed function, so the
parameter has to travel inside the accumulator.  It is carried unchanged, which is the content of
`RAM.foldl_param_eq`: a fold whose round leaves the first component alone is the fold of the
second component with that first component frozen. -/

/-- A fold that carries its first component unchanged is the fold of the second component. -/
theorem foldl_param_eq {γ α σ : Type*} (F : γ → σ → α → σ) : ∀ (l : List α) (x : γ × σ),
    List.foldl (fun y a => ((y.1, F y.1 y.2 a) : γ × σ)) x l
      = (x.1, List.foldl (fun y a => F x.1 y a) x.2 l) := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.foldl_cons]

theorem foldl_mapParam_eq {γ α β : Type*} (f : γ × α → β) : ∀ (l : List α) (x : γ × List β),
    List.foldl (fun y a => ((y.1, f (y.1, a) :: y.2) : γ × List β)) x l
      = (x.1, List.foldl (fun y a => f (x.1, a) :: y) x.2 l) :=
  foldl_param_eq (fun cc y a => f (cc, a) :: y)

set_option maxHeartbeats 1000000 in
/-- **Mapping a two-argument `PolyFun` over a list, with the first argument held fixed, is a
`PolyFun`.**  No hypothesis beyond `hf` is needed, for the same reason as in `RAM.PolyFun.map`:
the size bound carried by `hf` bounds every value `f (c, a)` with `a` an entry of the list, and
`RAM.size_list_le_of_entries` turns that into a bound on the whole image. -/
theorem PolyFun.mapParam [Enc α] [Enc β] [Enc γ] {f : γ × α → β} (hf : PolyFun f) :
    PolyFun (fun p : γ × List α => p.2.map (fun a => f (p.1, a))) := by
  obtain ⟨c, d, hc⟩ := hf.size
  have hMb : PolyBound (fun n => c * (4 * n + 1) ^ d) :=
    (polyBound_witness c d).comp ((polyBound_const 4).mul polyBound_id)
  have hpb : PolyBound (fun n => 2 * n + 2 * (n + (1 + n * (2 * (c * (4 * n + 1) ^ d) + 1)))) :=
    ((polyBound_const 2).mul polyBound_id).add ((polyBound_const 2).mul
      (polyBound_id.add ((polyBound_const 1).add
        (polyBound_id.mul (((polyBound_const 2).mul hMb).add (polyBound_const 1))))))
  have hstep : PolyFun (fun z : (γ × List β) × α =>
      ((z.1.1, f (z.1.1, z.2) :: z.1.2) : γ × List β)) :=
    (polyFun_fst.comp polyFun_fst).pair
      (((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp hf).pair
        (polyFun_fst.comp polyFun_snd)).comp polyFun_cons)
  have hacc : ∀ (x : γ × List β) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => ((y.1, f (y.1, a) :: y.2) : γ × List β)) x (r.take j))
        ≤ (fun n => 2 * n + 2 * (n + (1 + n * (2 * (c * (4 * n + 1) ^ d) + 1))))
            (Enc.size ((x, r) : (γ × List β) × List α)) := by
    intro x r j
    rw [foldl_mapParam_eq]
    set N := Enc.size ((x, r) : (γ × List β) × List α) with hN
    have hx : Enc.size x ≤ N := Combine.size_fst_le x r
    have hr : Enc.size r ≤ N := Combine.size_snd_le x r
    have hx1 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
    have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
    have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have hentry : ∀ b ∈ (r.take j).map (fun a => f (x.1, a)),
        Enc.size b ≤ c * (4 * N + 1) ^ d := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
      have h1 : Enc.size a ≤ Enc.size (r.take j) := size_mem_le ha
      have h3 : Enc.size ((x.1, a) : γ × α) ≤ 2 * Enc.size x.1 + 2 * Enc.size a :=
        Combine.size_pair_le _ _
      have h4 := hc ((x.1, a) : γ × α)
      have h5 : (Enc.size ((x.1, a) : γ × α) + 1) ^ d ≤ (4 * N + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h6 := Nat.mul_le_mul_left c h5
      omega
    have hmaplen : ((r.take j).map (fun a => f (x.1, a))).length = (r.take j).length :=
      List.length_map _
    have hmap : Enc.size ((r.take j).map (fun a => f (x.1, a)))
        ≤ 1 + N * (2 * (c * (4 * N + 1) ^ d) + 1) := by
      have h1 := size_list_le_of_entries ((r.take j).map (fun a => f (x.1, a)))
        (c * (4 * N + 1) ^ d) hentry
      have h2 : (r.take j).length ≤ Enc.size (r.take j) := length_le_size _
      have h3 : (r.take j).length * (2 * (c * (4 * N + 1) ^ d) + 1)
          ≤ N * (2 * (c * (4 * N + 1) ^ d) + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [hmaplen] at h1
      omega
    have hW := size_foldl_map_cons_le (fun a => f (x.1, a)) (r.take j) x.2
    have hpair := Combine.size_pair_le x.1
      (List.foldl (fun y a => f (x.1, a) :: y) x.2 (r.take j))
    dsimp only
    omega
  have hfold := PolyFun.foldl hstep hpb hacc
  have hin : PolyFun (fun p : γ × List α => (((p.1, ([] : List β)) : γ × List β), p.2)) :=
    (polyFun_fst.pair polyFun_nil).pair polyFun_snd
  refine (((hin.comp hfold).comp polyFun_snd).comp polyFun_reverse).of_eq (fun p => ?_)
  rw [foldl_mapParam_eq]
  dsimp only
  rw [foldl_map_cons_eq]
  simp

theorem foldl_filterParam_eq {γ α : Type*} (q : γ × α → Bool) : ∀ (l : List α) (x : γ × List α),
    List.foldl (fun y a => ((y.1, if q (y.1, a) then a :: y.2 else y.2) : γ × List α)) x l
      = (x.1, List.foldl (fun y a => if q (x.1, a) then a :: y else y) x.2 l) :=
  foldl_param_eq (fun cc y a => if q (cc, a) then a :: y else y)

/-- **Filtering by a two-argument `PolyFun` predicate, with the first argument held fixed.** -/
theorem PolyFun.filterParam [Enc α] [Enc γ] {q : γ × α → Bool} (hq : PolyFun q) :
    PolyFun (fun p : γ × List α => p.2.filter (fun a => q (p.1, a))) := by
  have hstep : PolyFun (fun z : (γ × List α) × α =>
      ((z.1.1, if q (z.1.1, z.2) then z.2 :: z.1.2 else z.1.2) : γ × List α)) :=
    (polyFun_fst.comp polyFun_fst).pair
      (PolyFun.ite (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp hq)
        ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_cons)
        (polyFun_fst.comp polyFun_snd))
  have hacc : ∀ (x : γ × List α) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a =>
          ((y.1, if q (y.1, a) then a :: y.2 else y.2) : γ × List α)) x (r.take j))
        ≤ (fun n => 6 * n) (Enc.size ((x, r) : (γ × List α) × List α)) := by
    intro x r j
    rw [foldl_filterParam_eq]
    have hx : Enc.size x ≤ Enc.size ((x, r) : (γ × List α) × List α) := Combine.size_fst_le x r
    have hr : Enc.size r ≤ Enc.size ((x, r) : (γ × List α) × List α) := Combine.size_snd_le x r
    have hx1 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
    have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
    have hW := size_foldl_filter_cons_le (fun a => q (x.1, a)) (r.take j) x.2
    have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have hpair := Combine.size_pair_le x.1
      (List.foldl (fun y a => if q (x.1, a) then a :: y else y) x.2 (r.take j))
    dsimp only
    omega
  have hfold := PolyFun.foldl hstep ((polyBound_const 6).mul polyBound_id) hacc
  have hin : PolyFun (fun p : γ × List α => (((p.1, ([] : List α)) : γ × List α), p.2)) :=
    (polyFun_fst.pair polyFun_nil).pair polyFun_snd
  refine (((hin.comp hfold).comp polyFun_snd).comp polyFun_reverse).of_eq (fun p => ?_)
  rw [foldl_filterParam_eq]
  dsimp only
  rw [foldl_filter_cons_eq]
  simp

theorem foldl_foldlParam_eq {γ α σ : Type*} (f : γ × (σ × α) → σ) :
    ∀ (l : List α) (x : γ × σ),
    List.foldl (fun y a => ((y.1, f (y.1, (y.2, a))) : γ × σ)) x l
      = (x.1, List.foldl (fun y a => f (x.1, (y, a))) x.2 l) :=
  foldl_param_eq (fun cc y a => f (cc, (y, a)))

/-- Regrouping a triple costs at most a factor ten in the size. -/
theorem size_assoc_le [Enc γ] [Enc σ] [Enc α] (cc : γ) (x : σ) (r : List α) :
    Enc.size ((cc, (x, r)) : γ × (σ × List α))
      ≤ 10 * Enc.size (((cc, x), r) : (γ × σ) × List α) := by
  have h1 := Combine.size_pair_le cc ((x, r) : σ × List α)
  have h2 := Combine.size_pair_le x r
  have h3 : Enc.size ((cc, x) : γ × σ) ≤ Enc.size (((cc, x), r) : (γ × σ) × List α) :=
    Combine.size_fst_le _ r
  have h4 : Enc.size r ≤ Enc.size (((cc, x), r) : (γ × σ) × List α) := Combine.size_snd_le _ r
  have h5 : Enc.size cc ≤ Enc.size ((cc, x) : γ × σ) := Combine.size_fst_le cc x
  have h6 : Enc.size x ≤ Enc.size ((cc, x) : γ × σ) := Combine.size_snd_le cc x
  omega

/-- **Folding with a parameter.**  The hypothesis `hacc` is the bound on the accumulator, as in
`RAM.PolyFun.foldl`; it is stated in the size of the whole input `(c, (x, r))`. -/
theorem PolyFun.foldlParam [Enc α] [Enc γ] [Enc σ] {f : γ × (σ × α) → σ} (hf : PolyFun f)
    {p : ℕ → ℕ} (hpb : PolyBound p)
    (hacc : ∀ (cc : γ) (x : σ) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => f (cc, (y, a))) x (r.take j))
        ≤ p (Enc.size ((cc, (x, r)) : γ × (σ × List α)))) :
    PolyFun (fun z : γ × (σ × List α) =>
      List.foldl (fun y a => f (z.1, (y, a))) z.2.1 z.2.2) := by
  obtain ⟨c, d, hcd⟩ := hpb
  have hstep : PolyFun (fun w : (γ × σ) × α => ((w.1.1, f (w.1.1, (w.1.2, w.2))) : γ × σ)) :=
    (polyFun_fst.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp hf)
  have hpb' : PolyBound (fun n => 2 * n + 2 * (c * (10 * n + 1) ^ d)) :=
    ((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul ((polyBound_witness c d).comp
        ((polyBound_const 10).mul polyBound_id)))
  have hacc' : ∀ (x : γ × σ) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => ((y.1, f (y.1, (y.2, a))) : γ × σ)) x (r.take j))
        ≤ (fun n => 2 * n + 2 * (c * (10 * n + 1) ^ d))
            (Enc.size ((x, r) : (γ × σ) × List α)) := by
    intro x r j
    rw [foldl_foldlParam_eq]
    obtain ⟨cc, y⟩ := x
    have h1 := hacc cc y r j
    have h2 := size_assoc_le cc y r
    have h3 := hcd (Enc.size ((cc, (y, r)) : γ × (σ × List α)))
    have h4 : (Enc.size ((cc, (y, r)) : γ × (σ × List α)) + 1) ^ d
        ≤ (10 * Enc.size (((cc, y), r) : (γ × σ) × List α) + 1) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    have h5 := Nat.mul_le_mul_left c h4
    have hpair := Combine.size_pair_le cc
      (List.foldl (fun yy a => f (cc, (yy, a))) y (r.take j))
    have h6 : Enc.size cc ≤ Enc.size (((cc, y), r) : (γ × σ) × List α) := by
      have ha : Enc.size cc ≤ Enc.size ((cc, y) : γ × σ) := Combine.size_fst_le cc y
      have hb : Enc.size ((cc, y) : γ × σ) ≤ Enc.size (((cc, y), r) : (γ × σ) × List α) :=
        Combine.size_fst_le _ r
      omega
    dsimp only
    omega
  have hfold := PolyFun.foldl hstep hpb' hacc'
  have hin : PolyFun (fun z : γ × (σ × List α) =>
      ((((z.1, z.2.1) : γ × σ)), z.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair (polyFun_snd.comp polyFun_snd)
  refine ((hin.comp hfold).comp polyFun_snd).of_eq (fun z => ?_)
  rw [foldl_foldlParam_eq]

/-! ## Ranges, `zip` and `zipIdx`

The round of `range` appends the current length, so the accumulator is `0, 1, ..., j - 1`
reversed and nothing has to be counted separately.  Read the warning in the header of this file
about `List.range` on a bare machine natural. -/

/-- One round of `range`: append the number of entries produced so far. -/
def rangeStep {α : Type*} (s : List ℕ × α) : List ℕ := s.1.length :: s.1

/-- **The closed form.**  Started at an arbitrary accumulator `x`, the fold stacks
`x.length, x.length + 1, ...` on top of it. -/
theorem rangeStep_result {α : Type*} : ∀ (l : List α) (x : List ℕ),
    List.foldl (fun y a => rangeStep (y, a)) x l
      = (List.range' x.length l.length).reverse ++ x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      have h : rangeStep (x, a) = x.length :: x := rfl
      rw [h, ih]
      simp [List.range'_succ]

theorem rangeStep_size_bound [Enc α] (x : List ℕ) (r : List α) (j : ℕ) :
    Enc.size (List.foldl (fun y a => rangeStep (y, a)) x (r.take j))
      ≤ 1 + (Enc.size ((x, r) : List ℕ × List α)
          * (4 * Enc.size ((x, r) : List ℕ × List α) + 5)
        + Enc.size ((x, r) : List ℕ × List α)) := by
  rw [rangeStep_result]
  set N := Enc.size ((x, r) : List ℕ × List α) with hN
  have hx : Enc.size x ≤ N := Combine.size_fst_le x r
  have hr : Enc.size r ≤ N := Combine.size_snd_le x r
  have hxl : x.length ≤ N := le_trans (length_le_size x) hx
  have hm : (r.take j).length ≤ N := by
    have h1 : (r.take j).length ≤ r.length := by
      rw [List.length_take]; exact min_le_right _ _
    have h2 : r.length ≤ Enc.size r := length_le_size r
    omega
  have hentry : ∀ a ∈ List.range' x.length (r.take j).length, Enc.size a ≤ 2 * N + 2 := by
    intro a ha
    have h := List.mem_range'_1.1 ha
    have h1 : Nat.size a ≤ a := size_le_self a
    have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
    omega
  have hlen : (List.range' x.length (r.take j).length).length = (r.take j).length :=
    List.length_range'
  have hrange := size_list_le_of_entries (List.range' x.length (r.take j).length)
    (2 * N + 2) hentry
  rw [hlen] at hrange
  have hmul : (r.take j).length * (2 * (2 * N + 2) + 1) ≤ N * (4 * N + 5) := by
    have h7 := Nat.mul_le_mul_right (2 * (2 * N + 2) + 1) hm
    have harith : N * (2 * (2 * N + 2) + 1) = N * (4 * N + 5) := by ring
    omega
  have happ := size_append_le ((List.range' x.length (r.take j).length).reverse) x
  have hrev : Enc.size ((List.range' x.length (r.take j).length).reverse)
      = Enc.size (List.range' x.length (r.take j).length) := size_reverse _
  omega

theorem polyFun_rangeStep [Enc α] : PolyFun (rangeStep : List ℕ × α → List ℕ) :=
  ((polyFun_fst.comp polyFun_length).pair polyFun_fst).comp polyFun_cons

/-- **`List.range l.length` is a `PolyFun` of `l`.**  The length arrives as a list, whose
encoding is at least that long, so the answer is polynomially bounded.  `List.range n` for a
machine natural `n` is *not* a `PolyFun`; see the header of this file. -/
theorem polyFun_rangeLength [Enc α] : PolyFun (fun l : List α => List.range l.length) := by
  have hfold := PolyFun.foldl (polyFun_rangeStep (α := α))
    (p := fun n => 1 + (n * (4 * n + 5) + n))
    ((polyBound_const 1).add ((polyBound_id.mul
      (((polyBound_const 4).mul polyBound_id).add (polyBound_const 5))).add polyBound_id))
    (fun x r j => rangeStep_size_bound x r j)
  have hin : PolyFun (fun l : List α => (([] : List ℕ), l)) := polyFun_nil.pair polyFun_id
  refine ((hin.comp hfold).comp polyFun_reverse).of_eq (fun l => ?_)
  rw [rangeStep_result]
  simp [List.range_eq_range']

/-- **The range cut off at a machine natural.**  Here the cut-off may be a machine natural,
because the answer is never longer than the list. -/
theorem polyFun_rangeTake [Enc α] :
    PolyFun (fun p : List α × ℕ => List.range (min p.2 p.1.length)) := by
  refine (((polyFun_fst.comp polyFun_rangeLength).pair polyFun_snd).comp
    polyFun_take).of_eq (fun p => ?_)
  exact List.take_range ..

/-- One round of `zip`: take the head of the second list, if there is one. -/
def zipStep {α β : Type*} (s : (List (α × β) × List β) × α) : List (α × β) × List β :=
  match s.1.2 with
  | [] => (s.1.1, [])
  | b :: m => ((s.2, b) :: s.1.1, m)

/-- **The closed form.** -/
theorem zipStep_result {α β : Type*} : ∀ (l : List α) (acc : List (α × β)) (m : List β),
    List.foldl (fun y a => zipStep (y, a)) ((acc, m) : List (α × β) × List β) l
      = ((l.zip m).reverse ++ acc, m.drop l.length) := by
  intro l
  induction l with
  | nil => intro acc m; simp
  | cons a t ih =>
      intro acc m
      rw [List.foldl_cons]
      cases m with
      | nil =>
          have h : zipStep (((acc, ([] : List β)), a)) = (acc, ([] : List β)) := rfl
          rw [h, ih]
          simp
      | cons b m =>
          have h : zipStep (((acc, b :: m), a)) = ((a, b) :: acc, m) := rfl
          rw [h, ih]
          simp

/-- The size of a `zip`: at most `min` many pairs, each no larger than the two lists. -/
theorem size_zip_le [Enc α] [Enc β] (u : List α) (v : List β) :
    Enc.size (u.zip v) ≤ 1 + Enc.size u * (2 * (2 * Enc.size u + 2 * Enc.size v) + 1) := by
  have hentry : ∀ q ∈ u.zip v, Enc.size q ≤ 2 * Enc.size u + 2 * Enc.size v := by
    intro q hq
    obtain ⟨h1, h2⟩ := List.of_mem_zip hq
    have h3 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := size_pair_le' q
    have h4 : Enc.size q.1 ≤ Enc.size u := size_mem_le h1
    have h5 : Enc.size q.2 ≤ Enc.size v := size_mem_le h2
    omega
  have h := size_list_le_of_entries (u.zip v) _ hentry
  have hlen : (u.zip v).length ≤ u.length := by
    rw [List.length_zip]; exact min_le_left _ _
  have hlen2 : u.length ≤ Enc.size u := length_le_size u
  have h6 := Nat.mul_le_mul_right (2 * (2 * Enc.size u + 2 * Enc.size v) + 1)
    (le_trans hlen hlen2)
  omega

theorem zipStep_size_bound [Enc α] [Enc β] (x : List (α × β) × List β) (r : List α) (j : ℕ) :
    Enc.size (List.foldl (fun y a => zipStep (y, a)) x (r.take j))
      ≤ 2 * (1 + Enc.size ((x, r) : (List (α × β) × List β) × List α)
          * (8 * Enc.size ((x, r) : (List (α × β) × List β) × List α) + 1)
        + Enc.size ((x, r) : (List (α × β) × List β) × List α))
        + 2 * Enc.size ((x, r) : (List (α × β) × List β) × List α) := by
  obtain ⟨acc, m⟩ := x
  rw [zipStep_result]
  set N := Enc.size (((acc, m), r) : (List (α × β) × List β) × List α) with hN
  have hx : Enc.size ((acc, m) : List (α × β) × List β) ≤ N := Combine.size_fst_le _ r
  have hr : Enc.size r ≤ N := Combine.size_snd_le _ r
  have hacc : Enc.size acc ≤ Enc.size ((acc, m) : List (α × β) × List β) :=
    Combine.size_fst_le acc m
  have hm : Enc.size m ≤ Enc.size ((acc, m) : List (α × β) × List β) :=
    Combine.size_snd_le acc m
  have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
  have hzip := size_zip_le (r.take j) m
  have hzipN : Enc.size (r.take j) * (2 * (2 * Enc.size (r.take j) + 2 * Enc.size m) + 1)
      ≤ N * (8 * N + 1) := by
    have h1 : 2 * (2 * Enc.size (r.take j) + 2 * Enc.size m) + 1 ≤ 8 * N + 1 := by omega
    exact Nat.mul_le_mul (by omega) h1
  have happ := size_append_le (((r.take j).zip m).reverse) acc
  have hrev : Enc.size (((r.take j).zip m).reverse) = Enc.size ((r.take j).zip m) :=
    size_reverse _
  have hdrop : Enc.size (m.drop (r.take j).length) ≤ Enc.size m := size_drop_le _ m
  have hpair := Combine.size_pair_le ((((r.take j).zip m).reverse ++ acc))
    (m.drop (r.take j).length)
  omega

theorem polyFun_zipStep [Enc α] [Enc β] :
    PolyFun (zipStep : (List (α × β) × List β) × α → List (α × β) × List β) := by
  have hg : PolyFun (fun z : List (α × β) × α =>
      ((z.1, ([] : List β)) : List (α × β) × List β)) := polyFun_fst.pair polyFun_nil
  have hh : PolyFun (fun z : (β × List β) × (List (α × β) × α) =>
      (((z.2.2, z.1.1) :: z.2.1, z.1.2) : List (α × β) × List β)) :=
    ((((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst)).pair
      (polyFun_snd.comp polyFun_fst)).comp polyFun_cons).pair
      (polyFun_fst.comp polyFun_snd)
  have hin : PolyFun (fun s : (List (α × β) × List β) × α =>
      ((s.1.2, ((s.1.1, s.2) : List (α × β) × α)) : List β × (List (α × β) × α))) :=
    (polyFun_fst.comp polyFun_snd).pair ((polyFun_fst.comp polyFun_fst).pair polyFun_snd)
  refine (hin.comp (PolyFun.listCases hg hh)).of_eq (fun s => ?_)
  obtain ⟨⟨acc, m⟩, a⟩ := s
  cases m <;> rfl

/-- **`List.zip` is a `PolyFun`.** -/
theorem polyFun_zip [Enc α] [Enc β] : PolyFun (fun p : List α × List β => p.1.zip p.2) := by
  have hfold := PolyFun.foldl (polyFun_zipStep (α := α) (β := β))
    (p := fun n => 2 * (1 + n * (8 * n + 1) + n) + 2 * n)
    (((polyBound_const 2).mul (((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 8).mul polyBound_id).add
        (polyBound_const 1)))).add polyBound_id)).add
      ((polyBound_const 2).mul polyBound_id))
    (fun x r j => zipStep_size_bound x r j)
  have hin : PolyFun (fun p : List α × List β =>
      (((([] : List (α × β)), p.2) : List (α × β) × List β), p.1)) :=
    (polyFun_nil.pair polyFun_snd).pair polyFun_fst
  refine (((hin.comp hfold).comp polyFun_fst).comp polyFun_reverse).of_eq (fun p => ?_)
  rw [zipStep_result]
  simp

/-- **`List.zipIdx` is a `PolyFun`.**  This is the numbering of the entries of a list, in
Mathlib's current spelling; the older name is `List.enum`. -/
theorem polyFun_zipIdx [Enc α] : PolyFun (fun l : List α => l.zipIdx) := by
  refine ((polyFun_id.pair polyFun_rangeLength).comp polyFun_zip).of_eq (fun l => ?_)
  simp [List.zipIdx_eq_zip_range', List.range_eq_range']

end RAM
