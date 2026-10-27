import Workspace.Machine.Build

/-!
# Folding a list

With the case analysis of `Workspace/Machine/Cases.lean` and the constructors of
`Workspace/Machine/Build.lean`, a list traversal is a bounded iteration of
`Workspace/Machine/Iterate.lean`: the state is the accumulator together with what is left of the
list, one round consumes the head, and `RAM.rawLength` is a bound on the number of rounds,
because a list is never longer than its encoding.

The one hypothesis a fold genuinely needs is a **bound on the accumulator along the fold**.  It
cannot be dropped: one clean step may double the length of its output, so without it the
accumulator, and with it the cost of one round, grows exponentially (`DESIGN.md`, "Doubts" item
3).  `RAM.PolyFun.foldl` therefore takes a polynomial bound on
`Enc.size (List.foldl f x (r.take j))`, uniformly in `j`.

Everything else in this file is that combinator applied.

## Main results

* `RAM.foldlStep`, `RAM.foldlStep_iterate`, `RAM.PolyFun.foldl`;
* `RAM.polyFun_foldlCons`, `RAM.polyFun_reverse`, `RAM.polyFun_append`;
* `RAM.polyFun_listMem`: membership, for a type with a `PolyFun` equality test;
* the size lemmas `RAM.size_cons_eq`, `RAM.size_take_le`, `RAM.size_append_le`,
  `RAM.size_foldl_cons_le`, `RAM.size_mem_le`.
-/

namespace RAM

variable {α β γ σ : Type*}

/-! ## Sizes of list operations -/

theorem encList_append {α : Type*} (f : α → List ℕ) (u v : List α) :
    encList f (u ++ v) = encList f u ++ encList f v := by
  induction u with
  | nil => simp [encList]
  | cons a t ih => simp [encList, ih, List.append_assoc]

theorem size_cons_eq [Enc α] (a : α) (u : List α) :
    Enc.size (a :: u) = listSize (frame (Enc.encode a)) + Enc.size u - 1 := by
  show listSize (frame (Enc.encode a) ++ encList Enc.encode u) = _
  rw [listSize_append]
  rfl

theorem one_le_size [Enc α] (a : α) : 1 ≤ Enc.size a := by
  have h := length_lt_listSize (Enc.encode a)
  have h2 : Enc.size a = listSize (Enc.encode a) := rfl
  omega

theorem one_le_listSize_frame (xs : List ℕ) : 1 ≤ listSize (frame xs) := by
  have := length_lt_listSize (frame xs); omega

theorem size_nil [Enc α] : Enc.size ([] : List α) = 1 := by
  show listSize (encList Enc.encode ([] : List α)) = 1
  simp [encList]

theorem size_take_le [Enc α] : ∀ (j : ℕ) (l : List α), Enc.size (l.take j) ≤ Enc.size l := by
  intro j
  induction j with
  | zero =>
      intro l
      rw [List.take_zero, size_nil]
      exact one_le_size l
  | succ j ih =>
      intro l
      cases l with
      | nil => rw [List.take_nil]
      | cons a t =>
          rw [List.take_succ_cons, size_cons_eq, size_cons_eq]
          have h1 := ih t
          have h2 := one_le_listSize_frame (Enc.encode a)
          have h3 := one_le_size (t.take j)
          have h4 := one_le_size t
          omega

theorem size_append_le [Enc α] (u v : List α) :
    Enc.size (u ++ v) ≤ Enc.size u + Enc.size v := by
  have h : Enc.size (u ++ v) = Enc.size u + Enc.size v - 1 := by
    show listSize (encList Enc.encode (u ++ v)) = _
    rw [encList_append, listSize_append]
    rfl
  have := one_le_size v
  omega

/-- An entry of a list is no larger than the list. -/
theorem size_mem_le [Enc α] {a : α} : ∀ {l : List α}, a ∈ l → Enc.size a ≤ Enc.size l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b t ih =>
      intro h
      rw [size_cons_eq]
      have hfr : listSize (frame (Enc.encode b))
          = Enc.size b + (Nat.size (Enc.encode b).length + 1) := listSize_frame _
      rcases List.mem_cons.1 h with rfl | h'
      · have := one_le_size t
        omega
      · have h1 := ih h'
        have h2 := one_le_listSize_frame (Enc.encode b)
        omega

/-- The accumulator of a fold that conses stays below the two inputs together. -/
theorem size_foldl_cons_le [Enc α] : ∀ (l : List α) (x : List α),
    Enc.size (List.foldl (fun y a => a :: y) x l) ≤ Enc.size x + Enc.size l := by
  intro l
  induction l with
  | nil => intro x; rw [List.foldl_nil]; omega
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      have h := ih (a :: x)
      have e1 : Enc.size (a :: x) = listSize (frame (Enc.encode a)) + Enc.size x - 1 :=
        size_cons_eq a x
      have e2 : Enc.size (a :: t) = listSize (frame (Enc.encode a)) + Enc.size t - 1 :=
        size_cons_eq a t
      have h2 := one_le_listSize_frame (Enc.encode a)
      have h3 := one_le_size x
      have h4 := one_le_size t
      omega

/-- A list is at most as long as the encoding of a pair that carries it. -/
theorem length_le_rawLength_pair [Enc σ] [Enc α] (x : σ) (r : List α) :
    r.length ≤ rawLength ((x, r) : σ × List α) := by
  have h1 : r.length ≤ (Enc.encode r).length := length_le_rawLength r
  have h2 : rawLength ((x, r) : σ × List α)
      = ((Enc.encode x).length + 1) + ((Enc.encode r).length + 1) := by
    show (frame (Enc.encode x) ++ frame (Enc.encode r)).length = _
    simp [frame]
    omega
  omega

/-! ## One round of a fold -/

/-- One round of a fold: consume the head of the list into the accumulator. -/
def foldlStep {α σ : Type*} (f : σ × α → σ) (s : σ × List α) : σ × List α :=
  match s.2 with
  | [] => s
  | a :: l => (f (s.1, a), l)

theorem foldlStep_iterate {α σ : Type*} (f : σ × α → σ) (j : ℕ) : ∀ (x : σ) (r : List α),
    (foldlStep f)^[j] (x, r)
      = (List.foldl (fun y a => f (y, a)) x (r.take j), r.drop j) := by
  induction j with
  | zero => intro x r; simp
  | succ j ih =>
      intro x r
      rw [Function.iterate_succ_apply]
      cases r with
      | nil =>
          have h : foldlStep f (x, ([] : List α)) = (x, ([] : List α)) := rfl
          rw [h, ih]
          simp
      | cons a t =>
          have h : foldlStep f (x, a :: t) = (f (x, a), t) := rfl
          rw [h, ih]
          simp

theorem polyFun_foldlStep [Enc α] [Enc σ] {f : σ × α → σ} (hf : PolyFun f) :
    PolyFun (foldlStep f) := by
  have hg : PolyFun (fun x : σ => (x, ([] : List α))) := polyFun_id.pair polyFun_nil
  have hh : PolyFun (fun q : (α × List α) × σ => (f (q.2, q.1.1), q.1.2)) :=
    ((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp hf).pair
      (polyFun_fst.comp polyFun_snd)
  have hcases := PolyFun.listCases hg hh
  refine (polyFun_swap.comp hcases).of_eq (fun s => ?_)
  obtain ⟨x, r⟩ := s
  cases r <;> rfl

/-! ## The fold -/

set_option maxHeartbeats 1000000 in
/-- **A fold over a list is a `PolyFun`.**  The hypothesis `hacc` is the bound on the
accumulator along the fold; it is the one thing that does not follow from `hf`. -/
theorem PolyFun.foldl [Enc α] [Enc σ] {f : σ × α → σ} (hf : PolyFun f) {p : ℕ → ℕ}
    (hpb : PolyBound p)
    (hacc : ∀ (x : σ) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => f (y, a)) x (r.take j))
        ≤ p (Enc.size ((x, r) : σ × List α))) :
    PolyFun (fun s : σ × List α => List.foldl (fun y a => f (y, a)) s.1 s.2) := by
  have hstepF : PolyFun (foldlStep f) := polyFun_foldlStep hf
  have hstep : PolyFun (fun z : ℕ × (σ × List α) => (z.1 - 1, foldlStep f z.2)) :=
    (PolyFun.sub polyFun_fst (polyFun_const 1)).pair (polyFun_snd.comp hstepF)
  have hk : PolyFun (fun a : σ × List α => (rawLength a, a)) :=
    polyFun_rawLength.pair polyFun_id
  have hbound : ∀ (a : σ × List α), ∀ j ≤ rawLength a,
      Enc.size ((rawLength a - j, (foldlStep f)^[j] a) : ℕ × (σ × List α))
        ≤ 4 * p (Enc.size a) + 6 * Enc.size a + 4 := by
    rintro ⟨x, r⟩ j _
    rw [foldlStep_iterate]
    set N : ℕ := Enc.size ((x, r) : σ × List α) with hN
    set X : ℕ := rawLength ((x, r) : σ × List α) - j with hX
    set Y : σ := List.foldl (fun y a => f (y, a)) x (r.take j) with hY
    set Z : List α := r.drop j with hZ
    have hraw : rawLength ((x, r) : σ × List α) < N := rawLength_lt_size _
    have hsX : Enc.size X ≤ N + 2 := by
      have h1 : Enc.size X = Nat.size X + 2 := Small.size_nat X
      have h2 : Nat.size X ≤ X := size_le_self X
      omega
    have hsY : Enc.size Y ≤ p N := hacc x r j
    have hsZ : Enc.size Z ≤ N :=
      le_trans (size_drop_le j r) (Combine.size_snd_le x r)
    have hpair : Enc.size ((Y, Z) : σ × List α) ≤ 2 * Enc.size Y + 2 * Enc.size Z :=
      Combine.size_pair_le Y Z
    have htop : Enc.size ((X, (Y, Z)) : ℕ × (σ × List α))
        ≤ 2 * Enc.size X + 2 * Enc.size ((Y, Z) : σ × List α) := Combine.size_pair_le _ _
    omega
  have hiter : PolyFun (fun a : σ × List α => (foldlStep f)^[rawLength a] a) :=
    PolyFun.iterate hstep hk (fun a => le_of_lt (rawLength_lt_size a)) polyBound_id
      hbound (((polyBound_const 4).mul hpb).add
        (((polyBound_const 6).mul polyBound_id).add (polyBound_const 4)))
  refine (hiter.comp polyFun_fst).of_eq (fun s => ?_)
  obtain ⟨x, r⟩ := s
  rw [foldlStep_iterate]
  have hle := length_le_rawLength_pair x r
  have ht : r.take (rawLength ((x, r) : σ × List α)) = r := List.take_of_length_le hle
  have hd : r.drop (rawLength ((x, r) : σ × List α)) = [] := List.drop_eq_nil_of_le hle
  rw [ht]

/-! ## Reversing and appending

`List.foldl (fun y a => a :: y) x l = l.reverse ++ x`, so one instance of the fold gives both
`List.reverse` and `(++)`. -/

theorem foldl_cons_eq {α : Type*} : ∀ (l : List α) (x : List α),
    List.foldl (fun y a => a :: y) x l = l.reverse ++ x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih => intro x; rw [List.foldl_cons, ih]; simp

theorem polyFun_foldlCons [Enc α] :
    PolyFun (fun s : List α × List α => List.foldl (fun y a => a :: y) s.1 s.2) := by
  have hf : PolyFun (fun q : List α × α => q.2 :: q.1) := polyFun_swap.comp polyFun_cons
  have hmain := PolyFun.foldl hf (p := fun n => 2 * n)
    ((polyBound_const 2).mul polyBound_id) (fun x r j => ?_)
  · exact hmain.of_eq (fun s => rfl)
  · have h1 : Enc.size (List.foldl (fun y a => a :: y) x (r.take j))
        ≤ Enc.size x + Enc.size (r.take j) := size_foldl_cons_le _ _
    have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h3 : Enc.size x ≤ Enc.size ((x, r) : List α × List α) := Combine.size_fst_le x r
    have h4 : Enc.size r ≤ Enc.size ((x, r) : List α × List α) := Combine.size_snd_le x r
    dsimp only
    omega

/-- **Reversing a list is a `PolyFun`.** -/
theorem polyFun_reverse [Enc α] : PolyFun (fun l : List α => l.reverse) := by
  have hin : PolyFun (fun l : List α => (([] : List α), l)) := polyFun_nil.pair polyFun_id
  refine (hin.comp polyFun_foldlCons).of_eq (fun l => ?_)
  show List.foldl (fun y a => a :: y) ([] : List α) l = l.reverse
  rw [foldl_cons_eq]
  simp

/-- **Concatenation of two lists is a `PolyFun`.** -/
theorem polyFun_append [Enc α] : PolyFun (fun p : List α × List α => p.1 ++ p.2) := by
  have hin : PolyFun (fun p : List α × List α => (p.2, p.1.reverse)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_reverse)
  refine (hin.comp polyFun_foldlCons).of_eq (fun p => ?_)
  show List.foldl (fun y a => a :: y) p.2 p.1.reverse = p.1 ++ p.2
  rw [foldl_cons_eq]
  simp

/-! ## Membership -/

/-- The fold that tests membership. -/
theorem memFold_eq {α : Type*} [DecidableEq α] : ∀ (l : List α) (b : Bool) (x : α),
    List.foldl (fun s a => ((s.1 || decide (s.2 = a) : Bool), s.2)) (b, x) l
      = ((b || decide (x ∈ l) : Bool), x) := by
  intro l
  induction l with
  | nil => intro b x; simp
  | cons a t ih =>
      intro b x
      rw [List.foldl_cons, ih]
      have hb : (decide (x = a) || decide (x ∈ t)) = decide (x ∈ a :: t) := by
        by_cases h1 : x = a <;> by_cases h2 : x ∈ t <;> simp [List.mem_cons, h1, h2]
      rw [Bool.or_assoc, hb]

/-- **Membership in a list is a `PolyFun`**, for a type with a `PolyFun` equality test. -/
theorem polyFun_listMem [Enc α] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) :
    PolyFun (fun p : α × List α => decide (p.1 ∈ p.2)) := by
  have hf : PolyFun (fun q : (Bool × α) × α => ((q.1.1 || decide (q.1.2 = q.2) : Bool), q.1.2)) := by
    have hcond : PolyFun (fun q : (Bool × α) × α => (if q.1.1 then true
        else decide (q.1.2 = q.2) : Bool)) :=
      PolyFun.ite (polyFun_fst.comp polyFun_fst) (polyFun_const true)
        (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp heq)
    exact (hcond.pair (polyFun_fst.comp polyFun_snd)).of_eq (fun q => by
      cases h : q.1.1 <;> simp [h])
  have hmain := PolyFun.foldl hf (p := fun n => 2 * n + 6)
    (((polyBound_const 2).mul polyBound_id).add (polyBound_const 6)) (fun x r j => ?_)
  · have hin : PolyFun (fun p : α × List α => (((false, p.1) : Bool × α), p.2)) :=
      ((polyFun_const false).pair polyFun_fst).pair polyFun_snd
    refine ((hin.comp hmain).comp polyFun_fst).of_eq (fun p => ?_)
    obtain ⟨x, l⟩ := p
    show (List.foldl (fun s a => ((s.1 || decide (s.2 = a) : Bool), s.2))
      ((false, x)) l).1 = _
    rw [memFold_eq]
    simp
  · obtain ⟨b, y⟩ := x
    rw [memFold_eq]
    have h1 : Enc.size ((((b || decide (y ∈ r.take j) : Bool)), y) : Bool × α)
        ≤ 2 * Enc.size ((b || decide (y ∈ r.take j) : Bool)) + 2 * Enc.size y :=
      Combine.size_pair_le _ _
    have h2 : Enc.size ((b || decide (y ∈ r.take j) : Bool)) ≤ 3 := Combine.size_bool_le _
    have h3 : Enc.size y ≤ Enc.size ((b, y) : Bool × α) := Combine.size_snd_le b y
    have h4 : Enc.size ((b, y) : Bool × α)
        ≤ Enc.size ((((b, y) : Bool × α), r) : (Bool × α) × List α) :=
      Combine.size_fst_le _ r
    dsimp only
    omega

/-! ## Filtering

`List.foldl (fun y a => if q a then a :: y else y) x l = (l.filter q).reverse ++ x`, and the
accumulator of that fold is no larger than the two inputs together, so no extra hypothesis is
needed. -/

theorem foldl_filter_cons_eq {α : Type*} (q : α → Bool) : ∀ (l : List α) (x : List α),
    List.foldl (fun y a => if q a then a :: y else y) x l = (l.filter q).reverse ++ x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      by_cases h : q a
      · rw [if_pos h, ih, List.filter_cons_of_pos h]
        simp
      · rw [if_neg h, ih, List.filter_cons_of_neg (by simpa using h)]

theorem size_foldl_filter_cons_le [Enc α] (q : α → Bool) : ∀ (l : List α) (x : List α),
    Enc.size (List.foldl (fun y a => if q a then a :: y else y) x l)
      ≤ Enc.size x + Enc.size l := by
  intro l
  induction l with
  | nil => intro x; rw [List.foldl_nil]; omega
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      have e1 : Enc.size (a :: x) = listSize (frame (Enc.encode a)) + Enc.size x - 1 :=
        size_cons_eq a x
      have e2 : Enc.size (a :: t) = listSize (frame (Enc.encode a)) + Enc.size t - 1 :=
        size_cons_eq a t
      have h2 := one_le_listSize_frame (Enc.encode a)
      have h3 := one_le_size x
      have h4 := one_le_size t
      by_cases h : q a
      · rw [if_pos h]
        have h5 := ih (a :: x)
        omega
      · rw [if_neg h]
        have h5 := ih x
        omega

/-- **Filtering a list is a `PolyFun`**, for a `PolyFun` predicate. -/
theorem PolyFun.filter [Enc α] {q : α → Bool} (hq : PolyFun q) :
    PolyFun (fun l : List α => l.filter q) := by
  have hf : PolyFun (fun z : List α × α => if q z.2 then z.2 :: z.1 else z.1) :=
    PolyFun.ite (polyFun_snd.comp hq) (polyFun_swap.comp polyFun_cons) polyFun_fst
  have hfold := PolyFun.foldl hf (p := fun n => 2 * n)
    ((polyBound_const 2).mul polyBound_id) (fun x r j => ?_)
  · have hin : PolyFun (fun l : List α => (([] : List α), l)) := polyFun_nil.pair polyFun_id
    refine ((hin.comp hfold).comp polyFun_reverse).of_eq (fun l => ?_)
    show (List.foldl (fun y a => if q a then a :: y else y) ([] : List α) l).reverse = _
    rw [foldl_filter_cons_eq]
    simp
  · have h1 := size_foldl_filter_cons_le q (r.take j) x
    have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h3 : Enc.size x ≤ Enc.size ((x, r) : List α × List α) := Combine.size_fst_le x r
    have h4 : Enc.size r ≤ Enc.size ((x, r) : List α × List α) := Combine.size_snd_le x r
    dsimp only
    omega

/-! ## Mapping

The accumulator of a map is a list of values of `g`, and its size is bounded through
`RAM.listSize_encList_le`: an array of `n` entries of size at most `S` has encoding size at most
`1 + n * (S + Nat.size S + 1)`.  Both `n` and `S` are polynomial in the size of the input, so no
hypothesis beyond `PolyFun g` is needed. -/

theorem foldl_map_cons_eq {α β : Type*} (g : α → β) : ∀ (l : List α) (x : List β),
    List.foldl (fun y a => g a :: y) x l = (l.map g).reverse ++ x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih => intro x; rw [List.foldl_cons, ih]; simp

theorem size_foldl_map_cons_le [Enc α] [Enc β] (g : α → β) : ∀ (l : List α) (x : List β),
    Enc.size (List.foldl (fun y a => g a :: y) x l) ≤ Enc.size x + Enc.size (l.map g) := by
  intro l
  induction l with
  | nil => intro x; rw [List.foldl_nil]; omega
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      have h := ih (g a :: x)
      have e1 : Enc.size (g a :: x) = listSize (frame (Enc.encode (g a))) + Enc.size x - 1 :=
        size_cons_eq _ _
      have e2 : Enc.size ((a :: t).map g)
          = listSize (frame (Enc.encode (g a))) + Enc.size (t.map g) - 1 := by
        rw [List.map_cons]
        exact size_cons_eq _ _
      have h2 := one_le_listSize_frame (Enc.encode (g a))
      have h3 := one_le_size x
      have h4 := one_le_size (t.map g)
      omega

/-- The size of the image of a list under a function with a polynomial size bound. -/
theorem size_map_le [Enc α] [Enc β] {g : α → β} {c d : ℕ}
    (hg : ∀ a : α, Enc.size (g a) ≤ c * (Enc.size a + 1) ^ d) (l : List α) :
    Enc.size (l.map g) ≤ 1 + Enc.size l * (2 * (c * (Enc.size l + 1) ^ d) + 1) := by
  have hentry : ∀ b ∈ l.map g, Enc.size b ≤ c * (Enc.size l + 1) ^ d := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    have h2 : Enc.size a ≤ Enc.size l := size_mem_le ha
    exact le_trans (hg a) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d))
  have hmain := listSize_encList_le (l.map g) (c * (Enc.size l + 1) ^ d) hentry
  have hsz : Enc.size (l.map g) = listSize (encList Enc.encode (l.map g)) := rfl
  have hlenm : (l.map g).length = l.length := List.length_map _
  have hll : l.length ≤ Enc.size l := by
    have h1 : l.length ≤ rawLength l := length_le_rawLength l
    have h2 : rawLength l < Enc.size l := rawLength_lt_size l
    omega
  have hss : Nat.size (c * (Enc.size l + 1) ^ d) ≤ c * (Enc.size l + 1) ^ d := size_le_self _
  have hstep : l.length * (c * (Enc.size l + 1) ^ d
        + Nat.size (c * (Enc.size l + 1) ^ d) + 1)
      ≤ Enc.size l * (2 * (c * (Enc.size l + 1) ^ d) + 1) :=
    Nat.mul_le_mul hll (by omega)
  rw [hlenm] at hmain
  omega

set_option maxHeartbeats 1000000 in
/-- **Mapping a `PolyFun` over a list is a `PolyFun`.** -/
theorem PolyFun.map [Enc α] [Enc β] {g : α → β} (hg : PolyFun g) :
    PolyFun (fun l : List α => l.map g) := by
  obtain ⟨c, d, hc⟩ := hg.size
  have hpb : PolyBound (fun n => n + (1 + n * (2 * (c * (n + 1) ^ d) + 1))) :=
    polyBound_id.add ((polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_witness c d)).add (polyBound_const 1))))
  have hf : PolyFun (fun z : List β × α => g z.2 :: z.1) :=
    ((polyFun_snd.comp hg).pair polyFun_fst).comp polyFun_cons
  have hfold := PolyFun.foldl hf
    (p := fun n => n + (1 + n * (2 * (c * (n + 1) ^ d) + 1))) hpb (fun x r j => ?_)
  · have hin : PolyFun (fun l : List α => (([] : List β), l)) := polyFun_nil.pair polyFun_id
    refine ((hin.comp hfold).comp polyFun_reverse).of_eq (fun l => ?_)
    show (List.foldl (fun y a => g a :: y) ([] : List β) l).reverse = _
    rw [foldl_map_cons_eq]
    simp
  · have h1 := size_foldl_map_cons_le g (r.take j) x
    have h2 := size_map_le hc (r.take j)
    have h3 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h4 : Enc.size x ≤ Enc.size ((x, r) : List β × List α) := Combine.size_fst_le x r
    have h5 : Enc.size r ≤ Enc.size ((x, r) : List β × List α) := Combine.size_snd_le x r
    have h6 : Enc.size (r.take j) * (2 * (c * (Enc.size (r.take j) + 1) ^ d) + 1)
        ≤ Enc.size ((x, r) : List β × List α)
          * (2 * (c * (Enc.size ((x, r) : List β × List α) + 1) ^ d) + 1) := by
      refine Nat.mul_le_mul (by omega) ?_
      have : (Enc.size (r.take j) + 1) ^ d
          ≤ (Enc.size ((x, r) : List β × List α) + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have := Nat.mul_le_mul_left c this
      omega
    dsimp only
    omega

end RAM
