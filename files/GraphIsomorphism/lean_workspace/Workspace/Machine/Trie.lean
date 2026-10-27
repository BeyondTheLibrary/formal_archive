import Workspace.Machine.Exact

/-!
# A trie in RAM memory

A set of strings over `[0, n)` is stored as a trie whose nodes are blocks of `2n + 1`
consecutive registers: the first register is a flag (`1` if the string of the node is in the
set), and the register `1 + 2x` holds the address of the child along the letter `x`, or `0`.
The nodes are allocated one after the other from the root, in fresh (zero) memory, so that
allocating a node costs nothing but moving the allocation pointer.  (The stride `2` for the
children makes the address of a child computable with additions only.)

This file is pure mathematics about memories: `RAM.Trie.Rep` is the representation invariant,
`RAM.Trie.walk` is what a lookup computes, `RAM.Trie.walk_eq` says that a lookup finds the node
of the string exactly when the string is a node, and `RAM.Trie.Rep.addChild`,
`RAM.Trie.Rep.setFlag` are the two writes an insertion performs.
-/

namespace RAM

namespace Trie

/-- The node width: a flag and `n` child pointers at stride `2`. -/
def width (n : ℕ) : ℕ := 2 * n + 1

/-- The address of node number `i`. -/
def addr (n root i : ℕ) : ℕ := root + width n * i

/-- **The representation invariant.**  `ps` lists the nodes (strings) in allocation order,
`S` the stored strings. -/
structure Rep (m : Mem) (n root : ℕ) (ps : List (List ℕ)) (S : List (List ℕ)) : Prop where
  nodup : ps.Nodup
  head : [] ∈ ps ∧ ps.idxOf [] = 0
  closed : ∀ p x, p ++ [x] ∈ ps → p ∈ ps
  lt : ∀ p ∈ ps, ∀ x ∈ p, x < n
  child : ∀ i (hi : i < ps.length), ∀ x < n,
    m (addr n root i + 1 + x + x) = if ps[i] ++ [x] ∈ ps then addr n root (ps.idxOf (ps[i] ++ [x]))
      else 0
  flag : ∀ i (hi : i < ps.length), m (addr n root i) = if ps[i] ∈ S then 1 else 0
  sub : ∀ t ∈ S, t ∈ ps

/-- The next free address. -/
def next (n root : ℕ) (ps : List (List ℕ)) : ℕ := addr n root ps.length

/-- One step of a lookup: from node `nd` along letter `x`; a missing node stays missing. -/
def stepW (m : Mem) (nd x : ℕ) : ℕ := if nd = 0 then 0 else m (nd + 1 + x + x)

/-- A lookup: follow the letters of `t` from the root. -/
def walk (m : Mem) (nd : ℕ) (t : List ℕ) : ℕ := t.foldl (stepW m) nd

theorem walk_append (m : Mem) (nd : ℕ) (t : List ℕ) (x : ℕ) :
    walk m nd (t ++ [x]) = stepW m (walk m nd t) x := by
  simp [walk, List.foldl_append]

theorem walk_zero (m : Mem) (t : List ℕ) : walk m 0 t = 0 := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t x ih => rw [walk_append, ih, stepW, if_pos rfl]

/-- Cells of different nodes, or different cells of one node, are different registers. -/
theorem addr_cell_inj {n root i i' j j' : ℕ} (hj : j < width n) (hj' : j' < width n)
    (h : addr n root i + j = addr n root i' + j') : i = i' ∧ j = j' := by
  unfold addr at h
  have h1 : width n * i + j = width n * i' + j' := by omega
  have hw : 0 < width n := by unfold width; omega
  have e1 : (width n * i + j) / width n = i := by
    rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
  have e2 : (width n * i' + j') / width n = i' := by
    rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hj', Nat.add_zero]
  have hi : i = i' := by rw [← e1, ← e2, h1]
  subst hi
  exact ⟨rfl, by omega⟩

theorem child_lt_width {n x : ℕ} (hx : x < n) : 1 + x + x < width n := by
  unfold width; omega

theorem idxOf_lt {ps : List (List ℕ)} {p : List ℕ} (h : p ∈ ps) : ps.idxOf p < ps.length :=
  List.idxOf_lt_length_iff.2 h

theorem getElem_idxOf {ps : List (List ℕ)} {p : List ℕ} (h : p ∈ ps) :
    ps[ps.idxOf p]'(idxOf_lt h) = p := List.getElem_idxOf (idxOf_lt h)

/-- **A lookup finds the node of `t` exactly when `t` is a node.** -/
theorem walk_eq {m : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) (hroot : 0 < root) (t : List ℕ) (ht : ∀ x ∈ t, x < n) :
    walk m root t = if t ∈ ps then addr n root (ps.idxOf t) else 0 := by
  induction t using List.reverseRecOn with
  | nil =>
    rw [if_pos h.head.1, h.head.2]; simp [walk, addr]
  | append_singleton t x ih =>
    have ht' : ∀ y ∈ t, y < n := fun y hy => ht y (by simp [hy])
    have hx : x < n := ht x (by simp)
    rw [walk_append, ih ht']
    by_cases hmem : t ∈ ps
    · rw [if_pos hmem, stepW, if_neg (by unfold addr; omega)]
      have := h.child (ps.idxOf t) (idxOf_lt hmem) x hx
      rw [getElem_idxOf hmem] at this
      rw [this]
    · rw [if_neg hmem, stepW, if_pos rfl, if_neg (fun h' => hmem (h.closed _ _ h'))]

theorem addr_pos {n root i : ℕ} (hroot : 0 < root) : addr n root i ≠ 0 := by
  unfold addr; omega

/-- **A query**: the flag at the end of the lookup is set exactly for the stored strings. -/
theorem query_iff {m : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) (hroot : 0 < root) (t : List ℕ) (ht : ∀ x ∈ t, x < n) :
    (walk m root t ≠ 0 ∧ m (walk m root t) = 1) ↔ t ∈ S := by
  rw [walk_eq h hroot t ht]
  by_cases hmem : t ∈ ps
  · rw [if_pos hmem]
    have := h.flag (ps.idxOf t) (idxOf_lt hmem)
    rw [getElem_idxOf hmem] at this
    rw [this]
    constructor
    · rintro ⟨-, h1⟩; by_contra hS; rw [if_neg hS] at h1; exact absurd h1 (by decide)
    · intro hS; exact ⟨addr_pos hroot, by rw [if_pos hS]⟩
  · rw [if_neg hmem]
    exact ⟨fun h' => absurd rfl h'.1, fun hS => absurd (h.sub t hS) hmem⟩

/-! ## The empty trie and the two writes of an insertion -/

/-- **A new root** in fresh memory is the empty trie. -/
theorem rep_new {m : Mem} {n root : ℕ} (hfresh : ∀ z, root ≤ z → m z = 0) :
    Rep m n root [[]] [] := by
  refine ⟨List.nodup_singleton _, ⟨by simp, by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro p x hp; simp at hp
  · intro p hp x hx; simp at hp; subst hp; simp at hx
  · intro i hi x hx
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp only [List.getElem_singleton, List.nil_append, List.mem_singleton, List.cons_ne_nil,
      if_false]
    exact hfresh _ (by unfold addr; omega)
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp only [List.getElem_singleton, List.not_mem_nil, if_false]
    exact hfresh _ (by unfold addr; omega)
  · intro t ht; simp at ht

/-- **Adding a child.**  At node `p`, the child along `x` is missing; the new node `p ++ [x]`
is allocated at the next free address (fresh memory), and the child pointer is set. -/
theorem Rep.addChild {m : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) (hfresh : ∀ z, next n root ps ≤ z → m z = 0)
    {p : List ℕ} (hp : p ∈ ps) {x : ℕ} (hx : x < n) (hnew : p ++ [x] ∉ ps) :
    Rep (m.update (addr n root (ps.idxOf p) + 1 + x + x) (next n root ps)) n root
      (ps ++ [p ++ [x]]) S ∧
    ∀ z, next n root (ps ++ [p ++ [x]]) ≤ z →
      (m.update (addr n root (ps.idxOf p) + 1 + x + x) (next n root ps)) z = 0 := by
  set c := addr n root (ps.idxOf p) + 1 + x + x with hc
  set ps' := ps ++ [p ++ [x]] with hps'
  have hip := idxOf_lt hp
  have hcell : c < next n root ps := by
    have := child_lt_width (n := n) hx
    unfold next addr at *
    have : width n * ps.idxOf p + width n ≤ width n * ps.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hip
    omega
  have hidx_old : ∀ q ∈ ps, ps'.idxOf q = ps.idxOf q := fun q hq => by
    rw [hps', List.idxOf_append_of_mem hq]
  have hidx_new : ps'.idxOf (p ++ [x]) = ps.length := by
    rw [hps', List.idxOf_append_of_notMem hnew]; simp
  have hlen : ps'.length = ps.length + 1 := by simp [hps']
  -- cells of old node `i` other than `c` are unchanged
  have hold : ∀ i < ps.length, ∀ j < width n, (i, j) ≠ (ps.idxOf p, 1 + x + x) →
      (m.update c (next n root ps)) (addr n root i + j) = m (addr n root i + j) := by
    intro i hi j hj hne
    rw [Mem.update_of_ne]
    intro heq
    have := addr_cell_inj (n := n) (root := root) hj (child_lt_width hx)
      (by rw [heq, hc]; ring)
    exact hne (by rw [this.1, this.2])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hps', ← List.concat_eq_append]
    exact List.Nodup.concat hnew h.nodup
  · exact ⟨List.mem_append_left _ h.head.1, by rw [hidx_old _ h.head.1, h.head.2]⟩
  · intro q y hq
    rw [hps', List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · exact List.mem_append_left _ (h.closed q y hq)
    · have := List.append_inj' hq rfl
      rw [this.1]; exact List.mem_append_left _ hp
  · intro q hq y hy
    rw [hps', List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact h.lt q hq y hy
    · rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact h.lt p hp y hy
      · exact hx
  · intro i hi y hy
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · -- an old node
      have hgi : ps'[i]'(by omega) = ps[i] := List.getElem_append_left hi
      rw [hgi]
      by_cases hcase : i = ps.idxOf p ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcase
        rw [← hc, Mem.update_self]
        have : ps[ps.idxOf p] = p := getElem_idxOf hp
        rw [this, if_pos (by simp [hps']), hidx_new]
        rfl
      · rw [show addr n root i + 1 + y + y = addr n root i + (1 + y + y) by ring,
          hold i hi _ (child_lt_width hy) (by
          intro heq; simp only [Prod.mk.injEq] at heq
          exact hcase ⟨heq.1, by omega⟩)]
        rw [← show addr n root i + 1 + y + y = addr n root i + (1 + y + y) by ring,
          h.child i hi y hy]
        have hmem' : ps[i] ++ [y] ∈ ps' ↔ ps[i] ++ [y] ∈ ps := by
          rw [hps', List.mem_append, List.mem_singleton]
          constructor
          · rintro (h1 | h1)
            · exact h1
            · exfalso
              have := List.append_inj' h1 rfl
              have hy' : y = x := by simpa using this.2
              have hi' : i = ps.idxOf p := by
                rw [← this.1]
                exact (List.Nodup.idxOf_getElem h.nodup i hi).symm
              exact hcase ⟨hi', hy'⟩
          · exact Or.inl
        by_cases hm : ps[i] ++ [y] ∈ ps
        · rw [if_pos hm, if_pos (hmem'.2 hm), hidx_old _ hm]
        · rw [if_neg hm, if_neg (fun h' => hm (hmem'.1 h'))]
    · -- the new node: fresh memory, no children
      have hgi : ps'[ps.length]'(by omega) = p ++ [x] := by simp [hps']
      have hne : addr n root ps.length + 1 + y + y ≠ c := by unfold next addr at *; omega
      rw [hgi, Mem.update_of_ne m _ hne]
      rw [hfresh _ (by unfold next addr; omega)]
      rw [if_neg]
      intro hm
      rw [hps', List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hnew (h.closed _ _ hm)
      · have := congrArg List.length hm; simp at this
  · intro i hi
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have hgi : ps'[i]'(by omega) = ps[i] := List.getElem_append_left hi
      rw [hgi]
      have := hold i hi 0 (by unfold width; omega) (by
        intro heq; simp only [Prod.mk.injEq] at heq; omega)
      simp only [Nat.add_zero] at this
      rw [this, h.flag i hi]
    · have hgi : ps'[ps.length]'(by omega) = p ++ [x] := by simp [hps']
      have hne : addr n root ps.length ≠ c := by unfold next addr at *; omega
      rw [hgi, Mem.update_of_ne m _ hne]
      rw [hfresh _ (by unfold next addr; omega), if_neg]
      intro hS; exact hnew (h.sub _ hS)
  · intro t ht; exact List.mem_append_left _ (h.sub t ht)
  · intro z hz
    have hz' : z ≠ c := by
      unfold next at *; unfold addr at *; rw [hlen] at hz
      have : width n * ps.length ≤ width n * (ps.length + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [Mem.update_of_ne m _ hz']
    apply hfresh
    unfold next addr at *
    rw [hlen] at hz
    have : width n * ps.length ≤ width n * (ps.length + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- **Setting a flag**: storing the string `t`, which is already a node. -/
theorem Rep.setFlag {m : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) {t : List ℕ} (ht : t ∈ ps) :
    Rep (m.update (addr n root (ps.idxOf t)) 1) n root ps (t :: S) := by
  have hit := idxOf_lt ht
  refine ⟨h.nodup, h.head, h.closed, h.lt, ?_, ?_, ?_⟩
  · intro i hi x hx
    have hne : addr n root i + 1 + x + x ≠ addr n root (ps.idxOf t) := by
      intro heq
      have := addr_cell_inj (n := n) (root := root) (child_lt_width hx) (by unfold width; omega)
        (by rw [← heq]; ring : addr n root i + (1 + x + x) = addr n root (ps.idxOf t) + 0)
      omega
    rw [Mem.update_of_ne m _ hne, h.child i hi x hx]
  · intro i hi
    by_cases hi' : i = ps.idxOf t
    · subst hi'
      rw [Mem.update_self, getElem_idxOf ht, if_pos (List.mem_cons_self)]
    · have hne' : addr n root i ≠ addr n root (ps.idxOf t) := by
        intro heq
        have := addr_cell_inj (n := n) (root := root) (j := 0) (j' := 0)
          (by unfold width; omega) (by unfold width; omega) (by simpa using heq)
        exact hi' this.1
      rw [Mem.update_of_ne m _ hne', h.flag i hi]
      have hne : ps[i] ≠ t := by
        intro heq; apply hi'; rw [← heq]; exact (List.Nodup.idxOf_getElem h.nodup i hi).symm
      simp [List.mem_cons, hne]
  · intro s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ht
    · exact h.sub s hs

/-- The trie is unchanged by writes outside its nodes. -/
theorem Rep.update_out {m : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) {a v : ℕ} (ha : a < root ∨ next n root ps ≤ a) :
    Rep (m.update a v) n root ps S := by
  have hne : ∀ i < ps.length, ∀ j < width n, addr n root i + j ≠ a := by
    intro i hi j hj heq
    unfold next addr at ha
    rw [← heq] at ha
    unfold addr at ha
    have : width n * i + width n ≤ width n * ps.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    omega
  refine ⟨h.nodup, h.head, h.closed, h.lt, fun i hi x hx => ?_, fun i hi => ?_, h.sub⟩
  · have h1 : addr n root i + 1 + x + x ≠ a := by
      have := hne i hi (1 + x + x) (child_lt_width hx)
      rw [show addr n root i + 1 + x + x = addr n root i + (1 + x + x) by ring]; exact this
    rw [Mem.update_of_ne m _ h1]
    exact h.child i hi x hx
  · have h1 : addr n root i ≠ a := by simpa using hne i hi 0 (by unfold width; omega)
    rw [Mem.update_of_ne m _ h1]
    exact h.flag i hi

/-- A lookup reads only the cells of the nodes. -/
theorem Rep.congr {m m' : Mem} {n root : ℕ} {ps : List (List ℕ)} {S : List (List ℕ)}
    (h : Rep m n root ps S) (he : ∀ z, root ≤ z → z < next n root ps → m' z = m z) :
    Rep m' n root ps S := by
  have hin : ∀ i < ps.length, ∀ j < width n, root ≤ addr n root i + j ∧
      addr n root i + j < next n root ps := by
    intro i hi j hj
    unfold next addr
    have : width n * i + width n ≤ width n * ps.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    omega
  refine ⟨h.nodup, h.head, h.closed, h.lt, fun i hi x hx => ?_, fun i hi => ?_, h.sub⟩
  · have := hin i hi (1 + x + x) (child_lt_width hx)
    rw [show addr n root i + 1 + x + x = addr n root i + (1 + x + x) by ring,
      he _ this.1 this.2, ← show addr n root i + 1 + x + x = addr n root i + (1 + x + x) by ring]
    exact h.child i hi x hx
  · have := hin i hi 0 (by unfold width; omega)
    simp only [Nat.add_zero] at this
    rw [he _ this.1 this.2]
    exact h.flag i hi

end Trie

end RAM
