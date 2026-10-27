/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  One refinement round on the
RAM: the new colors `c'(x) = (st(c)(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ [N])` as strings in memory.
-/
import Workspace.Algo.TagLinSort2

/-!
# The rows of one refinement round

Given the ranks `rk x = st(c)(x)` of the vertices (an array at register `40`), the number `N`
of colors (register `41`) and the list of edges (at register `42`, `m` edges in register
`43`), `rowsProg` writes, for each vertex `x`, the string

  `rk x, d⁺₀(x), d⁻₀(x), …, d⁺_{N-1}(x), d⁻_{N-1}(x)`

(`rowStr`) in the string format of the sort (`StrAt`), and the array of their addresses.  It
first writes every row with zero counts (`rowsInit`, `O(nN)` steps), then walks the edges once
and increments two counters per edge (`edgesProg`, `O(m)` steps).

Rows have the fixed width `W = 4N + 3`; row `x` starts at `fr + n + x W`, where `fr` is the
free address (register `14`), and the address array is at `fr`.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact

/-! ## The strings -/

/-- `d⁺ᵢ(x)` counted on a list of edges: the edges `(x, y)` with `rk y = i`. -/
def outC (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (i x : ℕ) : ℕ :=
  es.countP (fun e => e.1 = x ∧ rk e.2 = i)

/-- `d⁻ᵢ(x)` counted on a list of edges: the edges `(y, x)` with `rk y = i`. -/
def inC (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (i x : ℕ) : ℕ :=
  es.countP (fun e => e.2 = x ∧ rk e.1 = i)

/-- The new color of `x`, as a string. -/
def rowStr (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (N x : ℕ) : List ℕ :=
  rk x :: (List.range N).flatMap (fun i => [outC es rk i x, inC es rk i x])

/-- Row width. -/
def rowW (N : ℕ) : ℕ := 4 * N + 3

/-- A row with zero counts: `[4N+2, 1, r, 1, 0, 1, 0, …]`. -/
def RowAt (m : Mem) (p N r : ℕ) (fo fi : ℕ → ℕ) : Prop :=
  m p = 4 * N + 2 ∧ m (p + 1) = 1 ∧ m (p + 2) = r ∧
    ∀ i < N, m (p + 3 + 4 * i) = 1 ∧ m (p + 4 + 4 * i) = fo i ∧ m (p + 5 + 4 * i) = 1 ∧
      m (p + 6 + 4 * i) = fi i

theorem cell_inj {x y c c' W : ℕ} (hc : c < W) (hc' : c' < W) (h : x * W + c = y * W + c') :
    x = y ∧ c = c' := by
  rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
  · have : (x + 1) * W ≤ y * W := Nat.mul_le_mul_right _ hxy
    rw [Nat.succ_mul] at this; omega
  · omega
  · have : (y + 1) * W ≤ x * W := Nat.mul_le_mul_right _ hxy
    rw [Nat.succ_mul] at this; omega

theorem length_rowStr (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (N x : ℕ) :
    (rowStr es rk N x).length = 2 * N + 1 := by
  unfold rowStr
  rw [List.length_cons, List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

theorem getElem_flatMap_pair (N : ℕ) (f g : ℕ → ℕ) (i : ℕ) (hi : i < N) :
    ((List.range N).flatMap (fun i => [f i, g i]))[2 * i]'(by
      rw [List.length_flatMap]; simp; omega) = f i ∧
    ((List.range N).flatMap (fun i => [f i, g i]))[2 * i + 1]'(by
      rw [List.length_flatMap]; simp; omega) = g i := by
  induction N with
  | zero => omega
  | succ N ih =>
    have hl : ((List.range N).flatMap (fun i => [f i, g i])).length = 2 * N := by
      rw [List.length_flatMap]; simp; ring
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [List.getElem_append_left (by rw [hl] <;> omega),
        List.getElem_append_left (by rw [hl] <;> omega)]
      exact ih hi
    · rw [List.getElem_append_right (by rw [hl] <;> omega),
        List.getElem_append_right (by rw [hl] <;> omega)]
      simp [hl]

/-- A row with the final counts is the string `rowStr`. -/
theorem strAt_of_rowAt {m : Mem} {p N : ℕ} {es : List (ℕ × ℕ)} {rk : ℕ → ℕ} {x : ℕ}
    (h : RowAt m p N (rk x) (fun i => outC es rk i x) (fun i => inC es rk i x)) :
    StrAt m p (rowStr es rk N x) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨by rw [h0, length_rowStr]; ring, fun j hj => ?_⟩
  rw [length_rowStr] at hj
  rcases j with _ | j
  · exact ⟨by simpa using h1, by simpa [rowStr] using h2⟩
  · have hj' : j < 2 * N := by omega
    obtain ⟨i, hi⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
    have hiN : i < N := by omega
    obtain ⟨g1, g2, g3, g4⟩ := h3 i hiN
    have hp := getElem_flatMap_pair N (fun i => outC es rk i x) (fun i => inC es rk i x) i hiN
    rcases hi with rfl | rfl
    · refine ⟨by rw [show p + 1 + 2 * (2 * i + 1) = p + 3 + 4 * i by ring]; exact g1, ?_⟩
      rw [show p + 2 + 2 * (2 * i + 1) = p + 4 + 4 * i by ring, g2]
      simp only [rowStr, List.getElem_cons_succ]
      exact hp.1.symm
    · refine ⟨by rw [show p + 1 + 2 * (2 * i + 1 + 1) = p + 5 + 4 * i by ring]; exact g3, ?_⟩
      rw [show p + 2 + 2 * (2 * i + 1 + 1) = p + 6 + 4 * i by ring, g4]
      simp only [rowStr, List.getElem_cons_succ]
      exact hp.2.symm

/-! ## The programs -/

/-- Fill the pairs `1, 0` of one row (register `3` points before the next pair, `5` counts). -/
def pairLoop : Program :=
  whileNz 5 (seq (addTo 3 3 1) (seq (storeTo 3 1) (seq (addTo 3 3 1) (seq (assign 6 0)
    (seq (storeTo 3 6) (subTo 5 5 1))))))

/-- One row with zero counts. -/
def rowBody : Program :=
  seq (addTo 2 20 48) (seq (storeTo 2 44) (seq (storeTo 44 46) (seq (addTo 3 44 1)
    (seq (storeTo 3 1) (seq (addTo 3 3 1) (seq (addTo 4 40 48) (seq (loadTo 4 4)
    (seq (storeTo 3 4) (seq (copyTo 5 45) (seq pairLoop (seq (addTo 44 44 47)
    (seq (addTo 48 48 1) (subTo 29 29 1)))))))))))))

/-- All rows with zero counts. -/
def rowsInit : Program :=
  seq (copyTo 20 14) (seq (addTo 44 14 21) (seq (addTo 45 41 41) (seq (addTo 46 45 45)
    (seq (addTo 46 46 1) (seq (addTo 46 46 1) (seq (addTo 47 46 1) (seq (assign 48 0)
    (seq (copyTo 29 21) (seq (whileNz 29 rowBody) (copyTo 14 44))))))))))

/-- One edge `(a, b)`: increment `d⁺_{rk b}(a)` and `d⁻_{rk a}(b)`. -/
def edgeBody : Program :=
  seq (loadTo 2 49) (seq (addTo 3 49 1) (seq (addTo 3 3 1) (seq (loadTo 3 3)
  (seq (addTo 4 40 3) (seq (loadTo 4 4) (seq (addTo 4 4 4) (seq (addTo 4 4 4)
  (seq (addTo 5 20 2) (seq (loadTo 5 5) (seq (addTo 5 5 4) (seq (addTo 5 5 1) (seq (addTo 5 5 1)
  (seq (addTo 5 5 1) (seq (addTo 5 5 1)
  (seq (loadTo 6 5) (seq (addTo 6 6 1) (seq (storeTo 5 6)
  (seq (addTo 4 40 2) (seq (loadTo 4 4) (seq (addTo 4 4 4) (seq (addTo 4 4 4)
  (seq (addTo 5 20 3) (seq (loadTo 5 5) (seq (addTo 5 5 4) (seq (addTo 5 5 1) (seq (addTo 5 5 1)
  (seq (addTo 5 5 1) (seq (addTo 5 5 1) (seq (addTo 5 5 1) (seq (addTo 5 5 1)
  (seq (loadTo 6 5) (seq (addTo 6 6 1) (seq (storeTo 5 6)
  (seq (addTo 49 49 1) (seq (addTo 49 49 1) (seq (addTo 49 49 1) (seq (addTo 49 49 1)
  (seq (addTo 49 49 1) (subTo 29 29 1)))))))))))))))))))))))))))))))))))))))

/-- All edges. -/
def edgesProg : Program :=
  seq (addTo 49 42 1) (seq (addTo 49 49 1) (seq (copyTo 29 43) (whileNz 29 edgeBody)))

/-- **One refinement round**: the rows, then the counts. -/
def rowsProg : Program := seq rowsInit edgesProg

/-- The registers the round writes. -/
notation "Wrows" => [2, 3, 4, 5, 6, 14, 20, 29, 44, 45, 46, 47, 48, 49]

/-! ## The pairs of one row -/

theorem wf_pairBody : Wf (seq (addTo 3 3 1) (seq (storeTo 3 1) (seq (addTo 3 3 1) (seq (assign 6 0)
    (seq (storeTo 3 6) (subTo 5 5 1)))))) := by wf_tac

theorem wf_pairLoop : Wf pairLoop := by unfold pairLoop; wf_tac

theorem runsTo_pairLoop {M : Mem} {p N : ℕ} (h1 : M 1 = 1) (h3 : M 3 = p + 2) (h5 : M 5 = 2 * N)
    (hp : 64 ≤ p) :
    ∃ t, RunsTo pairLoop (fun m => m = M) (fun m => Keep [3, 5, 6] (p + 3) (p + 3 + 4 * N) M m ∧
      (∀ i < 2 * N, m (p + 3 + 2 * i) = 1 ∧ m (p + 4 + 2 * i) = 0) ∧ t ≤ 16 * N + 1) t := by
  have key := runsTo_whileNz_amortX (i := 5) wf_pairBody
    (fun m => ∃ k ≤ 2 * N, m 5 + k = 2 * N ∧ m 3 = p + 2 + 2 * k ∧
      Keep [3, 5, 6] (p + 3) (p + 3 + 4 * N) M m ∧
      ∀ i < k, m (p + 3 + 2 * i) = 1 ∧ m (p + 4 + 2 * i) = 0) (fun m => 8 * m 5) ?_ M
    ⟨0, by omega, by omega, by omega, Keep.refl _ _ _ _, fun i hi => by omega⟩
  · obtain ⟨t, ht⟩ := key
    refine ⟨t, ht.weaken (fun m ⟨⟨k, hk, h5', h3', hkeep, hc⟩, h0, hpot⟩ => ?_)⟩
    have : k = 2 * N := by omega
    subst this
    exact ⟨hkeep, hc, by simp only [h5] at hpot; omega⟩
  intro m ⟨k, hk, h5', h3', hkeep, hc⟩ hne
  have e1 : m 1 = 1 := by rw [hkeep 1 (by simp) (by omega), h1]
  refine ⟨6, ?_⟩
  rt
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, h3']
  refine ⟨⟨k + 1, by omega, by omega, by omega, ?_, fun i hi => ?_⟩, by omega⟩
  · refine (((((hkeep.upd (Or.inl (by simp)) _).upd (Or.inr ⟨by omega, by omega⟩) _).upd
      (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd (Or.inr ⟨by omega, by omega⟩) _).upd
      (Or.inl (by simp)) _
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simp (disch := omega) only [Mem.update_of_ne]
      exact hc i hi
    · rw [show p + 2 + 2 * i + 1 + 1 = p + 4 + 2 * i by ring,
        show p + 2 + 2 * i + 1 = p + 3 + 2 * i by ring]
      constructor
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]

theorem runsTo_pairLoop' {M : Mem} {p N : ℕ} (h1 : M 1 = 1) (h3 : M 3 = p + 2)
    (h5 : M 5 = 2 * N) (hp : 64 ≤ p) :
    RunsTo pairLoop (fun m => m = M) (fun m => Keep [3, 5, 6] (p + 3) (p + 3 + 4 * N) M m ∧
      (∀ i < 2 * N, m (p + 3 + 2 * i) = 1 ∧ m (p + 4 + 2 * i) = 0)) (16 * N + 1) := by
  obtain ⟨t, ht⟩ := runsTo_pairLoop h1 h3 h5 hp
  obtain ⟨M', ⟨hk, hc, hle⟩, hrun⟩ := ht.exact
  exact (hrun.mono hle).weaken (fun m hm => by subst hm; exact ⟨hk, hc⟩)

/-! ## The rows with zero counts -/

theorem wf_rowBody : Wf rowBody := by unfold rowBody pairLoop; wf_tac

theorem rowAt_zero {m : Mem} {p N r : ℕ} (h0 : m p = 4 * N + 2) (h1 : m (p + 1) = 1)
    (h2 : m (p + 2) = r) (hc : ∀ i < 2 * N, m (p + 3 + 2 * i) = 1 ∧ m (p + 4 + 2 * i) = 0) :
    RowAt m p N r (fun _ => 0) (fun _ => 0) := by
  refine ⟨h0, h1, h2, fun i hi => ?_⟩
  have a := hc (2 * i) (by omega)
  have b := hc (2 * i + 1) (by omega)
  rw [show p + 3 + 2 * (2 * i) = p + 3 + 4 * i by ring,
    show p + 4 + 2 * (2 * i) = p + 4 + 4 * i by ring] at a
  rw [show p + 3 + 2 * (2 * i + 1) = p + 5 + 4 * i by ring,
    show p + 4 + 2 * (2 * i + 1) = p + 6 + 4 * i by ring] at b
  exact ⟨a.1, a.2, b.1, b.2⟩

theorem RowAt.congr {m m' : Mem} {p N r : ℕ} {fo fi : ℕ → ℕ} (h : RowAt m p N r fo fi)
    (hm : ∀ z, p ≤ z → z < p + rowW N → m' z = m z) : RowAt m' p N r fo fi := by
  unfold rowW at hm
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨by rw [hm _ le_rfl (by omega), h0], by rw [hm _ (by omega) (by omega), h1],
    by rw [hm _ (by omega) (by omega), h2], fun i hi => ?_⟩
  obtain ⟨a, b, c, d⟩ := h3 i hi
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hm _ (by omega) (by omega)] <;> assumption

set_option maxHeartbeats 0 in
/-- **All rows with zero counts**, in `16 N n + 16 n + 11` steps. -/
theorem runsTo_rowsInit {M : Mem} {n N R fr : ℕ} {rk : ℕ → ℕ} (h1 : M 1 = 1) (h14 : M 14 = fr)
    (h21 : M 21 = n) (h40 : M 40 = R) (h41 : M 41 = N) (hR : ∀ x < n, M (R + x) = rk x)
    (hR64 : 64 ≤ R) (hRf : R + n ≤ fr) :
    RunsTo rowsInit (fun m => m = M) (fun m => Keep Wrows fr (fr + n + n * rowW N) M m ∧
      m 14 = fr + n + n * rowW N ∧ m 20 = fr ∧
      ∀ x < n, m (fr + x) = fr + n + x * rowW N ∧
        RowAt m (fr + n + x * rowW N) N (rk x) (fun _ => 0) (fun _ => 0))
      (16 * N * n + 16 * n + 11) := by
  have hf : 64 ≤ fr := by omega
  set W := rowW N with hW
  have hW' : W = 4 * N + 3 := rfl
  set rb := fr + n with hrb
  set M1 := ((((((((M.update 20 fr).update 44 rb).update 45 (N + N)).update 46 (N + N + (N + N))).update
    46 (N + N + (N + N) + 1)).update 46 (N + N + (N + N) + 1 + 1)).update 47
    (N + N + (N + N) + 1 + 1 + 1)).update 48 0).update 29 n with hM1
  have hpre : RunsTo (seq (copyTo 20 14) (seq (addTo 44 14 21) (seq (addTo 45 41 41)
      (seq (addTo 46 45 45) (seq (addTo 46 46 1) (seq (addTo 46 46 1) (seq (addTo 47 46 1)
      (seq (assign 48 0) (copyTo 29 21))))))))) (fun m => m = M) (fun m => m = M1) 9 := by
    rt
    rw [hM1, hrb]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h14, h21, h41]
  have ho1 : Outside [20, 44, 45, 46, 47, 48, 29] M M1 := by
    rw [hM1]; outside_tac (Outside.refl [20, 44, 45, 46, 47, 48, 29] M)
  have g : ∀ z, z ∉ [20, 44, 45, 46, 47, 48, 29] → M1 z = M z := ho1
  have e45 : M1 45 = 2 * N := by
    rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
  have e46 : M1 46 = 4 * N + 2 := by
    rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
  have e47 : M1 47 = W := by
    rw [hM1, hW']; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
  clear_value M1
  have key := runsTo_whileNz_amortX (i := 29) wf_rowBody
    (fun m => ∃ x ≤ n, m 48 = x ∧ m 29 + x = n ∧ m 44 = rb + x * W ∧ m 20 = fr ∧
      m 45 = 2 * N ∧ m 46 = 4 * N + 2 ∧ m 47 = W ∧ Keep Wrows fr (rb + x * W) M m ∧
      ∀ y < x, m (fr + y) = rb + y * W ∧ RowAt m (rb + y * W) N (rk y) (fun _ => 0) (fun _ => 0))
    (fun m => (16 * N + 16) * m 29) ?_ M1
    ⟨0, by omega, by rw [hM1]; try rfl, by rw [hM1]; try rfl, by
      rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega, by
      rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne], e45, e46, e47,
      Keep.of_outside (ho1.mono (by intro z hz; simp at hz ⊢; omega)), fun y hy => by omega⟩
  · obtain ⟨t, ht⟩ := key
    obtain ⟨M2, ⟨⟨x, hx, h48, h29, h44, h20, -, -, -, hkeep, hrows⟩, h0, hpot⟩, hrun⟩ := ht.exact
    have hxn : x = n := by omega
    subst hxn
    have ht' : t ≤ (16 * N + 16) * x + 1 := by
      simp only at hpot
      have : M1 29 = x := by rw [hM1]; simp
      rw [this] at hpot; omega
    unfold rowsInit
    refine ((hpre.seq (hrun.seq (T' := 1) (copy_last' (T := 0) rfl))).mono ?_).weaken ?_
    · have : (16 * N + 16) * x = 16 * N * x + 16 * x := by ring
      omega
    · intro m hm
      subst hm
      refine ⟨(hkeep.upd (Or.inl (by simp)) _), by rw [Mem.update_self, h44], by
        rw [Mem.update_of_ne _ _ (by decide), h20], fun y hy => ?_⟩
      obtain ⟨a, b⟩ := hrows y hy
      refine ⟨by rw [Mem.update_of_ne _ _ (by omega), a], b.congr (fun z hz _ => ?_)⟩
      rw [Mem.update_of_ne _ _ (by omega)]
  intro m ⟨x, hx, h48, h29, h44, h20, h45, h46, h47, hkeep, hrows⟩ hne
  have hxn : x < n := by omega
  have e1 : m 1 = 1 := by rw [hkeep 1 (by simp) (by omega), h1]
  have e40 : m 40 = R := by rw [hkeep 40 (by simp) (by omega), h40]
  have eR : m (R + x) = rk x := by rw [hkeep _ (by simp; omega) (by omega), hR x hxn]
  set p := rb + x * W with hp
  have hWx : (x + 1) * W = x * W + W := by ring
  have hyW : ∀ y < x, rb + y * W + W ≤ p := fun y hy => by
    have : (y + 1) * W ≤ x * W := Nat.mul_le_mul_right _ hy
    rw [Nat.succ_mul] at this; omega
  refine ⟨16 * N + 1 + 3 + 10, ?_⟩
  unfold rowBody
  rt
  refine ExplLinear.at_mem (fun M' => M' 1 = 1 ∧ M' 3 = p + 2 ∧ M' 5 = 2 * N ∧ M' 44 = p ∧ M' 48 = x ∧
      M' 29 = m 29 ∧ M' 20 = fr ∧ M' 45 = 2 * N ∧ M' 46 = 4 * N + 2 ∧ M' 47 = W ∧
      M' (fr + x) = p ∧ M' p = 4 * N + 2 ∧ M' (p + 1) = 1 ∧ M' (p + 2) = rk x ∧
      Outside [2, 3, 4, 5, fr + x, p, p + 1, p + 2] m M')
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e40, eR,
    h20, h44, h45, h46, h47, h48]; done)
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e40, eR, h20, h44, h45,
      h46, h47, h48]
  obtain ⟨f1, f3, f5, f44, f48, f29, f20, f45, f46, f47, fS, f0, f1', f2', ho⟩ := hM'
  refine block_seq (T' := 3) (runsTo_pairLoop' f1 f3 f5 (by omega)) (fun M2 ⟨hk2, hc2⟩ => ?_)
  have g : ∀ z, z ≠ 3 → z ≠ 5 → z ≠ 6 → (z < p + 3 ∨ p + 3 + 4 * N ≤ z) → M2 z = M' z :=
    fun z a b c d => hk2 z (by simp; omega) d
  have g1 : M2 1 = 1 := by rw [g 1 (by omega) (by omega) (by omega) (by omega), f1]
  rt
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g1,
    g 44 (by omega) (by omega) (by omega) (by omega), g 47 (by omega) (by omega) (by omega)
    (by omega), g 48 (by omega) (by omega) (by omega) (by omega),
    g 29 (by omega) (by omega) (by omega) (by omega), f44, f47, f48, f29]
  have hK : (16 * N + 16) * (m 29 - 1) + (16 * N + 16) = (16 * N + 16) * m 29 := by
    rw [← Nat.mul_succ]; congr 1; omega
  refine ⟨⟨x + 1, by omega, rfl, by omega, by rw [hWx]; omega,
    by rw [g 20 (by omega) (by omega) (by omega) (by omega), f20],
    by rw [g 45 (by omega) (by omega) (by omega) (by omega), f45],
    by rw [g 46 (by omega) (by omega) (by omega) (by omega), f46], trivial, ?_, fun y hy => ?_⟩,
    by omega⟩
  · intro z hz hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hWx] at hr
    simp (disch := omega) only [Mem.update_of_ne]
    rw [g z (by omega) (by omega) (by omega) (by omega), ho z (by simp; omega)]
    exact hkeep z (by simp; omega) (by omega)
  · have gf : ∀ z, 64 ≤ z → ((((M2.update 44 (p + W)).update 48 (x + 1)).update 29 (m 29 - 1)) z
        = M2 z) := fun z hz => by simp (disch := omega) only [Mem.update_of_ne]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
    · have hyW' := hyW y hy
      obtain ⟨a, b⟩ := hrows y hy
      have hyx : y * W ≤ x * W := Nat.mul_le_mul_right _ hy.le
      refine ⟨?_, b.congr (fun z hz1 hz2 => ?_)⟩
      · rw [g _ (by omega) (by omega) (by omega) (by omega), ho _ (by simp; omega), a]
      · unfold rowW at hz2
        rw [gf z (by omega), g z (by omega) (by omega) (by omega) (by omega),
          ho z (by simp; omega)]
    · refine ⟨by rw [g _ (by omega) (by omega) (by omega) (by omega), fS], ?_⟩
      refine rowAt_zero ?_ ?_ ?_ (fun i hi => ?_)
      · rw [gf _ (by omega), g _ (by omega) (by omega) (by omega) (by omega), f0]
      · rw [gf _ (by omega), g _ (by omega) (by omega) (by omega) (by omega), f1']
      · rw [gf _ (by omega), g _ (by omega) (by omega) (by omega) (by omega), f2']
      · rw [gf _ (by omega), gf _ (by omega)]
        exact hc2 i hi

/-! ## The counts -/

theorem rowW_pos (N : ℕ) : 3 ≤ rowW N := by unfold rowW; omega

/-- Two cells of rows are equal only in the same row at the same offset. -/
theorem row_cell_eq {rb W x a c c' : ℕ} (hc : c < W) (hc' : c' < W) :
    rb + x * W + c = rb + a * W + c' ↔ x = a ∧ c = c' := by
  constructor
  · intro h; exact cell_inj hc hc' (by omega)
  · rintro ⟨rfl, rfl⟩; rfl

/-- One edge adds `1` to one out-count and one in-count. -/
theorem rowAt_bump {m : Mem} {rb N x a b i1 i2 r : ℕ} {fo fi : ℕ → ℕ}
    (h : RowAt m (rb + x * rowW N) N r fo fi) (hi1 : i1 < N) (hi2 : i2 < N) :
    let q1 := rb + a * rowW N + (4 + 4 * i1)
    let q2 := rb + b * rowW N + (6 + 4 * i2)
    let m1 := m.update q1 (m q1 + 1)
    RowAt (m1.update q2 (m1 q2 + 1)) (rb + x * rowW N) N r
      (fun i => fo i + if x = a ∧ i = i1 then 1 else 0)
      (fun i => fi i + if x = b ∧ i = i2 then 1 else 0) := by
  intro q1 q2 m1
  have hW : rowW N = 4 * N + 3 := rfl
  have hq12 : q2 ≠ q1 := by
    intro h
    have := (row_cell_eq (rb := rb) (W := rowW N) (x := b) (a := a) (c := 6 + 4 * i2)
      (c' := 4 + 4 * i1) (by omega) (by omega)).1 h
    omega
  have e1 : m1 q2 = m q2 := Mem.update_of_ne _ _ hq12
  -- reading a cell of row `x`
  have rd : ∀ c, c < rowW N → (m1.update q2 (m1 q2 + 1)) (rb + x * rowW N + c) =
      m (rb + x * rowW N + c) + (if x = a ∧ c = 4 + 4 * i1 then 1 else 0) +
        (if x = b ∧ c = 6 + 4 * i2 then 1 else 0) := by
    intro c hc
    have k1 := row_cell_eq (rb := rb) (x := x) (a := a) (c := c) (c' := 4 + 4 * i1) hc
      (by omega : 4 + 4 * i1 < rowW N)
    have k2 := row_cell_eq (rb := rb) (x := x) (a := b) (c := c) (c' := 6 + 4 * i2) hc
      (by omega : 6 + 4 * i2 < rowW N)
    by_cases h2 : x = b ∧ c = 6 + 4 * i2
    · have hq : rb + x * rowW N + c = q2 := k2.2 h2
      have h1 : ¬ (x = a ∧ c = 4 + 4 * i1) := by omega
      rw [hq, Mem.update_self, e1, if_neg h1, if_pos h2]
    · have hq : rb + x * rowW N + c ≠ q2 := fun h => h2 (k2.1 h)
      rw [Mem.update_of_ne _ _ hq, if_neg h2]
      by_cases h1 : x = a ∧ c = 4 + 4 * i1
      · have hq' : rb + x * rowW N + c = q1 := k1.2 h1
        rw [if_pos h1, hq']; simp only [m1, Mem.update_self]
      · have hq' : rb + x * rowW N + c ≠ q1 := fun h => h1 (k1.1 h)
        simp only [m1]; rw [Mem.update_of_ne _ _ hq', if_neg h1]; rfl
  obtain ⟨h0, h1, h2, h3⟩ := h
  have r0 := rd 0 (by omega); have r1 := rd 1 (by omega); have r2 := rd 2 (by omega)
  simp only [Nat.add_zero] at r0
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · rw [r0, h0]; split_ifs <;> omega
  · rw [r1, h1]; split_ifs <;> omega
  · rw [r2, h2]; split_ifs <;> omega
  · obtain ⟨c3, c4, c5, c6⟩ := h3 i hi
    have r3 := rd (3 + 4 * i) (by omega)
    have r4 := rd (4 + 4 * i) (by omega)
    have r5 := rd (5 + 4 * i) (by omega)
    have r6 := rd (6 + 4 * i) (by omega)
    rw [← Nat.add_assoc] at r3 r4 r5 r6
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r3, c3]; split_ifs <;> omega
    · rw [r4, c4]; beta_reduce; split_ifs <;> omega
    · rw [r5, c5]; split_ifs <;> omega
    · rw [r6, c6]; beta_reduce; split_ifs <;> omega

theorem outC_take_succ (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (e i x : ℕ) (he : e < es.length) :
    outC (es.take (e + 1)) rk i x = outC (es.take e) rk i x +
      if x = es[e].1 ∧ i = rk es[e].2 then 1 else 0 := by
  unfold outC
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some, List.countP_append,
    List.countP_singleton]
  congr 1
  by_cases h : x = es[e].1 ∧ i = rk es[e].2
  · rw [if_pos h]; simp [h.1, h.2]
  · rw [if_neg h]
    simp only [decide_eq_true_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h1 h2; exact h ⟨h1.symm, h2.symm⟩

theorem inC_take_succ (es : List (ℕ × ℕ)) (rk : ℕ → ℕ) (e i x : ℕ) (he : e < es.length) :
    inC (es.take (e + 1)) rk i x = inC (es.take e) rk i x +
      if x = es[e].2 ∧ i = rk es[e].1 then 1 else 0 := by
  unfold inC
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some, List.countP_append,
    List.countP_singleton]
  congr 1
  by_cases h : x = es[e].2 ∧ i = rk es[e].1
  · rw [if_pos h]; simp [h.1, h.2]
  · rw [if_neg h]
    simp only [decide_eq_true_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h1 h2; exact h ⟨h1.symm, h2.symm⟩

theorem wf_edgeBody : Wf edgeBody := by unfold edgeBody; wf_tac

set_option maxHeartbeats 0 in
/-- **The counts**: one pass over the edges, `42` steps per edge. -/
theorem runsTo_edgesProg {M : Mem} {n N R E0 fr : ℕ} {rk : ℕ → ℕ} {es : List (ℕ × ℕ)}
    (h1 : M 1 = 1) (h20 : M 20 = fr) (h40 : M 40 = R) (h42 : M 42 = E0)
    (h43 : M 43 = es.length) (hR : ∀ x < n, M (R + x) = rk x) (hrk : ∀ x < n, rk x < N)
    (hE : ∀ e (he : e < es.length), M (E0 + 5 * e + 2) = es[e].1 ∧ M (E0 + 5 * e + 4) = es[e].2)
    (hes : ∀ e ∈ es, e.1 < n ∧ e.2 < n)
    (hS : ∀ x < n, M (fr + x) = fr + n + x * rowW N)
    (hrows : ∀ x < n, RowAt M (fr + n + x * rowW N) N (rk x) (fun _ => 0) (fun _ => 0))
    (hR64 : 64 ≤ R) (hRf : R + n ≤ fr) (hE64 : 64 ≤ E0) (hEf : E0 + 5 * es.length ≤ fr) :
    RunsTo edgesProg (fun m => m = M) (fun m => Keep [2, 3, 4, 5, 6, 29, 49] (fr + n)
      (fr + n + n * rowW N) M m ∧ ∀ x < n, RowAt m (fr + n + x * rowW N) N (rk x)
        (fun i => outC es rk i x) (fun i => inC es rk i x)) (42 * es.length + 4) := by
  set W := rowW N with hW
  have hW' : W = 4 * N + 3 := rfl
  set M1 := ((M.update 49 (E0 + 1)).update 49 (E0 + 1 + 1)).update 29 es.length with hM1
  have hpre : RunsTo (seq (addTo 49 42 1) (seq (addTo 49 49 1) (copyTo 29 43)))
      (fun m => m = M) (fun m => m = M1) 3 := by
    rt
    rw [hM1]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h42, h43]
  have key := runsTo_whileNz_amortX (i := 29) wf_edgeBody
    (fun m => ∃ e ≤ es.length, m 49 = E0 + 5 * e + 2 ∧ m 29 + e = es.length ∧
      Keep [2, 3, 4, 5, 6, 29, 49] (fr + n) (fr + n + n * W) M m ∧
      ∀ x < n, RowAt m (fr + n + x * W) N (rk x) (fun i => outC (es.take e) rk i x)
        (fun i => inC (es.take e) rk i x)) (fun m => 42 * m 29) ?_ M1
    ⟨0, by omega, by rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne],
      by rw [hM1]; simp,
      Keep.of_outside (by rw [hM1]; outside_tac (Outside.refl [2, 3, 4, 5, 6, 29, 49] M)),
      fun x hx => by
        simp only [List.take_zero, outC, inC, List.countP_nil]
        exact (hrows x hx).congr (fun z hz _ => by
          rw [hM1]; simp (disch := omega) only [Mem.update_of_ne])⟩
  · obtain ⟨t, ht⟩ := key
    obtain ⟨M2, ⟨⟨e, he, h49, h29, hkeep, hrw⟩, h0, hpot⟩, hrun⟩ := ht.exact
    have hel : e = es.length := by omega
    subst hel
    have ht' : t ≤ 42 * es.length + 1 := by
      simp only at hpot
      have : M1 29 = es.length := by rw [hM1]; simp
      rw [this] at hpot; omega
    unfold edgesProg
    refine (hpre.seq hrun).mono (by omega) |>.weaken (fun m hm => ?_)
    subst hm
    refine ⟨hkeep, fun x hx => ?_⟩
    have := hrw x hx
    rwa [List.take_length] at this
  intro m ⟨e, he, h49, h29, hkeep, hrw⟩ hne
  have hel : e < es.length := by omega
  obtain ⟨ea, eb⟩ := hE e hel
  obtain ⟨han, hbn⟩ := hes es[e] (List.getElem_mem hel)
  set a := es[e].1 with ha
  set b := es[e].2 with hb
  have g : ∀ z, 64 ≤ z → z < fr + n → m z = M z := fun z h1 h2 =>
    hkeep z (by simp; omega) (Or.inl h2)
  have e1 : m 1 = 1 := by rw [hkeep 1 (by simp) (by omega), h1]
  have e20 : m 20 = fr := by rw [hkeep 20 (by simp) (by omega), h20]
  have e40 : m 40 = R := by rw [hkeep 40 (by simp) (by omega), h40]
  have ga : m (E0 + 5 * e + 2) = a := by rw [g _ (by omega) (by omega), ea]
  have gb : m (E0 + 5 * e + 2 + 1 + 1) = b := by
    rw [g _ (by omega) (by omega), ← eb]
  have gRa : m (R + a) = rk a := by rw [g _ (by omega) (by omega), hR a han]
  have gRb : m (R + b) = rk b := by rw [g _ (by omega) (by omega), hR b hbn]
  have gSa : m (fr + a) = fr + n + a * W := by rw [g _ (by omega) (by omega), hS a han]
  have gSb : m (fr + b) = fr + n + b * W := by rw [g _ (by omega) (by omega), hS b hbn]
  have hra := hrk a han
  have hrb := hrk b hbn
  set q1 := fr + n + a * W + (4 + 4 * rk b) with hq1
  set q2 := fr + n + b * W + (6 + 4 * rk a) with hq2
  have hq12 : q2 ≠ q1 := by
    intro h
    have := (row_cell_eq (rb := fr + n) (W := W) (x := b) (a := a) (c := 6 + 4 * rk a)
      (c' := 4 + 4 * rk b) (by omega) (by omega)).1 h
    omega
  have haW : a * W + W ≤ n * W := by
    have : (a + 1) * W ≤ n * W := Nat.mul_le_mul_right _ han
    rw [Nat.succ_mul] at this; omega
  have hbW : b * W + W ≤ n * W := by
    have : (b + 1) * W ≤ n * W := Nat.mul_le_mul_right _ hbn
    rw [Nat.succ_mul] at this; omega
  set m1 := m.update q1 (m q1 + 1) with hm1
  set bump := m1.update q2 (m1 q2 + 1) with hbump
  refine ⟨40, ?_⟩
  unfold edgeBody
  rt
  refine (?_ : ∀ mf : Mem, ((∀ z, 64 ≤ z → mf z = bump z) ∧ mf 49 = E0 + 5 * (e + 1) + 2 ∧
      mf 29 = m 29 - 1 ∧ ∀ z, z < 64 → z ∉ [2, 3, 4, 5, 6, 29, 49] → mf z = m z) →
    (∃ e' ≤ es.length, mf 49 = E0 + 5 * e' + 2 ∧ mf 29 + e' = es.length ∧
      Keep [2, 3, 4, 5, 6, 29, 49] (fr + n) (fr + n + n * W) M mf ∧
      ∀ x < n, RowAt mf (fr + n + x * W) N (rk x) (fun i => outC (es.take e') rk i x)
        (fun i => inC (es.take e') rk i x)) ∧ 42 * mf 29 + 40 + 2 ≤ 42 * m 29) _ ?_
  · rintro mf ⟨hb, f49, f29, freg⟩
    refine ⟨⟨e + 1, by omega, f49, by omega, fun z hz hr => ?_, fun x hx => ?_⟩, by omega⟩
    · by_cases h64 : z < 64
      · rw [freg z h64 hz]; exact hkeep z hz hr
      · rw [hb z (by omega), hbump, Mem.update_of_ne _ _ (by omega), hm1,
          Mem.update_of_ne _ _ (by omega)]
        exact hkeep z hz hr
    · have hbx := rowAt_bump (a := a) (b := b) (hrw x hx) hrb hra
      refine RowAt.congr (m := bump) ?_ (fun z hz _ => hb z (by omega))
      convert hbx using 2
      · exact outC_take_succ es rk e _ x hel
      · exact inC_take_succ es rk e _ x hel
  · refine ⟨fun z hz => ?_, ?_, ?_, fun z hz hz' => ?_⟩
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e20, e40, h49, ga, gb,
        gRa, gRb, gSa, gSb]
      rw [show fr + n + a * W + (rk b + rk b + (rk b + rk b)) + 1 + 1 + 1 + 1 = q1 by
          rw [hq1]; ring,
        show fr + n + b * W + (rk a + rk a + (rk a + rk a)) + 1 + 1 + 1 + 1 + 1 + 1 = q2 by
          rw [hq2]; ring]
      rw [hbump, hm1]
      simp only [Mem.update]
      split_ifs <;> omega
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e20, e40, h49, ga, gb,
        gRa, gRb, gSa, gSb]
      omega
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e20, e40, h49, ga, gb,
        gRa, gRb, gSa, gSb]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e20, e40, h49, ga, gb,
        gRa, gRb, gSa, gSb]

/-- **One refinement round**: the rows `rowStr` of all vertices, in
`16 N n + 16 n + 42 m + 15` steps. -/
theorem runsTo_rowsProg {M : Mem} {n N R E0 fr : ℕ} {rk : ℕ → ℕ} {es : List (ℕ × ℕ)}
    (h1 : M 1 = 1) (h14 : M 14 = fr) (h21 : M 21 = n) (h40 : M 40 = R) (h41 : M 41 = N)
    (h42 : M 42 = E0) (h43 : M 43 = es.length) (hR : ∀ x < n, M (R + x) = rk x)
    (hrk : ∀ x < n, rk x < N)
    (hE : ∀ e (he : e < es.length), M (E0 + 5 * e + 2) = es[e].1 ∧ M (E0 + 5 * e + 4) = es[e].2)
    (hes : ∀ e ∈ es, e.1 < n ∧ e.2 < n)
    (hR64 : 64 ≤ R) (hRf : R + n ≤ fr) (hE64 : 64 ≤ E0) (hEf : E0 + 5 * es.length ≤ fr) :
    RunsTo rowsProg (fun m => m = M) (fun m => Keep Wrows fr (fr + n + n * rowW N) M m ∧
      m 14 = fr + n + n * rowW N ∧ m 20 = fr ∧
      ∀ x < n, m (fr + x) = fr + n + x * rowW N ∧
        StrAt m (fr + n + x * rowW N) (rowStr es rk N x))
      (16 * N * n + 16 * n + 42 * es.length + 15) := by
  obtain ⟨M1, ⟨hk1, e14, e20, hrows⟩, hrun1⟩ :=
    (runsTo_rowsInit h1 h14 h21 h40 h41 hR hR64 hRf).exact
  have g : ∀ z, z ∉ Wrows → z < fr → M1 z = M z := fun z hz hr => hk1 z hz (Or.inl hr)
  have hrun2 := runsTo_edgesProg (M := M1) (n := n) (N := N) (R := R) (E0 := E0) (fr := fr)
    (rk := rk) (es := es) (by rw [g 1 (by simp) (by omega), h1]) e20
    (by rw [g 40 (by simp) (by omega), h40]) (by rw [g 42 (by simp) (by omega), h42])
    (by rw [g 43 (by simp) (by omega), h43])
    (fun x hx => by rw [g _ (by simp; omega) (by omega), hR x hx]) hrk
    (fun e he => by
      rw [g _ (by simp; omega) (by omega), g _ (by simp; omega) (by omega)]; exact hE e he)
    hes (fun x hx => (hrows x hx).1) (fun x hx => (hrows x hx).2) hR64 hRf hE64 hEf
  unfold rowsProg
  refine ((hrun1.seq hrun2).mono (by omega)).weaken (fun m ⟨hk2, hrw⟩ => ?_)
  have g2 : ∀ z, z ∉ [2, 3, 4, 5, 6, 29, 49] → z < fr + n → m z = M1 z :=
    fun z hz hr => hk2 z hz (Or.inl hr)
  refine ⟨hk1.trans (hk2.mono (a' := fr) (b' := fr + n + n * rowW N) (fun z hz => by
      simp at hz ⊢; omega) (by omega) le_rfl) (fun z hz => hz) le_rfl le_rfl,
    by rw [g2 14 (by simp) (by omega), e14], by rw [g2 20 (by simp) (by omega), e20],
    fun x hx => ⟨by rw [g2 _ (by simp; omega) (by omega), (hrows x hx).1],
      strAt_of_rowAt (hrw x hx)⟩⟩

end TagLin

end Algo
