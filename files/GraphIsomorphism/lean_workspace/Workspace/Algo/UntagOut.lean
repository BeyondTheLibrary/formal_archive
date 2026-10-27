/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1, line 2860: the cost `O(nk + n²m)` of the untagged naive refinement process.
The RAM program, part 2: writing the strings of `X*` once, at the end.
-/
import Workspace.Algo.UntagRAM

/-!
# The untagged process on the RAM: the output

After the rounds, the record of round `i` holds the sorted palette of round `i` and the rank of
every vertex.  The string of vertex `x` after `K` rounds is (`Algo.TagLin.strIter_eq`)
`(^K c₀(x) enc(cnts₀(x)) … enc(cnts_{K-1}(x))`, where `enc(u) = ,u₀,u₁…)` and `cnts_j(x)` is
the tail of the tagged string of `x` in round `j + 1`.  The program writes it letter by letter:
`K` opening parentheses, the input color (copied from record `0`), and for each `j < K` the
counts read off the string of `x` in record `j + 1`.

Registers: `19` the buffer `Q`, `39 = Q + 1`, `44` the write pointer, `34 = 2`, `35 = 0`,
`36 = 4n`, `37 = K`, `38 = 3`, `46` the vertex `x`, `47 = n - x`, `45` the length cell of the
current string, `26` the parentheses left, `48` the next record, `49` the rounds left, `27` twice
the counts left, `28` the next count.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact Babai Babai.TaggedDigraph Babai.ColoredDigraph

variable {r : RawColored}

/-! ## The programs -/

/-- One count `a`: the letters `, (a + 3)`, encoded `1 1 1 (a+3)`. -/
def cBody : Program :=
  seq (storeTo 44 1) (seq (addTo 44 44 1) (seq (storeTo 44 1) (seq (addTo 44 44 1)
  (seq (storeTo 44 1) (seq (addTo 44 44 1) (seq (loadTo 2 28) (seq (addTo 2 2 38)
  (seq (storeTo 44 2) (seq (addTo 44 44 1) (seq (addTo 28 28 34) (subTo 27 27 34)))))))))))

theorem wf_cBody : Wf cBody := by unfold cBody; wf_tac

/-- The letters of the counts `u`. -/
def cntLetters (u : List ℕ) : List ℕ := u.flatMap (fun a => [lComma, lNum a])

theorem cntLetters_take_succ (u : List ℕ) (t : ℕ) (ht : t < u.length) :
    encList Enc.encode (cntLetters (u.take (t + 1))) =
      encList Enc.encode (cntLetters (u.take t)) ++ [1, 1, 1, u[t] + 3] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  unfold cntLetters
  rw [List.flatMap_append, Exact.encList_append]
  rfl

theorem length_cntLetters (u : List ℕ) :
    (encList Enc.encode (cntLetters u)).length = 4 * u.length := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    unfold cntLetters at ih ⊢
    rw [List.flatMap_cons, Exact.encList_append, List.length_append, ih]
    simp [encList, RAM.frame, Enc.encode]; ring

/-- The state of the counts loop after `t` counts. -/
def CInv (m0 : Mem) (u : List ℕ) (p0 w0 t : ℕ) (m : Mem) : Prop :=
  t ≤ u.length ∧ m 27 = 2 * (u.length - t) ∧ m 28 = p0 + 2 * t ∧ m 44 = w0 + 4 * t ∧
    m 1 = 1 ∧ m 34 = 2 ∧ m 38 = 3 ∧
    Blk m w0 (encList Enc.encode (cntLetters (u.take t))) ∧ Keep [2, 27, 28, 44] w0 (w0 + 4 * t) m0 m

theorem runsTo_cBody {m0 m : Mem} {u : List ℕ} {p0 w0 t : ℕ} (ht : t < u.length) (hp : 64 ≤ p0)
    (hread : ∀ i (hi : i < u.length), m0 (p0 + 2 * i) = u[i]) (hpw : p0 + 2 * u.length ≤ w0 + 1)
    (hm : CInv m0 u p0 w0 t m) : RunsTo cBody (fun m' => m' = m) (CInv m0 u p0 w0 (t + 1)) 12 := by
  obtain ⟨-, e27, e28, e44, e1, e34, e38, hb, hk⟩ := hm
  have hut : m (p0 + 2 * t) = u[t] := by
    rw [hk _ (by simp; omega) (by omega)]; exact hread t ht
  have hl := length_cntLetters (u.take t)
  rw [List.length_take, Nat.min_eq_left ht.le] at hl
  unfold cBody
  refine store_seq (add_seq (store_seq (add_seq (store_seq (add_seq (load_seq (add_seq
    (store_seq (add_seq (add_seq (sub_last ?_)))))))))))
  unfold CInv
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e1, e28, e38, e34, e27, hut]
  refine ⟨by omega, by omega, by ring, by ring, trivial, trivial, trivial, ?_, ?_⟩
  · rw [cntLetters_take_succ u t ht, Blk.append, hl]
    refine ⟨hb.congr (fun z h1 h2 => ?_), ?_⟩
    · rw [hl] at h2
      simp (disch := omega) only [Mem.update_of_ne]
    · rw [Blk.cons, Blk.cons, Blk.cons, Blk.cons]
      refine ⟨?_, ?_, ?_, ?_, Blk.nil _ _⟩ <;>
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · intro z hz hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hk z (by simp; omega) (by omega)

/-- **The counts loop**: the letters of `u`, from the cells `p0, p0 + 2, …`, in `14 |u| + 1`
steps. -/
theorem runsTo_cLoop {m0 : Mem} {u : List ℕ} {p0 w0 : ℕ} (hp : 64 ≤ p0)
    (hread : ∀ i (hi : i < u.length), m0 (p0 + 2 * i) = u[i]) (hpw : p0 + 2 * u.length ≤ w0 + 1)
    (h27 : m0 27 = 2 * u.length) (h28 : m0 28 = p0) (h44 : m0 44 = w0) (h1 : m0 1 = 1)
    (h34 : m0 34 = 2) (h38 : m0 38 = 3) :
    RunsTo (whileNz 27 cBody) (fun m => m = m0) (fun m => m 44 = w0 + 4 * u.length ∧
      Blk m w0 (encList Enc.encode (cntLetters u)) ∧
      Keep [2, 27, 28, 44] w0 (w0 + 4 * u.length) m0 m) (14 * u.length + 1) := by
  have hloop := runsTo_whileNz_amort' (i := 27) wf_cBody (fun m => ∃ t, CInv m0 u p0 w0 t m)
    (fun m => 7 * m 27) (fun m ⟨t, ht⟩ hne => ⟨12, (runsTo_cBody (by
      obtain ⟨h1, h2, -⟩ := ht; rw [h2] at hne; omega) hp hread hpw ht).weaken
      (fun m' hm' => ⟨⟨t + 1, hm'⟩, by
        show 7 * m' 27 + 12 + 2 ≤ 7 * m 27
        rw [hm'.2.1, ht.2.1]; have := ht.1; have := hm'.1; omega⟩)⟩)
    m0 ⟨0, by omega, by rw [h27]; rfl, by rw [h28]; rfl, by rw [h44]; rfl, h1, h34, h38,
      Blk.nil _ _, Keep.refl _ _ _ _⟩
  refine (hloop.mono (by show 7 * m0 27 + 1 ≤ _; rw [h27]; omega)).weaken
    (fun m ⟨⟨t, ht, e27, _, e44, _, _, _, hb, hk⟩, h0⟩ => ?_)
  obtain rfl : t = u.length := by omega
  rw [List.take_length] at hb
  exact ⟨e44, hb, hk⟩

/-! ## One round of one vertex -/

/-- Find the string of `x` in the record at `m 48`: its rank `ρ`, the representative `v` of rank
`ρ`, the address `ptr` of the string of `v`; `27` twice the number of counts, `28 = ptr + 4` the
first count. -/
def rPre : Program :=
  seq (addTo 2 48 1) (seq (loadTo 2 2) (seq (addTo 3 2 36) (seq (addTo 3 3 46) (seq (loadTo 3 3)
  (seq (addTo 3 2 3) (seq (loadTo 3 3) (seq (loadTo 4 48) (seq (addTo 4 4 3) (seq (loadTo 4 4)
  (seq (loadTo 27 4) (seq (subTo 27 27 34) (seq (addTo 28 4 38) (addTo 28 28 1)))))))))))))

/-- Close the round: the letter `)`, the next record. -/
def rPost : Program :=
  seq (storeTo 44 1) (seq (addTo 44 44 1) (seq (storeTo 44 34) (seq (addTo 44 44 1)
  (seq (addTo 48 48 38) (subTo 49 49 1)))))

/-- One round `j` of vertex `x`: the counts of round `j`, from the record of round `j + 1`. -/
def rBody : Program := seq rPre (seq (whileNz 27 cBody) rPost)

theorem wf_rBody : Wf rBody := by
  unfold rBody rPre rPost
  exact wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_cBody) (by wf_tac))

theorem PX_getElem?_rX (r : RawTagged) (j : ℕ) {x : ℕ} (hx : x < r.1.length) :
    (PX r j)[rX r j x]? = some (sX r j x) := by
  have hlt := rX_lt r j hx
  rw [NX_eq_length] at hlt
  rw [List.getElem?_eq_getElem hlt]
  congr 1
  have e := rX_eq r j hx
  simp only [e]
  exact List.getElem_idxOf _

/-- **The string of `x` in a record.** -/
theorem runsTo_rPre {m : Mem} {r : RawTagged} {i x Q : ℕ} (hrec : RecOK r m (Fr r) Q i)
    (hx : x < r.1.length) (hF : 200 ≤ Fr r) (h48 : m 48 = 100 + 3 * i) (h46 : m 46 = x)
    (h36 : m 36 = 4 * r.1.length) (h34 : m 34 = 2) (h38 : m 38 = 3) (h1 : m 1 = 1) :
    ∃ ptr, Fr r ≤ ptr ∧ ptr + 1 + 2 * (sX r i x).length ≤ Q ∧ StrAt m ptr (sX r i x) ∧
      RunsTo rPre (fun m' => m' = m) (fun m' => m' 27 = 2 * (sX r i x).length - 2 ∧
        m' 28 = ptr + 4 ∧ m' 4 = ptr ∧
        ∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 → z ≠ 27 → z ≠ 28 → m' z = m z) 14 := by
  set A := m (100 + 3 * i + 1) with hA
  set S := m (100 + 3 * i) with hS
  set ρ := rX r i x with hρ
  have hrk : m (A + 4 * r.1.length + x) = ρ := hrec.rank x hx
  have hρN : ρ < NX r i := rX_lt r i hx
  obtain ⟨hv, hget, hlo, hhi, hstr⟩ := hrec.pal ρ hρN
  rw [← hA] at hv hget hlo hhi hstr
  rw [← hS] at hlo hhi hstr
  set v := m (A + ρ) with hvdef
  have hsv : sX r i v = sX r i x := by
    rw [PX_getElem?_rX r i hx] at hget; exact (Option.some.inj hget).symm
  rw [hsv] at hhi hstr
  set ptr := m (S + v) with hptr
  have hFA : Fr r ≤ A := hrec.loA
  have hFS : Fr r ≤ S := hrec.loS
  refine ⟨ptr, hlo, hhi, hstr, ?_⟩
  have hp0 : m ptr = 2 * (sX r i x).length := hstr.1
  unfold rPre
  refine add_seq (load_seq (add_seq (add_seq (load_seq (add_seq (load_seq (load_seq (add_seq
    (load_seq (load_seq (sub_seq (add_seq (add_last ?_)))))))))))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h48, h46, h36, h34, h38, h1]
  rw [show 100 + 3 * i + 1 = 100 + 3 * i + 1 by rfl, ← hA]
  simp (disch := omega) only [Mem.update_of_ne, hrk, ← hvdef, ← hS]
  refine ⟨by rw [← hptr, hp0], by rw [← hptr], by rw [← hptr], fun z h2 h3 h4 h27 h28 => ?_⟩
  simp (disch := omega) only [Mem.update_of_ne]

theorem encList_encCnt (u : List ℕ) :
    encList Enc.encode (encCnt u) = encList Enc.encode (cntLetters u) ++ [1, 2] := by
  unfold encCnt; rw [Exact.encList_append]; rfl

theorem length_encList_encCnt (u : List ℕ) :
    (encList Enc.encode (encCnt u)).length = 4 * u.length + 2 := by
  rw [encList_encCnt, List.length_append, length_cntLetters]; rfl

/-- **One round of one vertex**: the letters `enc(cnts_j(x))`, in `14 |cnts_j(x)| + 21` steps. -/
theorem runsTo_rBody {m : Mem} {r : RawColored} (hr : r.WF) {j x Q w : ℕ}
    (hrec : RecOK (toTagged r) m (Fr (toTagged r)) Q (j + 1)) (hx : x < r.1.length)
    (hF : 200 ≤ Fr (toTagged r)) (h48 : m 48 = 100 + 3 * (j + 1)) (h46 : m 46 = x)
    (h36 : m 36 = 4 * r.1.length) (h34 : m 34 = 2) (h38 : m 38 = 3) (h1 : m 1 = 1)
    (h44 : m 44 = w) (hQw : Q ≤ w) :
    RunsTo rBody (fun m' => m' = m) (fun m' =>
      m' 44 = w + (4 * (cnts r j x).length + 2) ∧
      Blk m' w (encList Enc.encode (encCnt (cnts r j x))) ∧ m' 48 = 100 + 3 * (j + 2) ∧
      m' 49 = m 49 - 1 ∧ m' 1 = 1 ∧
      Keep [2, 3, 4, 27, 28, 44, 48, 49] w (w + (4 * (cnts r j x).length + 2)) m m')
      (14 * (cnts r j x).length + 21) := by
  obtain ⟨ptr, hlo, hhi, hstr, hpre⟩ := runsTo_rPre (x := x) hrec hx hF h48 h46 h36 h34 h38 h1
  have hs := sX_succ' hr j hx
  set u := cnts r j x with hu
  rw [hs] at hhi hstr hpre
  simp only [List.length_cons] at hhi hpre
  unfold rBody
  refine RunsTo.mono (T := 14 + ((14 * u.length + 1) + 6)) ?_ (by omega)
  refine block_seq hpre (fun M1 ⟨a27, a28, _, aK⟩ => ?_)
  have hread : ∀ t (ht : t < u.length), M1 (ptr + 4 + 2 * t) = u[t] := fun t ht => by
    rw [aK _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    have := (hstr.2 (t + 1) (by simp; omega)).2
    rw [show ptr + 2 + 2 * (t + 1) = ptr + 4 + 2 * t by ring] at this
    rw [this]; rfl
  have g : ∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 → z ≠ 27 → z ≠ 28 → M1 z = m z := aK
  refine block_seq (runsTo_cLoop (u := u) (p0 := ptr + 4) (w0 := w) (by omega) hread (by omega)
    (by rw [a27]; omega) a28 (by rw [g 44 (by omega) (by omega) (by omega) (by omega) (by omega), h44])
    (by rw [g 1 (by omega) (by omega) (by omega) (by omega) (by omega), h1])
    (by rw [g 34 (by omega) (by omega) (by omega) (by omega) (by omega), h34])
    (by rw [g 38 (by omega) (by omega) (by omega) (by omega) (by omega), h38]))
    (fun M2 ⟨b44, hb, hk⟩ => ?_)
  have k : ∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 → z ≠ 27 → z ≠ 28 → z ≠ 44 → z < w → M2 z = m z :=
    fun z a b c d e f h => by
      rw [hk z (by simp; omega) (Or.inl h), g z a b c d e]
  have c1 : M2 1 = 1 := by rw [k 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have c34 : M2 34 = 2 := by rw [k 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h34]
  have c38 : M2 38 = 3 := by rw [k 38 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h38]
  have c48 : M2 48 = 100 + 3 * (j + 1) := by rw [k 48 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h48]
  have c49 : M2 49 = m 49 := k 49 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hl := length_cntLetters u
  unfold rPost
  refine store_seq (add_seq (store_seq (add_seq (add_seq (sub_last ?_)))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, b44, c1, c34, c38, c48, c49]
  refine ⟨by ring, ?_, by ring, trivial, trivial, fun z hz hab => ?_⟩
  · rw [encList_encCnt, Blk.append, hl]
    refine ⟨hb.congr (fun z h1 h2 => ?_), ?_⟩
    · rw [hl] at h2
      simp (disch := omega) only [Mem.update_of_ne]
    · rw [Blk.cons, Blk.cons]
      refine ⟨?_, ?_, Blk.nil _ _⟩ <;>
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    rw [hk z (by simp; omega) (by omega)]
    exact g z (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## The rounds of one vertex -/

/-- The count strings of vertex `x` in the rounds `j < K`. -/
noncomputable def cntsPart (r : RawColored) (K x : ℕ) : List ℕ :=
  (List.range K).flatMap (fun j => encCnt (cnts r j x))

theorem encList_cntsPart_succ (r : RawColored) (j x : ℕ) :
    encList Enc.encode (cntsPart r (j + 1) x) =
      encList Enc.encode (cntsPart r j x) ++ encList Enc.encode (encCnt (cnts r j x)) := by
  unfold cntsPart
  rw [List.range_succ, List.flatMap_append, Exact.encList_append]
  simp

theorem length_cnts_le (r : RawColored) (j x : ℕ) : (cnts r j x).length ≤ 2 * r.1.length := by
  rw [length_cnts]; have := NX_le (toTagged r) j; exact Nat.mul_le_mul_left 2 this

/-- The state of the rounds loop of vertex `x` after `j` rounds. -/
def RInv (r : RawColored) (m0 : Mem) (K x w0 j : ℕ) (m : Mem) : Prop :=
  j ≤ K ∧ m 49 = K - j ∧ m 48 = 100 + 3 * (j + 1) ∧
    m 44 = w0 + (encList Enc.encode (cntsPart r j x)).length ∧
    Blk m w0 (encList Enc.encode (cntsPart r j x)) ∧
    Keep [2, 3, 4, 27, 28, 44, 48, 49] w0 (w0 + (encList Enc.encode (cntsPart r j x)).length) m0 m

/-- **The rounds of vertex `x`**: the letters `enc(cnts₀(x)) … enc(cnts_{K-1}(x))`. -/
theorem runsTo_rLoop {m0 : Mem} {r : RawColored} (hr : r.WF) {K x Q w0 : ℕ}
    (hrecs : ∀ i ≤ K, RecOK (toTagged r) m0 (Fr (toTagged r)) Q i) (hx : x < r.1.length)
    (hF : 200 ≤ Fr (toTagged r)) (hK : 100 + 3 * (K + 1) ≤ Fr (toTagged r))
    (h48 : m0 48 = 103) (h49 : m0 49 = K) (h46 : m0 46 = x)
    (h36 : m0 36 = 4 * r.1.length) (h34 : m0 34 = 2) (h38 : m0 38 = 3) (h1 : m0 1 = 1)
    (h44 : m0 44 = w0) (hQw : Q ≤ w0) :
    RunsTo (whileNz 49 rBody) (fun m => m = m0) (fun m =>
      m 44 = w0 + (encList Enc.encode (cntsPart r K x)).length ∧
      Blk m w0 (encList Enc.encode (cntsPart r K x)) ∧
      Keep [2, 3, 4, 27, 28, 44, 48, 49] w0 (w0 + (encList Enc.encode (cntsPart r K x)).length) m0 m)
      (K * (28 * r.1.length + 23) + 1) := by
  have hFQ : Fr (toTagged r) ≤ Q := by
    have := (hrecs 0 (by omega)).loS; have := (hrecs 0 (by omega)).hiS; omega
  have hloop := runsTo_whileNz_amort' (i := 49) wf_rBody (fun m => ∃ j, RInv r m0 K x w0 j m)
    (fun m => m 49 * (28 * r.1.length + 23)) (fun m ⟨j, hj, e49, e48, e44, hb, hk⟩ hne => by
      have hjK : j < K := by omega
      have g : ∀ z, z ∉ [2, 3, 4, 27, 28, 44, 48, 49] → z < w0 → m z = m0 z :=
        fun z hz h => hk z hz (Or.inl h)
      have hrec : RecOK (toTagged r) m (Fr (toTagged r)) Q (j + 1) :=
        (hrecs (j + 1) (by omega)).congr (fun c hc => g _ (by simp; omega) (by omega))
          (fun z h1 h2 => g z (by simp; omega) (by omega))
      refine ⟨_, (runsTo_rBody hr hrec hx hF e48 (by rw [g 46 (by simp) (by omega), h46])
        (by rw [g 36 (by simp) (by omega), h36]) (by rw [g 34 (by simp) (by omega), h34])
        (by rw [g 38 (by simp) (by omega), h38]) (by rw [g 1 (by simp) (by omega), h1]) e44
        (by omega)).weaken (fun m' ⟨a44, ab, a48, a49, _, ak⟩ => ⟨⟨j + 1, by omega, by rw [a49, e49]; omega,
          a48, ?_, ?_, ?_⟩, ?_⟩)⟩
      · rw [a44, encList_cntsPart_succ, List.length_append, length_encList_encCnt]; ring
      · rw [encList_cntsPart_succ, Blk.append]
        exact ⟨hb.congr (fun z h1 h2 => ak z (by simp; omega) (Or.inl (by omega))), ab⟩
      · intro z hz hab
        rw [encList_cntsPart_succ, List.length_append, length_encList_encCnt] at hab
        rw [ak z hz (by omega), hk z hz (by omega)]
      · show m' 49 * _ + _ + 2 ≤ m 49 * _
        rw [a49, e49]
        have := length_cnts_le r j x
        have e : K - j = (K - j - 1) + 1 := by omega
        rw [e, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
        omega) m0 ⟨0, by omega, by rw [h49]; rfl, by rw [h48], by rw [h44]; rfl, Blk.nil _ _,
      Keep.refl _ _ _ _⟩
  refine (hloop.mono (by show m0 49 * _ + 1 ≤ _; rw [h49])).weaken
    (fun m ⟨⟨j, hj, e49, _, e44, hb, hk⟩, h0⟩ => ?_)
  obtain rfl : j = K := by omega
  exact ⟨e44, hb, hk⟩

/-! ## The opening parentheses and the input color -/

/-- One opening parenthesis `(`, encoded `1 0`. -/
def openBody : Program :=
  seq (storeTo 44 1) (seq (addTo 44 44 1) (seq (storeTo 44 35) (seq (addTo 44 44 1)
    (subTo 26 26 1))))

theorem wf_openBody : Wf openBody := by unfold openBody; wf_tac

theorem encList_replicate_succ (t : ℕ) :
    encList Enc.encode (List.replicate (t + 1) lOpen) =
      encList Enc.encode (List.replicate t lOpen) ++ [1, 0] := by
  rw [List.replicate_succ', Exact.encList_append]; rfl

theorem length_encList_replicate (t : ℕ) :
    (encList Enc.encode (List.replicate t lOpen)).length = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [encList_replicate_succ, List.length_append, ih]; simp; ring

/-- **The opening parentheses**: `K` letters `(`, in `7 K + 1` steps. -/
theorem runsTo_openLoop {m0 : Mem} {K w0 : ℕ} (h26 : m0 26 = K) (h44 : m0 44 = w0)
    (h1 : m0 1 = 1) (h35 : m0 35 = 0) (hw : 64 ≤ w0) :
    RunsTo (whileNz 26 openBody) (fun m => m = m0) (fun m => m 44 = w0 + 2 * K ∧
      Blk m w0 (encList Enc.encode (List.replicate K lOpen)) ∧
      Keep [26, 44] w0 (w0 + 2 * K) m0 m) (7 * K + 1) := by
  let inv : Mem → Prop := fun m => ∃ t ≤ K, m 26 = K - t ∧ m 44 = w0 + 2 * t ∧
    Blk m w0 (encList Enc.encode (List.replicate t lOpen)) ∧ Keep [26, 44] w0 (w0 + 2 * t) m0 m
  have hloop := runsTo_whileNz_amort' (i := 26) wf_openBody inv (fun m => 7 * m 26)
    (fun m ⟨t, ht, e26, e44, hb, hk⟩ hne => by
      have g1 : m 1 = 1 := by rw [hk 1 (by simp) (by omega), h1]
      have g35 : m 35 = 0 := by rw [hk 35 (by simp) (by omega), h35]
      refine ⟨5, ?_⟩
      unfold openBody
      refine store_seq (add_seq (store_seq (add_seq (sub_last ?_))))
      have hl := length_encList_replicate t
      refine ⟨⟨t + 1, by omega, ?_, ?_, ?_, fun z hz hab => ?_⟩, ?_⟩
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e26, g1]; omega
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, g1]; ring
      · rw [encList_replicate_succ, Blk.append, hl]
        refine ⟨hb.congr (fun z h1 h2 => ?_), ?_⟩
        · rw [hl] at h2
          simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, g1]
        · rw [Blk.cons, Blk.cons]
          refine ⟨?_, ?_, Blk.nil _ _⟩ <;>
            simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, g1, g35]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, g1]
        exact hk z (by simp; omega) (by omega)
      · show 7 * _ + 5 + 2 ≤ 7 * m 26
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e26, g1]
        omega)
    m0 ⟨0, by omega, by rw [h26]; rfl, by rw [h44]; rfl, Blk.nil _ _, Keep.refl _ _ _ _⟩
  refine (hloop.mono (by show 7 * m0 26 + 1 ≤ _; rw [h26])).weaken
    (fun m ⟨⟨t, ht, e26, e44, hb, hk⟩, h0⟩ => ?_)
  obtain rfl : t = K := by omega
  exact ⟨e44, hb, hk⟩

/-- Copy the input color of `x` from record `0`. -/
def c0P : Program :=
  seq (assign 48 100) (seq rPre (seq (addTo 3 4 1) (seq (loadTo 4 4) (cpAdv 3 4))))

theorem wf_c0P : Wf c0P := by
  unfold c0P rPre
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_cpAdv _ _))))

/-- **The input color of `x`**, copied from record `0`: `14 k + 23` steps, `k` its length. -/
theorem runsTo_c0P {m : Mem} {r : RawColored} {x Q w : ℕ}
    (hrec : RecOK (toTagged r) m (Fr (toTagged r)) Q 0) (hx : x < r.1.length)
    (hF : 200 ≤ Fr (toTagged r)) (h46 : m 46 = x)
    (h36 : m 36 = 4 * r.1.length) (h34 : m 34 = 2) (h38 : m 38 = 3) (h1 : m 1 = 1)
    (h44 : m 44 = w) (hQw : Q ≤ w) :
    RunsTo c0P (fun m' => m' = m) (fun m' =>
      m' 44 = w + 2 * r.1[x].length ∧ Blk m' w (encList Enc.encode r.1[x]) ∧ m' 1 = 1 ∧
      Keep [2, 3, 4, 27, 28, 44, 48, 59, 60, 61, 62, 63] w (w + 2 * r.1[x].length) m m')
      (14 * r.1[x].length + 23) := by
  have hs0 : sX (toTagged r) 0 x = r.1[x] := sX_zero (toTagged r) hx
  have hFQ : Fr (toTagged r) ≤ Q := by have := hrec.loS; have := hrec.hiS; omega
  unfold c0P
  refine RunsTo.mono (T := 1 + (14 + (1 + (1 + (7 * (Enc.encode r.1[x]).length + 6))))) ?_
    (by rw [ExplLinear.length_encode_nat_list]; omega)
  refine assign_seq ?_
  have g0 : ∀ z, z ≠ 48 → (m.update 48 100) z = m z := fun z hz => Mem.update_of_ne _ _ hz
  have hrec0 : RecOK (toTagged r) (m.update 48 100) (Fr (toTagged r)) Q 0 :=
    hrec.congr (fun c hc => g0 _ (by omega)) (fun z h1 h2 => g0 z (by omega))
  obtain ⟨ptr, hlo, hhi, hstr, hpre⟩ := runsTo_rPre (x := x) hrec0 hx hF (by simp)
    (by rw [g0 _ (by omega), h46]) (by rw [g0 _ (by omega), h36]; rfl) (by rw [g0 _ (by omega), h34])
    (by rw [g0 _ (by omega), h38]) (by rw [g0 _ (by omega), h1])
  rw [hs0] at hhi hstr
  refine block_seq hpre (fun M1 ⟨_, _, a4, aK⟩ => ?_)
  have g : ∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 → z ≠ 27 → z ≠ 28 → z ≠ 48 → M1 z = m z :=
    fun z a b c d e f => by rw [aK z a b c d e, g0 z f]
  have hp1 : M1 ptr = 2 * r.1[x].length := by
    rw [aK _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hstr.1
  have hblk : Blk (m.update 48 100) (ptr + 1) (Enc.encode r.1[x]) :=
    (Blk.frame_iff.1 (strAt_iff_blk.1 hstr)).2
  refine add_seq (load_seq ?_)
  set M2 := (M1.update 3 (M1 4 + M1 1)).update 4 ((M1.update 3 (M1 4 + M1 1)) ((M1.update 3
    (M1 4 + M1 1)) 4)) with hM2
  have c1 : M1 1 = 1 := by rw [g 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have c44 : M1 44 = w := by
    rw [g 44 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h44]
  have k2 : ∀ z, z ≠ 3 → z ≠ 4 → M2 z = M1 z := fun z a b => by
    simp (disch := omega) only [hM2, Mem.update_of_ne]
  have b3 : M2 3 = ptr + 1 := by simp (disch := omega) only [hM2, Mem.update_self, Mem.update_of_ne, a4, c1]
  have b4 : M2 4 = 2 * r.1[x].length := by
    simp (disch := omega) only [hM2, Mem.update_self, Mem.update_of_ne, a4, c1, hp1]
  have b44 : M2 44 = w := by rw [k2 44 (by omega) (by omega), c44]
  have hlen := ExplLinear.length_encode_nat_list r.1[x]
  refine (runsTo_cpAdv (M := M2) (src := 3) (ln := 4) (xs := Enc.encode r.1[x]) (by omega)
    (by omega) (by rw [b3]; omega) (by rw [b44]; omega) (by rw [b3, b4, b44]; omega)
    (by rw [b3]; exact hblk.congr (fun z h1 h2 => by
      rw [k2 z (by omega) (by omega), aK z (by omega) (by omega) (by omega) (by omega) (by omega)]))
    (by rw [b4, hlen])).weaken (fun m' ⟨hb, hk, h44'⟩ => ?_)
  rw [b44] at hb hk h44'
  rw [hlen] at hk h44'
  refine ⟨h44', hb, ?_, fun z hz hab => ?_⟩
  · rw [hk 1 (by simp) (by omega), k2 1 (by omega) (by omega), c1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hk z (by simp; omega) hab, k2 z (by omega) (by omega)]
    exact g z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## One vertex -/

/-- The length cell of the string of `x`, the next vertex. -/
def vPost : Program :=
  seq (subTo 2 44 45) (seq (subTo 2 2 1) (seq (storeTo 45 2) (seq (addTo 46 46 1)
    (subTo 47 47 1))))

/-- The string of vertex `x`: its length cell (patched at the end), `K` opening parentheses,
the input color, the counts of the rounds `j < K`. -/
def vBody : Program :=
  seq (copyTo 45 44) (seq (addTo 44 44 1) (seq (copyTo 26 37) (seq (whileNz 26 openBody)
  (seq c0P (seq (copyTo 49 37) (seq (assign 48 103) (seq (whileNz 49 rBody) vPost)))))))

theorem wf_vBody : Wf vBody := by
  unfold vBody
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq
    (wf_whileNz wf_openBody) (wf_seq wf_c0P (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (wf_whileNz wf_rBody) (by unfold vPost; wf_tac))))))))

/-- The string of vertex `x` after `K` rounds (`Algo.TagLin.strIter_eq`). -/
noncomputable def uS (r : RawColored) (K x : ℕ) : List ℕ :=
  List.replicate K lOpen ++ (r.1.getD x [] ++ cntsPart r K x)

/-- The registers the parts of one vertex write. -/
notation "Wm" => [2, 3, 4, 26, 27, 28, 44, 45, 48, 49, 59, 60, 61, 62, 63]

/-- The registers one vertex writes. -/
notation "Wv" => [2, 3, 4, 26, 27, 28, 44, 45, 46, 47, 48, 49, 59, 60, 61, 62, 63]

theorem encode_uS (r : RawColored) (K x : ℕ) :
    Enc.encode (uS r K x) = encList Enc.encode (List.replicate K lOpen) ++
      (encList Enc.encode (r.1.getD x []) ++ encList Enc.encode (cntsPart r K x)) := by
  show encList Enc.encode (uS r K x) = _
  unfold uS; rw [Exact.encList_append, Exact.encList_append]

/-- The cost of one vertex. -/
def vCost (n K k : ℕ) : ℕ := 7 * K + 14 * k + K * (28 * n + 23) + 35

set_option maxHeartbeats 1000000 in
/-- **One vertex**: the framed string of `x`, at the write pointer `w`. -/
theorem runsTo_vBody {m : Mem} {r : RawColored} (hr : r.WF) {K x Q w : ℕ}
    (hrecs : ∀ i ≤ K, RecOK (toTagged r) m (Fr (toTagged r)) Q i) (hx : x < r.1.length)
    (hF : 200 ≤ Fr (toTagged r)) (hK : 100 + 3 * (K + 1) ≤ Fr (toTagged r))
    (h37 : m 37 = K) (h46 : m 46 = x) (h36 : m 36 = 4 * r.1.length) (h34 : m 34 = 2)
    (h35 : m 35 = 0) (h38 : m 38 = 3) (h1 : m 1 = 1) (h44 : m 44 = w) (hQw : Q ≤ w) :
    RunsTo vBody (fun m' => m' = m) (fun m' =>
      m' 44 = w + 1 + (Enc.encode (uS r K x)).length ∧
      Blk m' w (frame (Enc.encode (uS r K x))) ∧ m' 46 = x + 1 ∧ m' 47 = m 47 - 1 ∧
      Keep Wv w (w + 1 + (Enc.encode (uS r K x)).length) m m')
      (vCost r.1.length K r.1[x].length) := by
  have hFQ : Fr (toTagged r) ≤ Q := by
    have := (hrecs 0 (by omega)).loS; have := (hrecs 0 (by omega)).hiS; omega
  have hgx : r.1.getD x [] = r.1[x] := List.getD_eq_getElem _ _ hx
  set R := encList Enc.encode (List.replicate K lOpen) with hR
  set C := encList Enc.encode r.1[x] with hC
  set P := encList Enc.encode (cntsPart r K x) with hP
  have hRl : R.length = 2 * K := length_encList_replicate K
  have hCl : C.length = 2 * r.1[x].length := ExplLinear.length_encode_nat_list _
  have henc : Enc.encode (uS r K x) = R ++ (C ++ P) := by rw [encode_uS, hgx]
  rw [henc]
  simp only [List.length_append]
  rw [hRl, hCl]
  set k := r.1[x].length with hk
  clear_value R C P
  unfold vBody vCost
  refine RunsTo.mono (T := 1 + (1 + (1 + ((7 * K + 1) + ((14 * k + 23) + (1 + (1 +
    ((K * (28 * r.1.length + 23) + 1) + 5)))))))) ?_ (by omega)
  refine copy_seq (add_seq (copy_seq ?_))
  set M0 := ((m.update 45 (m 44)).update 44 ((m.update 45 (m 44)) 44 +
    (m.update 45 (m 44)) 1)).update 26 (((m.update 45 (m 44)).update 44 ((m.update 45 (m 44)) 44 +
    (m.update 45 (m 44)) 1)) 37) with hM0
  have g0 : ∀ z, z ≠ 26 → z ≠ 44 → z ≠ 45 → M0 z = m z := fun z a b c => by
    simp (disch := omega) only [hM0, Mem.update_of_ne]
  have a26 : M0 26 = K := by simp (disch := omega) only [hM0, Mem.update_self, Mem.update_of_ne, h37]
  have a44 : M0 44 = w + 1 := by simp (disch := omega) only [hM0, Mem.update_self, Mem.update_of_ne, h44, h1]
  have a45 : M0 45 = w := by simp (disch := omega) only [hM0, Mem.update_self, Mem.update_of_ne, h44]
  clear_value M0
  clear hM0
  refine block_seq (runsTo_openLoop a26 a44 (by rw [g0 1 (by omega) (by omega) (by omega), h1])
    (by rw [g0 35 (by omega) (by omega) (by omega), h35]) (by omega)) (fun M1 ⟨b44, bR, bK⟩ => ?_)
  have g1 : ∀ z, z ∉ Wm → z < w + 1 → M1 z = m z := fun z hz h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [bK z (by simp; omega) (Or.inl h), g0 z (by omega) (by omega) (by omega)]
  have hrecs1 : ∀ i ≤ K, RecOK (toTagged r) M1 (Fr (toTagged r)) Q i := fun i hi =>
    (hrecs i hi).congr (fun c hc => g1 _ (by simp; omega) (by omega))
      (fun z h1 h2 => g1 z (by simp; omega) (by omega))
  refine block_seq (runsTo_c0P (x := x) (hrecs1 0 (by omega)) hx hF
    (by rw [g1 46 (by simp) (by omega), h46]) (by rw [g1 36 (by simp) (by omega), h36])
    (by rw [g1 34 (by simp) (by omega), h34]) (by rw [g1 38 (by simp) (by omega), h38])
    (by rw [g1 1 (by simp) (by omega), h1]) b44 (by omega)) (fun M2 ⟨c44, cC, c1, cK⟩ => ?_)
  rw [← hk] at c44 cK
  set w2 := w + 1 + 2 * K + 2 * k with hw2
  have g2 : ∀ z, z ∉ Wm → z < w + 1 → M2 z = m z := fun z hz h => by
    rw [cK z (by simp at hz ⊢; omega) (Or.inl (by omega)), g1 z hz h]
  refine copy_seq (assign_seq ?_)
  set M3 := (M2.update 49 (M2 37)).update 48 103 with hM3
  have g3 : ∀ z, z ≠ 48 → z ≠ 49 → M3 z = M2 z := fun z a b => by
    simp (disch := omega) only [hM3, Mem.update_of_ne]
  have hrecs3 : ∀ i ≤ K, RecOK (toTagged r) M3 (Fr (toTagged r)) Q i := fun i hi =>
    (hrecs i hi).congr
      (fun c hc => by rw [g3 _ (by omega) (by omega), g2 _ (by simp; omega) (by omega)])
      (fun z h1 h2 => by rw [g3 _ (by omega) (by omega), g2 z (by simp; omega) (by omega)])
  have f49 : M3 49 = K := by
    simp (disch := omega) only [hM3, Mem.update_self, Mem.update_of_ne]
    rw [g2 37 (by simp) (by omega), h37]
  have f48 : M3 48 = 103 := by simp [hM3]
  clear_value M3
  clear hM3
  refine block_seq (runsTo_rLoop (x := x) (w0 := w2) hr hrecs3 hx hF hK
    f48 f49
    (by rw [g3 _ (by omega) (by omega), g2 46 (by simp) (by omega), h46])
    (by rw [g3 _ (by omega) (by omega), g2 36 (by simp) (by omega), h36])
    (by rw [g3 _ (by omega) (by omega), g2 34 (by simp) (by omega), h34])
    (by rw [g3 _ (by omega) (by omega), g2 38 (by simp) (by omega), h38])
    (by rw [g3 _ (by omega) (by omega), c1])
    (by rw [g3 _ (by omega) (by omega), c44]) (by omega)) (fun M4 ⟨d44, dP, dK⟩ => ?_)
  rw [← hP] at d44 dP dK
  have g4 : ∀ z, z ∉ Wm → z < w2 → M4 z = M2 z := fun z hz h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [dK z (by simp; omega) (Or.inl h), g3 z (by omega) (by omega)]
  have e45 : M4 45 = w := by
    rw [dK 45 (by simp) (by omega), g3 45 (by omega) (by omega), cK 45 (by simp) (by omega),
      bK 45 (by simp) (by omega), a45]
  have e1 : M4 1 = 1 := by
    rw [dK 1 (by simp) (by omega), g3 1 (by omega) (by omega), c1]
  have e46 : M4 46 = x := by rw [g4 46 (by simp) (by omega), g2 46 (by simp) (by omega), h46]
  have e47 : M4 47 = m 47 := by rw [g4 47 (by simp) (by omega), g2 47 (by simp) (by omega)]
  unfold vPost
  refine sub_seq (sub_seq (store_seq (add_seq (sub_last ?_))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e45, e1, d44, e46, e47]
  refine ⟨?_, ?_, trivial, trivial, fun z hz hab => ?_⟩
  · rw [hw2]; ring
  · rw [Blk.frame_iff]
    refine ⟨?_, ?_⟩
    · simp only [Mem.update_of_ne _ _ (show w ≠ 47 by omega), Mem.update_of_ne _ _ (show w ≠ 46 by omega),
        Mem.update_self, List.length_append, hRl, hCl, hw2]
      omega
    · rw [Blk.append, Blk.append, hRl, hCl]
      rw [← hR] at bR
      rw [← hC] at cC
      refine ⟨bR.congr (fun z h1 h2 => ?_), cC.congr (fun z h1 h2 => ?_),
        dP.congr (fun z h1 h2 => ?_)⟩
      · rw [hRl] at h2
        simp (disch := omega) only [Mem.update_of_ne]
        rw [g4 z (by simp; omega) (by omega), cK z (by simp; omega) (Or.inl (by omega))]
      · rw [hCl] at h2
        simp (disch := omega) only [Mem.update_of_ne]
        rw [g4 z (by simp; omega) (by omega)]
      · simp (disch := omega) only [Mem.update_of_ne]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    rw [dK z (by simp; omega) (by omega), g3 z (by omega) (by omega),
      cK z (by simp; omega) (by omega), bK z (by simp; omega) (by omega),
      g0 z (by omega) (by omega) (by omega)]

/-! ## All vertices -/

/-- The strings of all vertices after `K` rounds. -/
noncomputable def uStrs (r : RawColored) (K : ℕ) : List (List ℕ) :=
  (List.range r.1.length).map (uS r K)

theorem length_uStrs (r : RawColored) (K : ℕ) : (uStrs r K).length = r.1.length := by
  simp [uStrs]

theorem getElem_uStrs (r : RawColored) (K : ℕ) {x : ℕ} (hx : x < (uStrs r K).length) :
    (uStrs r K)[x] = uS r K x := by
  simp [uStrs]

/-- **All vertices**: the strings of `X*`, from `w0`. -/
theorem runsTo_vLoop {m0 : Mem} {r : RawColored} (hr : r.WF) {K Q w0 k : ℕ}
    (hk : ∀ s ∈ r.1, s.length = k)
    (hrecs : ∀ i ≤ K, RecOK (toTagged r) m0 (Fr (toTagged r)) Q i)
    (hF : 200 ≤ Fr (toTagged r)) (hK : 100 + 3 * (K + 1) ≤ Fr (toTagged r))
    (h37 : m0 37 = K) (h46 : m0 46 = 0) (h47 : m0 47 = r.1.length) (h36 : m0 36 = 4 * r.1.length)
    (h34 : m0 34 = 2) (h35 : m0 35 = 0) (h38 : m0 38 = 3) (h1 : m0 1 = 1) (h44 : m0 44 = w0)
    (hQw : Q ≤ w0) :
    RunsTo (whileNz 47 vBody) (fun m => m = m0) (fun m =>
      m 44 = w0 + (encList Enc.encode (uStrs r K)).length ∧
      Blk m w0 (encList Enc.encode (uStrs r K)) ∧
      Keep Wv w0 (w0 + (encList Enc.encode (uStrs r K)).length) m0 m)
      (r.1.length * (vCost r.1.length K k + 2) + 1) := by
  set n := r.1.length with hn
  set S := uStrs r K with hS
  have hSn : S.length = n := length_uStrs r K
  have hFQ : Fr (toTagged r) ≤ Q := by
    have := (hrecs 0 (by omega)).loS; have := (hrecs 0 (by omega)).hiS; omega
  let inv : Mem → Prop := fun m => ∃ x ≤ n, m 46 = x ∧ m 47 = n - x ∧
    m 44 = w0 + (encList Enc.encode (S.take x)).length ∧
    Blk m w0 (encList Enc.encode (S.take x)) ∧
    Keep Wv w0 (w0 + (encList Enc.encode (S.take x)).length) m0 m
  have hloop := runsTo_whileNz_amort' (i := 47) wf_vBody inv (fun m => m 47 * (vCost n K k + 2))
    (fun m ⟨x, hx, e46, e47, e44, hb, hkp⟩ hne => by
      have hxn : x < n := by omega
      have g : ∀ z, z ∉ Wv → z < w0 → m z = m0 z := fun z hz h => hkp z hz (Or.inl h)
      have hrecs' : ∀ i ≤ K, RecOK (toTagged r) m (Fr (toTagged r)) Q i := fun i hi =>
        (hrecs i hi).congr (fun c hc => g _ (by simp; omega) (by omega))
          (fun z h1 h2 => g z (by simp; omega) (by omega))
      have hkx : r.1[x].length = k := hk _ (List.getElem_mem _)
      have hE : encList Enc.encode (S.take (x + 1)) =
          encList Enc.encode (S.take x) ++ frame (Enc.encode (uS r K x)) := by
        rw [encList_take_succ _ _ _ (by omega)]
        congr 3
        exact getElem_uStrs r K _
      refine ⟨_, (runsTo_vBody hr hrecs' hxn hF hK (by rw [g 37 (by simp) (by omega), h37]) e46
        (by rw [g 36 (by simp) (by omega), h36]) (by rw [g 34 (by simp) (by omega), h34])
        (by rw [g 35 (by simp) (by omega), h35]) (by rw [g 38 (by simp) (by omega), h38])
        (by rw [g 1 (by simp) (by omega), h1]) e44 (by omega)).weaken
        (fun m' ⟨a44, ab, a46, a47, ak⟩ => ⟨⟨x + 1, by omega, a46, by rw [a47, e47]; omega, ?_, ?_, ?_⟩, ?_⟩)⟩
      · rw [a44, hE, List.length_append]; simp [RAM.frame]; ring
      · rw [hE, Blk.append]
        exact ⟨hb.congr (fun z h1 h2 => ak z (by simp; omega) (Or.inl (by omega))), ab⟩
      · intro z hz hab
        rw [hE, List.length_append] at hab
        simp only [RAM.frame, List.length_cons] at hab
        rw [ak z hz (by omega), hkp z hz (by omega)]
      · show m' 47 * _ + _ + 2 ≤ m 47 * _
        rw [a47, e47, hkx]
        have e : n - x = (n - x - 1) + 1 := by omega
        rw [e, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
        have : vCost r.1.length K k = vCost n K k := rfl
        omega)
    m0 ⟨0, by omega, h46, by rw [h47]; rfl, by rw [h44]; rfl, Blk.nil _ _, Keep.refl _ _ _ _⟩
  refine (hloop.mono (by show m0 47 * _ + 1 ≤ _; rw [h47])).weaken
    (fun m ⟨⟨x, hx, _, e47, e44, hb, hkp⟩, h0⟩ => ?_)
  obtain rfl : x = n := by omega
  rw [← hSn, List.take_length] at e44 hb hkp
  exact ⟨e44, hb, hkp⟩

/-! ## The head and the tail -/

/-- The constants, the buffer `Q = m 14`, the first vertex. -/
def uHeadP : Program :=
  seq (assign 34 2) (seq (assign 35 0) (seq (assign 38 3) (seq (copyTo 19 14) (seq (addTo 39 19 1)
  (seq (addTo 44 19 34) (seq (addTo 36 21 21) (seq (addTo 36 36 36) (seq (subTo 37 54 34)
  (seq (assign 46 0) (copyTo 47 21))))))))))

theorem runsTo_uHeadP {M : Mem} {n K : ℕ} (h1 : M 1 = 1) (h21 : M 21 = n) (h54 : M 54 = K + 2) :
    RunsTo uHeadP (fun m => m = M) (fun m => m 19 = M 14 ∧ m 39 = M 14 + 1 ∧ m 44 = M 14 + 2 ∧
      m 34 = 2 ∧ m 35 = 0 ∧ m 38 = 3 ∧ m 36 = 4 * n ∧ m 37 = K ∧ m 46 = 0 ∧ m 47 = n ∧
      ∀ z, z ∉ [19, 34, 35, 36, 37, 38, 39, 44, 46, 47] → m z = M z) 11 := by
  unfold uHeadP
  refine assign_seq (assign_seq (assign_seq (copy_seq (add_seq (add_seq (add_seq (add_seq
    (sub_seq (assign_seq (copy_last ?_))))))))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h21, h54]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, by ring, by omega, trivial, trivial,
    fun z hz => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  simp (disch := omega) only [Mem.update_of_ne]

/-- The length cell of the strings, the edges (copied from `E = m 15`), the length cell of the
output. -/
def uTailP : Program :=
  seq (subTo 2 44 19) (seq (subTo 2 2 34) (seq (storeTo 39 2) (seq (loadTo 2 15) (seq (addTo 2 2 1)
  (seq (cpAdv 15 2) (seq (subTo 2 44 19) (seq (subTo 2 2 1) (storeTo 19 2))))))))

theorem wf_uTailP : Wf uTailP := by
  unfold uTailP
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_seq (wf_cpAdv _ _) (by wf_tac))))))

/-- **Move** a block `fo` from `Q = m 19` (ending at `m 44`) to `16`. -/
theorem runsTo_moveP {M : Mem} {Q : ℕ} {fo : List ℕ} (h19 : M 19 = Q) (h44 : M 44 = Q + fo.length)
    (hb : Blk M Q fo) (hQ : 200 ≤ Q) :
    RunsTo moveP (fun m => m = M) (fun m => Blk m 16 fo) (7 * fo.length + 8) := by
  unfold moveP
  refine RunsTo.mono (T := 1 + (1 + (1 + (7 * fo.length + 5)))) ?_ (by omega)
  refine copy_seq (assign_seq (sub_seq ?_))
  set M2 := ((M.update 0 (M 19)).update 1 16).update 2
    (((M.update 0 (M 19)).update 1 16) 44 - ((M.update 0 (M 19)).update 1 16) 19) with hM2
  have a0 : M2 0 = Q := by simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne, h19]
  have a1 : M2 1 = 16 := by simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne]
  have a2 : M2 2 = fo.length := by
    simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne, h19, h44]; omega
  have aK : ∀ z, 3 ≤ z → M2 z = M z := fun z hz => by
    simp (disch := omega) only [M2, Mem.update_of_ne]
  clear_value M2
  refine ((Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) M2 (by omega)
    (by omega) (Or.inl (by omega))).mono (by rw [a2])).weaken (fun m ⟨hc, _⟩ => ?_)
  intro j hj
  have := hc j (by rw [a2]; exact hj)
  rw [a1, a0, aK _ (by omega)] at this
  rw [this]; exact hb j hj

/-- **The tail**: the length cell of the strings, the edges, the length cell of the output. -/
theorem runsTo_uTailP {M : Mem} {Q E : ℕ} {S X : List ℕ} (h19 : M 19 = Q) (h39 : M 39 = Q + 1)
    (h44 : M 44 = Q + 2 + S.length) (h34 : M 34 = 2) (h1 : M 1 = 1) (h15 : M 15 = E)
    (hE : Blk M E (frame X)) (hEQ : E + X.length + 1 ≤ Q) (h64 : 64 ≤ E)
    (hS : Blk M (Q + 2) S) :
    RunsTo uTailP (fun m => m = M) (fun m => m 19 = Q ∧
      m 44 = Q + (frame (frame S ++ frame X)).length ∧ Blk m Q (frame (frame S ++ frame X)))
      (7 * X.length + 22) := by
  have hXf : (frame X).length = X.length + 1 := by simp [RAM.frame]
  obtain ⟨hE0, -⟩ := Blk.frame_iff.1 hE
  unfold uTailP
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + ((7 * (frame X).length + 6) + (1 + (1 + 1))))))))
    ?_ (by rw [hXf]; omega)
  refine sub_seq (sub_seq (store_seq (load_seq (add_seq ?_))))
  refine ExplLinear.at_mem (fun M1 => (∀ z, z ≠ 2 → z ≠ Q + 1 → M1 z = M z) ∧
    M1 2 = X.length + 1 ∧ M1 (Q + 1) = S.length) ⟨fun z a b => ?_, ?_, ?_⟩ (fun M1 ⟨k1, a2, aQ⟩ => ?_)
  · simp (disch := omega) only [Mem.update_of_ne, h39]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h39, h44, h19, h34, h15, h1, hE0]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h39, h44, h19, h34, h15, h1, hE0]
    omega
  have c15 : M1 15 = E := by rw [k1 15 (by omega) (by omega), h15]
  have c44 : M1 44 = Q + 2 + S.length := by rw [k1 44 (by omega) (by omega), h44]
  refine block_seq (runsTo_cpAdv (M := M1) (src := 15) (ln := 2) (xs := frame X) (by omega)
    (by omega) (by rw [c15]; omega) (by rw [c44]; omega) (by rw [c15, a2, c44]; omega)
    (by rw [c15]; exact hE.congr (fun z h1 h2 => k1 z (by omega) (by rw [hXf] at h2; omega)))
    (by rw [a2, hXf])) (fun M2 ⟨hb2, hk2, h44'⟩ => ?_)
  rw [c44] at hb2 hk2 h44'
  rw [hXf] at hk2 h44'
  have k2 : ∀ z, z ∉ [44, 59, 60, 61, 62, 63] → z < Q + 2 + S.length → M2 z = M1 z :=
    fun z hz h => hk2 z hz (Or.inl h)
  have d19 : M2 19 = Q := by rw [k2 19 (by simp) (by omega), k1 19 (by omega) (by omega), h19]
  have d1 : M2 1 = 1 := by rw [k2 1 (by simp) (by omega), k1 1 (by omega) (by omega), h1]
  refine sub_seq (sub_seq (store_last ?_))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, d19, d1, h44']
  have hlo : (frame (frame S ++ frame X)).length = S.length + X.length + 3 := by
    simp [RAM.frame]; omega
  refine ⟨trivial, by rw [hlo]; omega, ?_⟩
  rw [Blk.frame_iff, Blk.append, Blk.frame_iff, Blk.frame_iff]
  simp only [RAM.frame, List.length_cons, List.length_append]
  refine ⟨by simp only [Mem.update_self]; omega, ⟨?_, fun j hj => ?_⟩, ?_⟩
  · simp (disch := omega) only [Mem.update_of_ne]
    rw [k2 _ (by simp; omega) (by omega), aQ]
  · simp (disch := omega) only [Mem.update_of_ne]
    rw [k2 _ (by simp; omega) (by omega), k1 _ (by omega) (by omega),
      show Q + 1 + 1 + j = Q + 2 + j by ring]
    exact hS j hj
  · rw [show Q + 1 + (S.length + 1) = Q + 2 + S.length by ring]
    exact Blk.frame_iff.1 (hb2.congr (fun z h1 h2 => by
      rw [hXf] at h2
      simp (disch := omega) only [Mem.update_of_ne]))

/-! ## The output phase -/

/-- Write the strings of `X*` and the edges, and move the output to `16`. -/
def uOutP : Program := seq uHeadP (seq (whileNz 47 vBody) (seq uTailP moveP))

/-- The time of the output phase. -/
def tUOut (n K k L : ℕ) : ℕ := 11 + ((n * (vCost n K k + 2) + 1) + ((7 * L + 22) + (7 * L + 8)))

/-- **The output phase**: from the state after the rounds, the strings of `X*` and the edges,
framed at `16`. -/
theorem runsTo_uOutP {M : Mem} {r : RawColored} (hr : r.WF) {k : ℕ}
    (hk : ∀ s ∈ r.1, s.length = k)
    (hM : MInv (toTagged r) (stopIdx (decTagged (toTagged r)) + 1) M) :
    RunsTo uOutP (fun m => m = M) (fun m => Blk m 16 (frame (frame (encList Enc.encode
      (uStrs r (stopIdx (decTagged (toTagged r))))) ++ frame (encList Enc.encode r.2))))
      (tUOut r.1.length (stopIdx (decTagged (toTagged r))) k
        (frame (frame (encList Enc.encode (uStrs r (stopIdx (decTagged (toTagged r))))) ++
          frame (encList Enc.encode r.2))).length) := by
  set K := stopIdx (decTagged (toTagged r)) with hKdef
  set rt := toTagged r with hrt
  set n := r.1.length with hn
  set Q := M 14 with hQ
  set S := encList Enc.encode (uStrs r K) with hS
  set X := encList Enc.encode r.2 with hX
  have hF : 200 ≤ Fr rt := by unfold Fr; omega
  have hL := Lr_eq rt
  have hnL := n_le_ecl rt
  have hKn := hM.j_le
  have hKF : 100 + 3 * (K + 1) ≤ Fr rt := by
    have : rt.1.length = n := rfl
    unfold Fr; omega
  have hQ0 : SA0 rt + n ≤ Q := hM.r14
  have hSA : Fr rt + Lr rt + 1 = SA0 rt := rfl
  obtain ⟨-, -, -, -, -, -, -, hEb⟩ := inp_layout hM.inp
  have hEl : (encList Enc.encode rt.2.1).length = eel rt := rfl
  have hX' : encList Enc.encode rt.2.1 = X := rfl
  rw [hX'] at hEb hEl
  have hEQ : Eblk rt + X.length + 1 ≤ Q := by
    unfold Eblk SA0 at *; omega
  unfold uOutP tUOut
  refine block_seq (runsTo_uHeadP (K := K) hM.one hM.r21 (by rw [hM.r54])) (fun M1 ⟨a19, a39, a44, a34,
    a35, a38, a36, a37, a46, a47, aK⟩ => ?_)
  rw [← hQ] at a19 a39 a44
  have g1 : ∀ z, 50 ≤ z → M1 z = M z := fun z hz => aK z (by simp; omega)
  have hrecs1 : ∀ i ≤ K, RecOK rt M1 (Fr rt) Q i := fun i hi =>
    (hM.recs i (by omega)).congr (fun c hc => g1 _ (by omega)) (fun z h1 h2 => g1 z (by omega))
  refine block_seq (runsTo_vLoop hr hk hrecs1 hF hKF a37 a46 a47 a36 a34 a35 a38
    (by rw [aK 1 (by simp), hM.one]) a44 (by omega)) (fun M2 ⟨b44, bS, bK⟩ => ?_)
  rw [← hS] at b44 bS bK
  have g2 : ∀ z, z ∉ Wv → z < Q + 2 → M2 z = M1 z := fun z hz h => bK z hz (Or.inl h)
  refine RunsTo.mono (T := (7 * X.length + 22) +
    (7 * (frame (frame S ++ frame X)).length + 8)) ?_ (by simp [RAM.frame]; omega)
  refine block_seq (runsTo_uTailP (E := Eblk rt) (S := S) (X := X)
    (by rw [g2 19 (by simp) (by omega), a19]) (by rw [g2 39 (by simp) (by omega), a39])
    (by rw [b44]) (by rw [g2 34 (by simp) (by omega), a34])
    (by rw [g2 1 (by simp) (by omega), aK 1 (by simp), hM.one])
    (by rw [g2 15 (by simp) (by omega), aK 15 (by simp), hM.r15])
    (hEb.congr (fun z h1 h2 => by
      simp only [RAM.frame, List.length_cons] at h2
      rw [g2 z (by simp; unfold Eblk at h1; omega) (by omega), g1 z (by unfold Eblk at h1; omega)]))
    hEQ (by unfold Eblk; omega) bS) (fun M3 ⟨c19, c44, cb⟩ => ?_)
  exact runsTo_moveP c19 c44 cb (by unfold SA0 at hQ0; omega)

/-! ## The output, as `untagOut` -/

/-- The strings of `X*` are those the program writes. -/
theorem untagOut_fst (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    (untagOut r).1 = uStrs r (stopIdx (decTagged (toTagged r))) := by
  unfold untagOut strStable
  rw [strStop_eq hr hk]
  apply List.ext_getElem (by simp [uStrs])
  intro i h1 h2
  rw [List.getElem_ofFn, strIter_eq hr hk, getElem_uStrs]
  simp only [uS, cntsPart]
  rw [List.getD_eq_getElem _ _ (by simpa [uStrs] using h2)]
  rfl

theorem encode_untagOut (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    Enc.encode (untagOut r) = frame (encList Enc.encode
      (uStrs r (stopIdx (decTagged (toTagged r))))) ++ frame (encList Enc.encode r.2) := by
  rw [encode_raw, untagOut_fst hr hk]; rfl

end TagLin

end Algo
