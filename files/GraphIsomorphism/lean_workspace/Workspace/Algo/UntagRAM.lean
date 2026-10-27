/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1, line 2860: the cost `O(nk + n²m)` of the untagged naive refinement process.
The RAM program, part 1: the test `m = 0`, the setup, the rounds.
-/
import Workspace.Algo.UntagSem
import Workspace.Algo.TagLinOut

/-!
# The untagged process on the RAM: input and rounds

The program reads a raw colored digraph `r` (`Algo.RawColored`).  It first reads the length of
the edge encoding: if there is no edge, the output is the input (the process stops at once),
and the program only runs the bridge `down`.  Otherwise it copies the input to `F`, written as
the raw tagged digraph `toTagged r` (the empty tag appended), and runs the rounds of the tagged
program (`Workspace/Algo/TagLinMain.lean`): the ranks, not the strings, are refined.  The
strings of `X*` are written once, at the end (`Workspace/Algo/UntagOut.lean`).

* `runsTo_testP`: read the length `q` of the edge encoding.
* `runsTo_usetupP`: copy the input to `F`, as `toTagged r`.
* `runsTo_phaseB`: the parsing of the tagged program, after the copy.
* `runsTo_roundsP_stop`: the rounds cost at most `Kr (k + 1) + 1` steps, `k` the stopping round
  (the tagged program's bound used `n` in place of `k`).

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact Babai Babai.TaggedDigraph

/-! ## The input -/

/-- The length of the encoding of the colors. -/
def ucl (r : RawColored) : ℕ := (encList Enc.encode r.1).length

/-- The length of the encoding of the edges. -/
def uel (r : RawColored) : ℕ := (encList Enc.encode r.2).length

theorem encode_raw (r : RawColored) :
    Enc.encode r = frame (encList Enc.encode r.1) ++ frame (encList Enc.encode r.2) := rfl

theorem encode_toTagged (r : RawColored) :
    Enc.encode (toTagged r) = frame (encList Enc.encode r.1) ++
      frame (frame (encList Enc.encode r.2) ++ [0]) := rfl

theorem length_encode_raw (r : RawColored) : (Enc.encode r).length = ucl r + uel r + 2 := by
  rw [encode_raw]; simp [RAM.frame, ucl, uel]; ring

theorem Lr_toTagged (r : RawColored) : Lr (toTagged r) = (Enc.encode r).length + 2 := by
  unfold Lr; rw [encode_toTagged, length_encode_raw]; simp [RAM.frame, ucl, uel]; ring

theorem uel_eq (r : RawColored) : uel r = 5 * r.2.length := length_encList_edges _

theorem initMemAt_blk (l : List ℕ) : Blk (initMemAt 16 l) 16 (l.length :: l) := by
  intro j hj
  rw [initMemAt_of_ge _ (by omega)]
  rcases j with _ | j
  · simp [initMem]
  · simp only [initMem, show 16 + (j + 1) - 16 = j + 1 by omega, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, List.getElem_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simp at hj; omega)]

theorem initMemAt_high (l : List ℕ) {z : ℕ} (h : 17 + l.length ≤ z) : initMemAt 16 l z = 0 := by
  rw [initMemAt_of_ge _ (by omega)]
  simp only [initMem, show z - 16 ≠ 0 by omega, if_false]
  rw [List.getD_eq_default _ _ (by omega)]

theorem initMemAt_low (l : List ℕ) {z : ℕ} (h : z < 16) : initMemAt 16 l z = 0 :=
  initMemAt_of_lt _ h

theorem blk_input (r : RawColored) :
    Blk (initMemAt 16 (Enc.encode r)) 17 (frame (encList Enc.encode r.1) ++
      frame (encList Enc.encode r.2)) := by
  have := (initMemAt_blk (Enc.encode r))
  rw [Blk.cons] at this
  exact this.2

/-! ## The test `m = 0` -/

/-- Read the length `q` of the edge encoding into register `3`. -/
def testP : Program := seq (assign 2 18) (seq (addTo 2 2 17) (loadTo 3 2))

theorem wf_testP : Wf testP := by unfold testP; wf_tac

/-- After the test: the input memory with `18 + p` in `2` and `q` in `3`. -/
def TState (r : RawColored) (m : Mem) : Prop :=
  m 2 = 18 + ucl r ∧ m 3 = uel r ∧
    ∀ z, z ≠ 2 → z ≠ 3 → m z = initMemAt 16 (Enc.encode r) z

theorem runsTo_testP (r : RawColored) :
    RunsTo testP (fun m => m = initMemAt 16 (Enc.encode r)) (TState r) 3 := by
  have hb := blk_input r
  rw [Blk.append, Blk.frame_iff, Blk.frame_iff] at hb
  obtain ⟨⟨h17, -⟩, h18, -⟩ := hb
  unfold testP
  refine assign_seq' (add_seq' (load_last' (T := 0) ?_))
  refine ⟨?_, ?_, fun z h2 h3 => ?_⟩
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [h17]; rfl
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [h17]
    simp only [RAM.frame, List.length_cons] at h18
    rw [show 18 + (encList Enc.encode r.1).length = 17 + ((encList Enc.encode r.1).length + 1) by
      ring, h18]; rfl
  · simp (disch := omega) only [Mem.update_of_ne]

/-! ## The setup: the input at `F`, as a raw tagged digraph -/

/-- The registers of the first copy, and the length cell `L + 2` at `F`. -/
def uPart1 : Program :=
  seq (copyTo 4 16) (seq (addTo 4 4 16) (seq (addTo 4 4 16) (seq (assign 5 206) (seq (addTo 4 4 5)
  (seq (copyTo 5 16) (seq (assign 6 2) (seq (addTo 5 5 6) (seq (storeTo 4 5)
  (seq (assign 0 17) (seq (assign 1 1) (seq (addTo 5 4 1) (seq (copyTo 6 17) (addTo 6 6 1)))))))))))))

/-- The cells `q + 2`, `q` after the colors, and the registers of the second copy. -/
def uPart2 : Program :=
  seq (addTo 5 5 6) (seq (addTo 7 3 1) (seq (addTo 7 7 1) (seq (storeTo 5 7) (seq (addTo 5 5 1)
  (seq (storeTo 5 3) (seq (addTo 5 5 1) (addTo 0 2 1)))))))

/-- Copy the input to `F = 3 (L + 2) + 200` as `toTagged r`: the length `L + 2`, the colors, the
edges framed with the empty tag. -/
def usetupP : Program :=
  seq uPart1 (seq (Arrays.copyBlock 0 5 6 8) (seq uPart2 (seq (Arrays.copyBlock 0 5 3 8)
    (copyTo 1 4))))

theorem wf_usetupP : Wf usetupP := by
  unfold usetupP uPart1 uPart2 Arrays.copyBlock Arrays.copyPre Arrays.copyBody; wf_tac

theorem runsTo_uPart1 {M : Mem} {L p : ℕ} (i16 : M 16 = L) (i17 : M 17 = p) :
    RunsTo uPart1 (fun m => m = M) (fun m => m 0 = 17 ∧ m 1 = 1 ∧ m 4 = 3 * L + 206 ∧
      m 5 = 3 * L + 206 + 1 ∧ m 6 = p + 1 ∧ m (3 * L + 206) = L + 2 ∧
      ∀ z, (z = 2 ∨ z = 3 ∨ 8 ≤ z) → z ≠ 3 * L + 206 → m z = M z) 14 := by
  unfold uPart1
  refine copy_seq (add_seq (add_seq (assign_seq (add_seq (copy_seq (assign_seq (add_seq
    (store_seq (assign_seq (assign_seq (add_seq (copy_seq (add_last ?_)))))))))))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, i16, i17,
    show L + L + L + 206 = 3 * L + 206 by ring]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun z hz hF => ?_⟩
  simp (disch := omega) only [Mem.update_of_ne]

theorem runsTo_uPart2 {M : Mem} {p q G : ℕ} (i1 : M 1 = 1) (i2 : M 2 = 18 + p) (i3 : M 3 = q)
    (h56 : M 5 + M 6 = G) (hG : 8 ≤ G) :
    RunsTo uPart2 (fun m => m = M) (fun m => m 0 = 19 + p ∧ m 3 = q ∧ m 5 = G + 2 ∧
      m G = q + 2 ∧ m (G + 1) = q ∧
      ∀ z, z ≠ 0 → z ≠ 5 → z ≠ 7 → z ≠ G → z ≠ G + 1 → m z = M z) 8 := by
  unfold uPart2
  refine add_seq (add_seq (add_seq (store_seq (add_seq (store_seq (add_seq (add_last ?_)))))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, i1, i2, i3, h56]
  refine ⟨by ring, trivial, trivial, trivial, trivial, fun z h0 h5 h7 hG1 hG2 => ?_⟩
  simp (disch := omega) only [Mem.update_of_ne]

theorem inputA (r : RawColored) (j : ℕ) (hj : j < (encList Enc.encode r.1).length) :
    initMemAt 16 (Enc.encode r) (17 + 1 + j) = (encList Enc.encode r.1)[j] := by
  have hb := blk_input r
  rw [Blk.append, Blk.frame_iff] at hb
  exact hb.1.2 j hj

theorem inputB (r : RawColored) (j : ℕ) (hj : j < (encList Enc.encode r.2).length) :
    initMemAt 16 (Enc.encode r) (ucl r + 4 + 15 + j) = (encList Enc.encode r.2)[j] := by
  have hb := blk_input r
  rw [Blk.append, Blk.frame_iff, Blk.frame_iff] at hb
  have := hb.2.2 j hj
  simp only [RAM.frame, List.length_cons] at this
  rw [show 17 + ((encList Enc.encode r.1).length + 1) + 1 + j = ucl r + 4 + 15 + j by
    unfold ucl; ring] at this
  exact this


/-- **The setup**: the input at `F`, as `toTagged r`. -/
theorem runsTo_usetupP {M : Mem} {r : RawColored} (hM : TState r M) :
    RunsTo usetupP (fun m => m = M) (fun m => m 1 = Fr (toTagged r) ∧
      Blk m (Fr (toTagged r)) (Lr (toTagged r) :: Enc.encode (toTagged r)))
      (7 * (ucl r + uel r) + 40) := by
  obtain ⟨e2, e3, hI⟩ := hM
  have hLpq : (Enc.encode r).length = ucl r + uel r + 2 := length_encode_raw r
  have i16 : M 16 = (Enc.encode r).length := by
    rw [hI 16 (by decide) (by decide)]; exact (initMemAt_blk _ 0 (by simp))
  have i17 : M 17 = ucl r := by
    rw [hI 17 (by decide) (by decide)]
    exact (initMemAt_blk _ 1 (by rw [List.length_cons, hLpq]; omega))
  have hF : Fr (toTagged r) = 3 * (Enc.encode r).length + 206 := by
    unfold Fr; rw [Lr_toTagged]; ring
  -- the cells of the input
  have hA : ∀ j (hj : j < (encList Enc.encode r.1).length), M (17 + 1 + j) = (encList Enc.encode r.1)[j]'hj :=
    fun j hj => by rw [hI _ (by omega) (by omega)]; exact inputA r j hj
  have hB : ∀ j (hj : j < (encList Enc.encode r.2).length), M (ucl r + 4 + 15 + j) = (encList Enc.encode r.2)[j]'hj :=
    fun j hj => by rw [hI _ (by omega) (by omega)]; exact inputB r j hj
  have hHi : ∀ z, 17 + (Enc.encode r).length ≤ z → M z = 0 := fun z hz => by
    rw [hI _ (by omega) (by omega)]; exact initMemAt_high _ hz
  rw [encode_toTagged, Lr_toTagged, hF]
  have hpA : (encList Enc.encode r.1).length = ucl r := rfl
  have hqB : (encList Enc.encode r.2).length = uel r := rfl
  generalize encList Enc.encode r.1 = A at hA hpA ⊢
  generalize encList Enc.encode r.2 = B at hB hqB ⊢
  generalize (Enc.encode r).length = L at hLpq i16 hHi ⊢
  generalize ucl r = p at hLpq i17 e2 hA hB hpA ⊢
  generalize uel r = q at hLpq e3 hB hqB ⊢
  clear hI
  unfold usetupP
  refine RunsTo.mono (T := 14 + ((7 * (p + 1) + 5) + (8 + ((7 * q + 5) + 1)))) ?_ (by omega)
  refine block_seq (runsTo_uPart1 i16 i17) (fun M1 ⟨f0, f1, f4, f5, f6, fF, fz⟩ => ?_)
  refine block_seq ((Arrays.runsTo_copyBlock 0 5 6 8 (by decide) (by decide) (by decide) M1
    (by omega) (by omega) (Or.inr (by rw [f0, f6, f5]; omega))).mono (by rw [f6]))
    (fun M2 ⟨hc2, hk2⟩ => ?_)
  rw [f5, f6, f0] at hc2
  rw [f5, f6] at hk2
  have g : ∀ z, z < 8 ∨ 13 ≤ z → ¬ (3 * L + 206 + 1 ≤ z ∧ z < 3 * L + 206 + 1 + (p + 1)) →
      M2 z = M1 z := fun z h1 h2 => hk2 z h2 (by simp; omega)
  refine block_seq (runsTo_uPart2 (p := p) (q := q) (G := 3 * L + 206 + p + 2)
    (by rw [g 1 (by omega) (by omega), f1]) (by rw [g 2 (by omega) (by omega), fz 2 (by omega) (by omega), e2])
    (by rw [g 3 (by omega) (by omega), fz 3 (by omega) (by omega), e3])
    (by rw [g 5 (by omega) (by omega), g 6 (by omega) (by omega), f5, f6]; ring) (by omega))
    (fun M3 ⟨k0, k3, k5, kq2, kq, kz⟩ => ?_)
  refine block_seq ((Arrays.runsTo_copyBlock 0 5 3 8 (by decide) (by decide) (by decide) M3
    (by omega) (by omega) (Or.inr (by rw [k0, k3, k5]; omega))).mono (by rw [k3]))
    (fun M4 ⟨hc4, hk4⟩ => ?_)
  rw [k5, k3, k0] at hc4
  rw [k5, k3] at hk4
  have h4 : ∀ z, 13 ≤ z → ¬ (3 * L + 206 + p + 2 + 2 ≤ z ∧ z < 3 * L + 206 + p + 2 + 2 + q) →
      M4 z = M3 z := fun z h1 h2 => hk4 z h2 (by simp; omega)
  -- the cells below `F`, and at `F`, as in `M` or `M1`
  have low : ∀ z, 13 ≤ z → z < 3 * L + 206 → M4 z = M z := fun z h1 h2 => by
    rw [h4 z h1 (by omega), kz z (by omega) (by omega) (by omega) (by omega) (by omega),
      g z (by omega) (by omega), fz z (by omega) (by omega)]
  refine copy_last ⟨?_, ?_⟩
  · rw [Mem.update_self, hk4 4 (by omega) (by simp), kz 4 (by omega) (by omega) (by omega)
      (by omega) (by omega), g 4 (by omega) (by omega), f4]
  have hbF : ∀ z, 13 ≤ z → (M4.update 1 (M4 4)) z = M4 z := fun z hz =>
    Mem.update_of_ne _ _ (by omega)
  rw [Blk.cons]
  refine ⟨?_, ?_⟩
  · rw [hbF _ (by omega), h4 _ (by omega) (by omega),
      kz _ (by omega) (by omega) (by omega) (by omega) (by omega), g _ (by omega) (by omega), fF]
  rw [Blk.append, Blk.frame_iff, Blk.frame_iff, Blk.append, Blk.frame_iff]
  simp only [RAM.frame, List.length_cons, List.length_append]
  rw [hpA, hqB]
  refine ⟨⟨?_, fun j hj => ?_⟩, ?_, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_⟩
  · rw [hbF _ (by omega), h4 _ (by omega) (by omega),
      kz _ (by omega) (by omega) (by omega) (by omega) (by omega),
      show 3 * L + 206 + 1 = 3 * L + 206 + 1 + 0 by ring, hc2 0 (by omega),
      fz _ (by omega) (by omega), i17]
  · rw [hbF _ (by omega), h4 _ (by omega) (by omega),
      kz _ (by omega) (by omega) (by omega) (by omega) (by omega),
      show 3 * L + 206 + 1 + 1 + j = 3 * L + 206 + 1 + (j + 1) by ring, hc2 (j + 1) (by omega),
      fz _ (by omega) (by omega), show 17 + (j + 1) = 17 + 1 + j by ring]
    exact hA j (by omega)
  · rw [hbF _ (by omega), h4 _ (by omega) (by omega),
      show 3 * L + 206 + 1 + (p + 1) = 3 * L + 206 + p + 2 by ring, kq2]
    simp
  · rw [hbF _ (by omega), h4 _ (by omega) (by omega),
      show 3 * L + 206 + 1 + (p + 1) + 1 = 3 * L + 206 + p + 2 + 1 by ring, kq]
  · rw [hbF _ (by omega),
      show 3 * L + 206 + 1 + (p + 1) + 1 + 1 + j = 3 * L + 206 + p + 2 + 2 + j by ring,
      hc4 j (by omega), kz _ (by omega) (by omega) (by omega) (by omega) (by omega),
      g _ (by omega) (by omega), fz _ (by omega) (by omega),
      show 19 + p + j = p + 4 + 15 + j by ring]
    exact hB j (by omega)
  · obtain rfl : j = 0 := by simpa using hj
    rw [hbF _ (by omega),
      show 3 * L + 206 + 1 + (p + 1) + 1 + (q + 1) + 0 = 3 * L + 206 + p + 2 + 2 + q by ring,
      h4 _ (by omega) (by omega), kz _ (by omega) (by omega) (by omega) (by omega) (by omega),
      g _ (by omega) (by omega), fz _ (by omega) (by omega), hHi _ (by omega)]
    rfl

/-- The tagged program's phase A after its copy (`runsTo_phaseA`): parse, count the edges, the
addresses of the colors. -/
theorem runsTo_phaseB {M1 : Mem} {r : RawTagged} (h1 : M1 1 = Fr r)
    (hb : Blk M1 (Fr r) (Lr r :: Enc.encode r)) :
    RunsTo (seq parseP (seq ecntP ptrP)) (fun m => m = M1) (PState r)
      (17 + ((10 * r.2.1.length + 1) + (11 * ecl r + 2))) := by
  have he := eel_eq r
  refine block_seq (runsTo_parseP h1 hb) (fun M2 ⟨o2, f1, f4, f15, f17, f18, f20, f21, f30, f31,
    f42, f43⟩ => ?_)
  have hb2 : Blk M2 (Fr r) (Lr r :: Enc.encode r) :=
    ExplLinear.Blk.outside hb o2 (by intro z hz; simp at hz; unfold Fr; omega)
  refine block_seq (runsTo_ecntP (k := r.2.1.length) f1 (by rw [f4, he]) f43)
    (fun M3 ⟨o3, g43⟩ => ?_)
  have k3 : ∀ z, z ∉ [4, 43] → M3 z = M2 z := o3
  have hb3 : Blk M3 (Fr r) (Lr r :: Enc.encode r) :=
    ExplLinear.Blk.outside hb2 o3 (by intro z hz; simp at hz; unfold Fr; omega)
  refine (runsTo_ptrP (by rw [k3 1 (by simp), f1]) hb3 (by rw [k3 20 (by simp), f20])
    (by rw [k3 21 (by simp), f21]) (by rw [k3 30 (by simp), f30])
    (by rw [k3 31 (by simp), f31])).weaken (fun m ⟨hk, e21, hsa⟩ => ?_)
  have hS : Fr r + Lr r + 1 = SA0 r := rfl
  have hS2 : 200 ≤ SA0 r := by unfold SA0 Fr; omega
  have hLl : Lr r = (Enc.encode r).length := rfl
  have k4 : ∀ z, z ∉ [2, 21, 30, 32, 33] → z < SA0 r → m z = M3 z :=
    fun z hz hr => hk z hz (Or.inl hr)
  refine ⟨by rw [k4 1 (by simp) (by omega), k3 1 (by simp), f1],
    hb3.congr (fun z hz1 hz2 => k4 z (by simp; have : 200 ≤ Fr r := (by unfold Fr; omega); omega)
      (by simp at hz2; omega)),
    by rw [k4 15 (by simp) (by omega), k3 15 (by simp), f15],
    by rw [k4 17 (by simp) (by omega), k3 17 (by simp), f17],
    by rw [k4 18 (by simp) (by omega), k3 18 (by simp), f18],
    by rw [k4 20 (by simp) (by omega), k3 20 (by simp), f20], e21,
    by rw [k4 42 (by simp) (by omega), k3 42 (by simp), f42],
    by rw [k4 43 (by simp) (by omega), g43], hsa⟩

/-- **The rounds, with early stopping**: `Kr (k + 1) + 1` steps, `k` the stopping round. The
tagged program's bound (`runsTo_roundsP`) used `n ≥ k` in place of `k`. -/
theorem runsTo_roundsP_stop {M : Mem} {r : RawTagged} (hr : r.WF) (hM : MInv r 0 M) :
    ∃ t ≤ Kr r * (Babai.TaggedDigraph.stopIdx (decTagged r) + 1) + 1,
      RunsTo roundsP (fun m => m = M)
        (fun m => MInv r (Babai.TaggedDigraph.stopIdx (decTagged r) + 1) m) t := by
  set K := Babai.TaggedDigraph.stopIdx (decTagged r) with hK
  have hKs : NX r (K + 1) = NX r K := Babai.TaggedDigraph.stopIdx_spec _
  have hloop := runsTo_whileNz_amortX (i := 55) wf_roundP (fun m => ∃ j, MInv r j m ∧ j ≤ K + 1)
    (fun m => Kr r * (K + 2 - m 54)) (fun M' ⟨j, hj, _⟩ hf => by
      have hjK : j ≤ K := by
        by_contra hc
        rcases Nat.lt_or_ge (K + 1) j with h | h
        · exact hj.nostop K h hKs
        · obtain rfl : j = K + 1 := by omega
          exact hf (hj.flag.2 ⟨by omega, by simp only [Nat.add_sub_cancel]; exact hKs⟩)
      refine ⟨tRound r j, (runsTo_roundP hr hj hf).weaken (fun m hm => ⟨⟨j + 1, hm, by omega⟩, ?_⟩)⟩
      have := tRound_le hr j
      simp only
      rw [hm.r54, hj.r54]
      have e : K + 2 - (j + 1) = (K + 2 - (j + 1 + 1)) + 1 := by omega
      rw [e, Nat.mul_add, Nat.mul_one]
      omega) M ⟨0, hM, by omega⟩
  obtain ⟨t, ht⟩ := hloop
  obtain ⟨mf, ⟨⟨j, hj, -⟩, h55, hΦ⟩, hrun⟩ := ht.exact
  have ⟨hj0, hjs⟩ := hj.flag.1 h55
  have hstop : K = j - 1 := by
    refine stopIdx_eq_of r (by rw [Nat.sub_add_cancel hj0]; exact hjs) (fun i hi => ?_)
    exact hj.nostop i (by omega)
  refine ⟨t, ?_, hrun.weaken (fun m hm => ?_)⟩
  · have := hM.r54
    simp only at hΦ
    rw [this] at hΦ
    have e : K + 2 - (0 + 1) = K + 1 := by omega
    rw [e] at hΦ
    omega
  · rw [hm, hstop, Nat.sub_add_cancel hj0]; exact hj

end TagLin

end Algo
