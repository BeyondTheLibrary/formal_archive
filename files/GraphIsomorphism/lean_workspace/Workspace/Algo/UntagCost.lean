/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1, line 2860: the cost `O(nk + n²m)` of the untagged naive refinement process,
proved on the RAM.
-/
import Workspace.Algo.UntagOut
import Workspace.Algo.TagLinCost

/-!
# §4.1.1, line 2860: the untagged process costs `O(nk + n²m)`

Lines 2852–2860: *"If each color in `X` is described by a string of length `k` over `Σ` then
colors in `X'` are described by strings of length `k + O(n)`. Therefore the description of each
color in `X_j` has length `k + O(jn)` and therefore in `X*`, the length is `k + O(n²)`. The cost
of round `j` is `O(m)` comparison of colors, where `m = |E|`, so the total cost of round `j` is
`O(jnm)`. The overall total cost is `O(nk + n²m)`."*

`Algo.Section_4_1_1_untagged_cost_statement` states the bound for the untagged process with
colors as strings (`Babai.ColoredDigraph.strStable`, `Algo.untagOut`), on the RAM, with the
input size `n` added (the output lists `n` strings, so `n` steps are needed even when
`k = m = 0`).  `Algo.section_4_1_1_untagged_cost` proves it.

The paper's derivation does not give the bound: the printed round costs `O(jnm)` sum to
`Θ(n³m)` over `j < n`.  The program `Algo.TagLin.uProg` follows a different route (see
the corrected paper, §4.1.1 untagged cost): it refines ranks, not strings (the rounds of the tagged
program, `Workspace/Algo/TagLinMain.lean`), stops after `k ≤ 2m` rounds
(`Algo.TagLin.stopIdx_le_two_mul`), and writes the strings of `X*` once, at the end
(`Workspace/Algo/UntagOut.lean`).  With no edge the process stops at once and the output is the
input.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact Babai Babai.TaggedDigraph Babai.ColoredDigraph

/-! ## The program -/

/-- With at least one edge: copy the input as a tagged digraph, parse, round `0`, the rounds,
the strings, the bridge down. -/
def mainP : Program :=
  seq usetupP (seq (seq parseP (seq ecntP ptrP)) (seq round0P (seq roundsP
    (seq uOutP Bridge.down))))

/-- **The untagged process on the RAM.** -/
def uProg : Program := seq Bridge.up (seq testP (ifz 3 mainP Bridge.down))

/-- The step count of `mainP`. -/
noncomputable def tMain (r : RawColored) (k : ℕ) : ℕ :=
  (7 * (ucl r + uel r) + 40) + ((17 + ((10 * r.2.length + 1) + (11 * ucl r + 2))) +
    ((tSort0 (toTagged r) + 15) + ((Kr (toTagged r) * (stopIdx (decTagged (toTagged r)) + 1) + 1) +
    (tUOut r.1.length (stopIdx (decTagged (toTagged r))) k
      ((Enc.encode (untagOut r)).length + 1) + (7 * (Enc.encode (untagOut r)).length + 34)))))

theorem runsTo_mainP {M : Mem} {r : RawColored} (hr : r.WF) {k : ℕ}
    (hk : ∀ s ∈ r.1, s.length = k) (hM : TState r M) :
    RunsTo mainP (fun m => m = M) (fun m => OutputAt m (Enc.encode (untagOut r))) (tMain r k) := by
  have hecl : ecl (toTagged r) = ucl r := rfl
  unfold mainP tMain
  refine block_seq (runsTo_usetupP hM) (fun M1 ⟨h1, hb⟩ => ?_)
  refine block_seq ((runsTo_phaseB h1 hb).mono (by rw [hecl]; rfl)) (fun M2 hP => ?_)
  refine block_seq (runsTo_round0 hP) (fun M3 hI => ?_)
  obtain ⟨t, ht, hR⟩ := runsTo_roundsP_stop hr.toTagged hI
  refine block_seq (hR.mono ht) (fun M4 hI4 => ?_)
  have hlen : (frame (frame (encList Enc.encode (uStrs r (stopIdx (decTagged (toTagged r))))) ++
      frame (encList Enc.encode r.2))).length = (Enc.encode (untagOut r)).length + 1 := by
    rw [encode_untagOut hr hk]; rfl
  refine block_seq ((runsTo_uOutP hr hk hI4).mono (by rw [hlen])) (fun M5 hb5 => ?_)
  rw [← encode_untagOut hr hk] at hb5
  obtain ⟨h16, hb'⟩ := Blk.frame_iff.1 hb5
  refine (Bridge.runsTo_down h16).weaken (fun m ⟨h0, hi⟩ => ⟨h0, fun i hi' => ?_⟩)
  rw [hi (i + 1) (by omega) (by omega), show 16 + (i + 1) = 16 + 1 + i by ring,
    hb' i hi', List.getD_eq_getElem _ _ hi']

theorem uStrs_zero (r : RawColored) : uStrs r 0 = r.1 := by
  apply List.ext_getElem (by simp [uStrs])
  intro i h1 h2
  rw [getElem_uStrs]
  simp [uS, cntsPart, List.getElem?_eq_getElem h2]

/-- With no edge, `X* = X`. -/
theorem untagOut_of_nil {r : RawColored} (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k)
    (h0 : r.2 = []) : untagOut r = r := by
  have hK : stopIdx (decTagged (toTagged r)) = 0 := by
    have := stopIdx_le_two_mul hr.toTagged
    simp only [toTagged, h0, List.length_nil] at this
    simp only [toTagged]; omega
  have h1 := untagOut_fst hr hk
  rw [hK, uStrs_zero] at h1
  have h2 : (untagOut r).2 = r.2 := rfl
  exact Prod.ext h1 h2

/-- A small input with an edge, to read off that `mainP` is well formed. -/
def r0 : RawColored := ([[], []], [(0, 1)])

theorem wf_mainP : Wf mainP := by
  have hr0 : r0.WF := by
    refine ⟨by simp [r0], fun e he => ?_⟩
    simp [r0] at he; subst he; simp [r0]
  have hk0 : ∀ s ∈ r0.1, s.length = 0 := by simp [r0]
  obtain ⟨_, _, _, hT⟩ := (runsTo_testP r0).spec _ rfl
  exact (runsTo_mainP hr0 hk0 hT).wf

/-- The step count of `uProg`. -/
noncomputable def tU (r : RawColored) (k : ℕ) : ℕ :=
  (18 * (Enc.encode r).length + 78) +
    (3 + ((if r.2 = [] then 7 * (Enc.encode r).length + 34 else tMain r k) + 2))

/-- **The specification of `uProg`**: on a well-formed raw colored digraph whose colors have
length `k`, it outputs `X*` (colors as strings) within `tU r k` steps. -/
theorem runsTo_uProg {r : RawColored} (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    RunsTo uProg (fun m => m = initMem (Enc.encode r))
      (fun m => OutputAt m (Enc.encode (untagOut r))) (tU r k) := by
  unfold uProg tU
  refine block_seq (Bridge.runsTo_up _) (fun M0 hM0 => ?_)
  subst hM0
  refine block_seq (runsTo_testP r) (fun M1 hT => ?_)
  rcases Nat.eq_zero_or_pos (uel r) with h0 | hpos
  · have hnil : r.2 = [] := by
      rw [uel_eq] at h0; exact List.eq_nil_of_length_eq_zero (by omega)
    rw [untagOut_of_nil hr hk hnil]
    refine ifz_eq' (by rw [hT.2.1, h0]) ?_ wf_mainP
    have h16 : M1 16 = (Enc.encode r).length := by
      rw [hT.2.2 16 (by omega) (by omega)]; exact initMemAt_blk _ 0 (by simp)
    refine ((Bridge.runsTo_down h16).mono (by simp [hnil])).weaken
      (fun m ⟨h0', hi⟩ => ⟨h0', fun i hi' => ?_⟩)
    rw [hi (i + 1) (by omega) (by omega), hT.2.2 _ (by omega) (by omega)]
    rw [initMemAt_blk _ (i + 1) (by simp; omega)]
    simp [List.getElem?_eq_getElem hi']
  · have hne : r.2 ≠ [] := by
      intro h; rw [uel_eq, h] at hpos; simp at hpos
    refine ifz_ne' (by rw [hT.2.1]; omega) ((runsTo_mainP hr hk hT).mono (by simp [hne]))
      Bridge.wf_down

/-! ## The size of the output -/

theorem ucl_eq {r : RawColored} {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    ucl r = r.1.length * (2 * k + 1) := by
  unfold ucl
  rw [length_encList_strs, List.map_congr_left (g := fun _ => 2 * k + 1)
    (fun s hs => by rw [hk s hs]), List.map_const', List.sum_replicate, smul_eq_mul]

theorem length_cntsPart_le (r : RawColored) (K x : ℕ) :
    (cntsPart r K x).length ≤ K * (4 * r.1.length + 1) := by
  induction K with
  | zero => simp [cntsPart]
  | succ K ih =>
    have e : cntsPart r (K + 1) x = cntsPart r K x ++ encCnt (cnts r K x) := by
      unfold cntsPart; rw [List.range_succ, List.flatMap_append]; simp
    rw [e, List.length_append, length_encCnt]
    have := length_cnts_le r K x
    nlinarith

theorem length_uS_le {r : RawColored} {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) (K : ℕ) {x : ℕ}
    (hx : x < r.1.length) : (uS r K x).length ≤ K + k + K * (4 * r.1.length + 1) := by
  unfold uS
  simp only [List.length_append, List.length_replicate]
  rw [List.getD_eq_getElem _ _ hx, hk _ (List.getElem_mem _)]
  have := length_cntsPart_le r K x
  omega

theorem length_encList_uStrs_le {r : RawColored} {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k)
    (K : ℕ) : (encList Enc.encode (uStrs r K)).length ≤
      r.1.length * (2 * (K + k + K * (4 * r.1.length + 1)) + 1) := by
  rw [length_encList_strs]
  have hb : ∀ y ∈ (uStrs r K).map (fun s => 2 * s.length + 1),
      y ≤ 2 * (K + k + K * (4 * r.1.length + 1)) + 1 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    have := length_uS_le hk K (List.mem_range.1 hx)
    omega
  have := List.sum_le_card_nsmul _ _ hb
  rwa [List.length_map, length_uStrs, smul_eq_mul] at this

theorem length_encode_untagOut_le {r : RawColored} (hr : r.WF) {k : ℕ}
    (hk : ∀ s ∈ r.1, s.length = k) :
    (Enc.encode (untagOut r)).length ≤ r.1.length * (2 * (stopIdx (decTagged (toTagged r)) + k +
      stopIdx (decTagged (toTagged r)) * (4 * r.1.length + 1)) + 1) + 5 * r.2.length + 2 := by
  rw [encode_untagOut hr hk]
  have h1 := length_encList_uStrs_le hk (stopIdx (decTagged (toTagged r)))
  have h2 : (encList Enc.encode r.2).length = 5 * r.2.length := uel_eq r
  simp only [RAM.frame, List.length_append, List.length_cons]
  omega

/-! ## The bound -/

/-- `tU r k ≤ C (nk + n²m + n + 1)`. -/
theorem tU_le {r : RawColored} (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    tU r k ≤ 100000 * (r.1.length * k + r.1.length ^ 2 * r.2.length + r.1.length + 1) := by
  set n := r.1.length with hn
  set m := r.2.length with hm
  have hL : (Enc.encode r).length = n * (2 * k + 1) + 5 * m + 2 := by
    rw [length_encode_raw, ucl_eq hk, uel_eq]
  unfold tU
  by_cases h0 : r.2 = []
  · rw [if_pos h0, hL]
    have : m = 0 := by rw [hm, h0]; rfl
    rw [this]
    nlinarith
  rw [if_neg h0]
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (List.eq_nil_of_length_eq_zero h) h0
    · exact h
  have hn1 : 1 ≤ n := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h0
    have := (hr.2 e he).1; omega
  have hmn : m ≤ n * n := edges_le_sq hr.toTagged
  set K := stopIdx (decTagged (toTagged r)) with hK
  have hKm : K ≤ 2 * m := stopIdx_le_two_mul hr.toTagged
  have hout := length_encode_untagOut_le hr hk
  rw [← hK] at hout
  have hS0 := sum_sX_zero_le (toTagged r)
  have hecl : ecl (toTagged r) = ucl r := rfl
  rw [hecl, ucl_eq hk] at hS0
  have hucl := ucl_eq hk
  have huel := uel_eq r
  unfold tMain tUOut vCost tSort0 Kr
  rw [← hK, hucl, huel]
  have hn' : (toTagged r).1.length = n := rfl
  have hm' : (toTagged r).2.1.length = m := rfl
  rw [hn', hm']
  rw [hn'] at hS0
  simp only [← hn, ← hm] at hout ⊢
  set O := (Enc.encode (untagOut r)).length
  set S0 := ∑ y ∈ Finset.range n, (sX (toTagged r) 0 y).length
  have a1 : n * K ≤ n * (2 * m) := Nat.mul_le_mul_left n hKm
  have a2 : n * n * K ≤ n * n * (2 * m) := Nat.mul_le_mul_left (n * n) hKm
  have a3 : m * K ≤ m * (2 * m) := Nat.mul_le_mul_left m hKm
  have a4 : m * m ≤ n * n * m := Nat.mul_le_mul_right m hmn
  have a5 : n * 1 * m ≤ n * n * m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left n hn1)
  have a6 : n * n * 1 ≤ n * n * m := Nat.mul_le_mul_left (n * n) hm1
  have a7 : 1 * m ≤ n * n * m := Nat.mul_le_mul_right m (Nat.mul_le_mul hn1 hn1)
  have hsq : n ^ 2 * m = n * n * m := by ring
  rw [hsq, hL]
  have hS0' : 2 * S0 ≤ n * (2 * k + 1) := hS0
  clear_value O S0 K n m
  clear hS0 hucl huel hecl hK hr hk h0 hL hn hm hn' hm'
  linarith

end TagLin

open RAM in
/-- **§4.1.1, line 2860: the untagged cost `O(nk + n²m)`**, with colors as strings over `Σ`
(`Babai.ColoredDigraph.strStable`) and the input size `n` added.  A program reads a raw colored
digraph whose colors have length `k` and writes `X*` within `C (nk + n²m + n + 1)` steps. -/
def Section_4_1_1_untagged_cost_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ (r : RawColored) (k : ℕ), r.WF → (∀ s ∈ r.1, s.length = k) →
    ∃ t ≤ C * (r.1.length * k + r.1.length ^ 2 * r.2.length + r.1.length + 1),
      Halted P (run P (Config.init (Enc.encode r)) t) ∧
        OutputAt (run P (Config.init (Enc.encode r)) t).mem (Enc.encode (untagOut r))

/-- **§4.1.1, line 2860, proved**: the untagged process runs on the RAM in
`O(nk + n²m + n)` steps (`TagLin.uProg`). -/
theorem section_4_1_1_untagged_cost : Section_4_1_1_untagged_cost_statement := by
  refine ⟨TagLin.uProg, 100000, fun r k hr hk => ?_⟩
  obtain ⟨t, ht, hhalt, hout⟩ := (TagLin.runsTo_uProg hr hk).spec _ rfl
  exact ⟨t, ht.trans (TagLin.tU_le hr hk), hhalt, hout⟩


end Algo
