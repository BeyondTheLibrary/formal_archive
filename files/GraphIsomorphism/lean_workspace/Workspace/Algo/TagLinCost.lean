/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process, `O(n³) + |t₁|` plus the input
size, on the RAM.
-/
import Workspace.Algo.TagLinOut

/-!
# The corrected cost of §4.1.1, proved

`Algo.TagLin.tagProg` runs the tagged refinement process of §4.1.1 on a raw tagged digraph and
writes `X*` (`Algo.taggedOut`).  `Algo.TagLin.runsTo_tagProg` is its exact specification, with an
explicit step count; `Algo.TagLin.section_4_1_1_cost_corrected` bounds the count by
`C (n³ + |t₁| + size + 1)` and proves `Algo.Section_4_1_1_cost_corrected_statement`.

The bound is reached as follows.  A round sorts `n` strings of length `2N + 1 ≤ 2n + 1` by LCP
insertion sort (`O(n²)` steps) and computes the rows in `O(n² + m)` steps; there are at most `n`
rounds and `m ≤ n²`.  The output holds `k + 1 ≤ n` palettes; palette `i ≥ 1` has at most `n`
strings of length `2N_{i-1} + 1 ≤ 2n + 1`, and palette `0` is a sublist of the input colors.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact Babai Babai.TaggedDigraph

/-! ## The program -/

/-- The whole program: the bridge up, parsing, round `0`, the rounds, the output, the bridge
down. -/
def tagProg : Program :=
  seq Bridge.up (seq (seq setupP (seq parseP (seq ecntP ptrP))) (seq round0P (seq roundsP
    (seq outP Bridge.down))))

/-- The step count of `tagProg`. -/
noncomputable def tTag (r : RawTagged) : ℕ :=
  (18 * (Enc.encode r).length + 78) + ((20 * Lr r + 41) + ((tSort0 r + 15) +
    ((Kr r * (r.1.length + 1) + 1) + (tOut r + (7 * (Enc.encode (taggedOut r)).length + 34)))))

/-- **The specification of `tagProg`**: on a well-formed raw tagged digraph `r`, it outputs
`X*` within `tTag r` steps. -/
theorem runsTo_tagProg {r : RawTagged} (hr : r.WF) :
    RunsTo tagProg (fun m => m = initMem (Enc.encode r))
      (fun m => OutputAt m (Enc.encode (taggedOut r))) (tTag r) := by
  unfold tagProg tTag
  refine block_seq (Bridge.runsTo_up _) (fun M0 hM0 => ?_)
  subst hM0
  refine block_seq (runsTo_phaseA r) (fun M1 hP => ?_)
  refine block_seq (runsTo_round0 hP) (fun M2 hI => ?_)
  obtain ⟨t, ht, hR⟩ := runsTo_roundsP hr hI
  refine block_seq (hR.mono ht) (fun M3 hI3 => ?_)
  refine block_seq (runsTo_outP hI3) (fun M4 hb => ?_)
  obtain ⟨h16, hb'⟩ := Blk.frame_iff.1 hb
  refine (Bridge.runsTo_down h16).weaken (fun m ⟨h0, hi⟩ => ⟨h0, fun i hi' => ?_⟩)
  rw [hi (i + 1) (by omega) (by omega), show 16 + (i + 1) = 16 + 1 + i by ring,
    hb' i hi', List.getD_eq_getElem _ _ hi']

/-! ## The size of the output -/

theorem kS_le (r : RawTagged) : kS r ≤ r.1.length := by
  have := stopIdx_le (decTagged r)
  simp only [Fintype.card_fin] at this
  unfold kS; omega

theorem length_encList_strs (l : List (List ℕ)) :
    (encList Enc.encode l).length = (l.map (fun s => 2 * s.length + 1)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encList, List.length_append, RAM.frame, List.length_cons, List.map_cons,
      List.sum_cons, ih, ExplLinear.length_encode_nat_list]
    try ring

theorem tag0_c (r : RawTagged) (v : Fin r.1.length) : (tagIter (decTagged r) 0).c v = r.1[v] := by
  have := sX_zero r v.isLt
  simp only [sX, v.isLt, dif_pos] at this
  exact this

/-- Palette `0` is a list of distinct input colors: it is not longer than the input colors. -/
theorem length_E0_le (r : RawTagged) : (encList Enc.encode (PX r 0)).length ≤ ecl r := by
  unfold ecl
  rw [length_encList_strs, length_encList_strs]
  have hnd : (PX r 0).Nodup := oldColors_nodup _
  have hsub : PX r 0 ⊆ r.1 := fun s hs => by
    unfold PX at hs
    rw [mem_oldColors] at hs
    obtain ⟨v, rfl⟩ := hs
    rw [tag0_c]; exact List.getElem_mem _
  obtain ⟨l'', hperm, hsubl⟩ := hnd.subperm hsub
  calc ((PX r 0).map (fun s => 2 * s.length + 1)).sum
      = (l''.map (fun s => 2 * s.length + 1)).sum := ((hperm.map _).sum_eq).symm
    _ ≤ (r.1.map (fun s => 2 * s.length + 1)).sum :=
      (hsubl.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- Palette `i + 1` has at most `n` strings of length `2 N_i + 1 ≤ 2n + 1`. -/
theorem length_Esucc_le {r : RawTagged} (hr : r.WF) (i : ℕ) :
    (encList Enc.encode (PX r (i + 1))).length ≤ r.1.length * (4 * r.1.length + 3) := by
  rw [length_encList_strs]
  have hb : ∀ x ∈ (PX r (i + 1)).map (fun s => 2 * s.length + 1), x ≤ 4 * r.1.length + 3 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    unfold PX at hs
    rw [mem_oldColors] at hs
    obtain ⟨v, rfl⟩ := hs
    have e : (tagIter (decTagged r) (i + 1)).c v = sX r (i + 1) v := by
      simp only [sX, v.isLt, dif_pos]
    rw [e, sX_succ hr i v.isLt, length_rowStr]
    have := NX_le r i; omega
  have := List.sum_le_card_nsmul _ _ hb
  rw [List.length_map, smul_eq_mul] at this
  have h2 : (PX r (i + 1)).length ≤ r.1.length := by rw [← NX_eq_length]; exact NX_le r (i + 1)
  exact this.trans (Nat.mul_le_mul_right _ h2)

theorem length_palsOut_le {r : RawTagged} (hr : r.WF) :
    (encList Enc.encode (palsOut r)).length ≤
      ecl r + 1 + kS r * (r.1.length * (4 * r.1.length + 3) + 1) := by
  have key : ∀ j, (encList Enc.encode ((List.range (j + 1)).map (PX r))).length ≤
      ecl r + 1 + j * (r.1.length * (4 * r.1.length + 3) + 1) := by
    intro j
    induction j with
    | zero =>
      have := length_E0_le r
      change (frame (encList Enc.encode (PX r 0)) ++ []).length ≤ _
      simp only [RAM.frame, List.length_append, List.length_cons, List.length_nil]; omega
    | succ j ih =>
      rw [List.range_succ, List.map_append, Exact.encList_append, List.length_append]
      have := length_Esucc_le hr j
      have e : (encList Enc.encode ([j + 1].map (PX r))).length =
          (encList Enc.encode (PX r (j + 1))).length + 1 := by
        change (frame (encList Enc.encode (PX r (j + 1))) ++ []).length = _
        simp [RAM.frame]
      rw [e]
      nlinarith
  exact key (kS r)

theorem sum_palCost_le {r : RawTagged} (hr : r.WF) :
    ∑ j ∈ Finset.range (kS r + 1), palCost r (kS r - j) ≤
      7 * ecl r + 15 * r.1.length + 20 +
        kS r * (7 * (r.1.length * (4 * r.1.length + 3)) + 15 * r.1.length + 20) := by
  have e := Finset.sum_range_reflect (palCost r) (kS r + 1)
  simp only [Nat.add_sub_cancel] at e
  rw [e, Finset.sum_range_succ']
  have h0 : palCost r 0 ≤ 7 * ecl r + 15 * r.1.length + 20 := by
    unfold palCost; have := length_E0_le r; have := NX_le r 0; omega
  have hs : ∀ i ∈ Finset.range (kS r), palCost r (i + 1) ≤
      7 * (r.1.length * (4 * r.1.length + 3)) + 15 * r.1.length + 20 := fun i _ => by
    unfold palCost; have := length_Esucc_le hr i; have := NX_le r (i + 1); omega
  have := Finset.sum_le_card_nsmul _ _ _ hs
  rw [Finset.card_range, smul_eq_mul] at this
  omega

theorem length_out (r : RawTagged) :
    (Enc.encode (taggedOut r)).length =
      3 * r.1.length + eel r + etl r + (encList Enc.encode (palsOut r)).length + 4 := by
  rw [encode_taggedOut]
  simp only [RAM.frame, List.length_append, List.length_cons, length_encList_colsOut]
  unfold eel etl; omega

/-! ## The bound -/

/-- `tTag r ≤ C (n³ + L + 1)` with `L` the input length. -/
theorem tTag_le {r : RawTagged} (hr : r.WF) :
    tTag r ≤ 20000 * (r.1.length ^ 3 + (Enc.encode r).length + 1) := by
  set n := r.1.length with hn
  set k := kS r
  have hk : k ≤ n := kS_le r
  have hm : r.2.1.length ≤ n * n := edges_le_sq hr
  have hS := sum_sX_zero_le r
  have hPP := length_palsOut_le hr
  have hPC := sum_palCost_le hr
  have hout := length_out r
  have hL := Lr_eq r
  have hLl : Lr r = (Enc.encode r).length := rfl
  have hnL := n_le_ecl r
  have h1 : k * (n * (4 * n + 3) + 1) ≤ n * (n * (4 * n + 3) + 1) := Nat.mul_le_mul_right _ hk
  have h2 : k * (7 * (n * (4 * n + 3)) + 15 * n + 20) ≤
      n * (7 * (n * (4 * n + 3)) + 15 * n + 20) := Nat.mul_le_mul_right _ hk
  have h3 : r.2.1.length * (n + 1) ≤ n * n * (n + 1) := Nat.mul_le_mul_right _ hm
  have h4 : n * n ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · calc n * n = n * n * 1 := by ring
        _ ≤ n * n * n := Nat.mul_le_mul_left _ h
        _ = n ^ 3 := by ring
  have h5 : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · calc n = n * 1 := by ring
        _ ≤ n * n := Nat.mul_le_mul_left _ h
  unfold tTag tOut tSort0 Kr
  rw [hout]
  nlinarith

end TagLin

/-- **§4.1.1, the corrected bound `O(n³) + |t₁|` plus the input size, proved.**  The tagged
refinement process runs on the RAM in `O(n³ + size)` steps (`TagLin.tagProg`), which is within
the corrected bound. -/
theorem section_4_1_1_cost_corrected : Section_4_1_1_cost_corrected_statement := by
  refine ⟨TagLin.tagProg, 20000, fun r hr => ?_⟩
  obtain ⟨k, hk, hhalt, hout⟩ := (TagLin.runsTo_tagProg hr).spec _ rfl
  refine ⟨k, hk.trans ((TagLin.tTag_le hr).trans (Nat.mul_le_mul_left _ ?_)), hhalt, hout⟩
  have := RAM.length_lt_listSize (RAM.Enc.encode r)
  have : RAM.Enc.size r = RAM.listSize (RAM.Enc.encode r) := rfl
  omega


end Algo
