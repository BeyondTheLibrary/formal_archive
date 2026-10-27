/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  The output phase: write
`X* = (V, E, c*, t*)` after the rounds.
-/
import Workspace.Algo.TagLinMain

/-!
# Writing the output of the tagged refinement process

After the rounds (`Algo.TagLin.runsTo_roundsP`), the output `X*` is written in a buffer at the
free address `Q`: the final colors `[st(c_k)(v)]`, the edges (copied from the input), the tag
`t* = t ++ (P_0, …, P_k)`: the input tag (copied) and the palettes `P_i`, read off the records
of the rounds.  The buffer is then moved to `16` and the bridge `down` puts it in the output
convention.

Registers: `19` the buffer `Q`, `44` the write pointer, `45` the ranks, `47`, `48` the length
cells of the edge-and-tag part and of the tag, `49` the next record, `10` the length cell of the
current palette, `11`, `12` the record's string addresses and sorted list, `26`, `28`, `29`
counters.  The block copies use the scratch registers `59–63`.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact Babai Babai.TaggedDigraph

/-! ## Loops with a potential, bounded -/

theorem RunsTo.bound_of_post {P : Program} {M : Mem} {post : Mem → Prop} {t B : ℕ}
    (h : RunsTo P (fun m => m = M) (fun m => post m ∧ t ≤ B) t) :
    RunsTo P (fun m => m = M) post B := by
  obtain ⟨M', ⟨hp, htB⟩, hrun⟩ := h.exact
  exact (hrun.mono htB).weaken (fun m hm => by subst hm; exact hp)

/-- `runsTo_whileNz_amortX` with the time bound `Φ M + 1`. -/
theorem runsTo_whileNz_amort' {i : ℕ} {P : Program} (hw : Wf P) (inv : Mem → Prop)
    (Φ : Mem → ℕ)
    (hP : ∀ M, inv M → M i ≠ 0 → ∃ t, RunsTo P (fun m => m = M)
      (fun m' => inv m' ∧ Φ m' + t + 2 ≤ Φ M) t) (M : Mem) (hM : inv M) :
    RunsTo (whileNz i P) (fun m => m = M) (fun m' => inv m' ∧ m' i = 0) (Φ M + 1) := by
  obtain ⟨t, h⟩ := runsTo_whileNz_amortX hw inv Φ hP M hM
  exact RunsTo.bound_of_post (h.weaken (fun m ⟨a, b, c⟩ => ⟨⟨a, b⟩, by omega⟩))

/-! ## The output -/

/-- The stopping round `k`. -/
noncomputable def kS (r : RawTagged) : ℕ := stopIdx (decTagged r)

/-- The final colors `[st(c_k)(v)]`. -/
noncomputable def colsOut (r : RawTagged) : List (List ℕ) :=
  (List.range r.1.length).map (fun v => [rX r (kS r) v])

/-- The palettes `P_0, …, P_k`. -/
noncomputable def palsOut (r : RawTagged) : List (List (List ℕ)) :=
  (List.range (kS r + 1)).map (PX r)

theorem encode_taggedOut (r : RawTagged) :
    Enc.encode (taggedOut r) = frame (encList Enc.encode (colsOut r)) ++
      frame (frame (encList Enc.encode r.2.1) ++
        frame (encList Enc.encode r.2.2 ++ encList Enc.encode (palsOut r))) := by
  rw [taggedOut_eq]
  show frame (encList Enc.encode ((List.range r.1.length).map _)) ++
    frame (frame (encList Enc.encode r.2.1) ++ frame (encList Enc.encode (r.2.2 ++ _))) = _
  rw [Exact.encList_append]; rfl

theorem length_colsOut (r : RawTagged) : (colsOut r).length = r.1.length := by
  simp [colsOut]

theorem getElem_colsOut (r : RawTagged) {c : ℕ} (hc : c < (colsOut r).length) :
    (colsOut r)[c] = [rX r (kS r) c] := by
  simp [colsOut]

theorem length_encList_singles (l : List (List ℕ)) (h : ∀ s ∈ l, s.length = 1) :
    (encList Enc.encode l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encList, List.length_append, List.length_cons]
    rw [ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    have ha := h a List.mem_cons_self
    have : (Enc.encode a).length = 2 * a.length := ExplLinear.length_encode_nat_list a
    simp only [RAM.frame, List.length_cons]; omega

theorem length_encList_colsOut (r : RawTagged) :
    (encList Enc.encode (colsOut r)).length = 3 * r.1.length := by
  have key : ∀ l : List ℕ, (encList Enc.encode (l.map (fun v => [rX r (kS r) v]))).length =
      3 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, encList, List.length_append] at ih ⊢
      rw [ih]; simp only [RAM.frame, List.length_cons]
      have : (Enc.encode [rX r (kS r) a]).length = 2 := rfl
      omega
  rw [colsOut, key, List.length_range]

/-! ## Copy a block to the write pointer -/

/-- Copy `m ln` cells from `m src` to the write pointer `44`, and advance it. -/
def cpAdv (src ln : ℕ) : Program := seq (Arrays.copyBlock src 44 ln 59) (addTo 44 44 ln)

theorem wf_copyBlock (src dst n s : ℕ) : Wf (Arrays.copyBlock src dst n s) := by
  unfold Arrays.copyBlock Arrays.copyPre Arrays.copyBody; wf_tac

theorem wf_cpAdv (src ln : ℕ) : Wf (cpAdv src ln) := by
  unfold cpAdv; exact wf_seq (wf_copyBlock _ _ _ _) (Layout.wf_addTo _ _ _)

/-- **Copy and advance**: `7 |xs| + 6` steps. -/
theorem runsTo_cpAdv {M : Mem} {src ln : ℕ} {xs : List ℕ} (hs : src < 59) (hl : ln < 59)
    (h1 : 64 ≤ M src) (h2 : 64 ≤ M 44) (hd : M src + M ln ≤ M 44)
    (hx : Blk M (M src) xs) (hlen : M ln = xs.length) :
    RunsTo (cpAdv src ln) (fun m => m = M) (fun m => Blk m (M 44) xs ∧
      Keep [44, 59, 60, 61, 62, 63] (M 44) (M 44 + xs.length) M m ∧
      m 44 = M 44 + xs.length) (7 * xs.length + 6) := by
  unfold cpAdv
  refine RunsTo.mono (T := (7 * M ln + 5) + (0 + 1)) ?_ (by rw [hlen])
  refine block_seq (Arrays.runsTo_copyBlock src 44 ln 59 hs (by omega) hl M (by omega)
    (by omega) (Or.inr hd)) (fun M1 ⟨hc, hk⟩ => add_last' ?_)
  have e44 : M1 44 = M 44 := hk 44 (by omega) (by simp)
  have eln : M1 ln = M ln := hk ln (by omega) (by simp; omega)
  rw [e44, eln, hlen]
  refine ⟨fun j hj => ?_, fun z hz hab => ?_, by rw [Mem.update_self]⟩
  · rw [Mem.update_of_ne _ _ (by omega), hc j (by omega)]
    exact hx j hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1]
    exact hk z (by omega) (by simp; omega)

/-! ## The final colors -/

/-- Start the buffer at `Q = m 14`: the length cell `3n` of the colors; the ranks of round `k`
(record `m 50 - 5 = 100 + 3k + 1`, plus `4n`) in `45`. -/
def headP : Program :=
  seq (copyTo 19 14) (seq (addTo 44 19 1) (seq (addTo 2 21 21) (seq (addTo 2 2 21)
    (seq (storeTo 44 2) (seq (addTo 44 44 1) (seq (assign 2 5) (seq (subTo 2 50 2)
    (seq (loadTo 45 2) (seq (addTo 45 45 21) (seq (addTo 45 45 21) (seq (addTo 45 45 21)
    (seq (addTo 45 45 21) (seq (assign 3 2) (copyTo 29 21))))))))))))))

/-- One final color `[2, 1, st(c_k)(v)]`. -/
def colBody : Program :=
  seq (storeTo 44 3) (seq (addTo 44 44 1) (seq (storeTo 44 1) (seq (addTo 44 44 1)
    (seq (loadTo 2 45) (seq (storeTo 44 2) (seq (addTo 44 44 1) (seq (addTo 45 45 1)
    (subTo 29 29 1))))))))

def colP : Program := seq headP (whileNz 29 colBody)

theorem wf_colBody : Wf colBody := by unfold colBody; wf_tac

/-- The final colors, in `11 n + 16` steps. -/
theorem runsTo_colP {M : Mem} {r : RawTagged} (hM : MInv r (kS r + 1) M) :
    RunsTo colP (fun m => m = M) (fun m => m 19 = M 14 ∧ m 1 = 1 ∧
      m 44 = M 14 + 2 + 3 * r.1.length ∧
      Blk m (M 14 + 1) (frame (encList Enc.encode (colsOut r))) ∧
      Keep [2, 3, 19, 29, 44, 45] (M 14) (M 14 + 2 + 3 * r.1.length) M m)
      (15 + (11 * r.1.length + 1)) := by
  set n := r.1.length with hn
  set k := kS r
  set Q := M 14 with hQ
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hQ0 : SA0 r + n ≤ Q := hM.r14
  have hQ200 : 200 ≤ Q := by unfold SA0 at hQ0; omega
  have hRk := hM.recs k (by omega)
  set R := M (100 + 3 * k + 1) + 4 * n with hR
  have hRQ : R + n ≤ Q := by have := hRk.hiA; omega
  have hR64 : 64 ≤ R := by have := hRk.loA; omega
  have hrk : ∀ x < n, M (R + x) = rX r k x := fun x hx => hRk.rank x hx
  have e50 : M 50 - 5 = 100 + 3 * k + 1 := by rw [hM.r50]; omega
  have hk1 : 100 + 3 * k + 1 < Q := by
    have := hM.j_le; have := n_le_ecl r; have := Lr_eq r; unfold SA0 Fr at hQ0; omega
  unfold colP headP
  refine block_seq (T := 15) (T' := 11 * n + 1) (M := M)
    (mid := fun m => Keep [2, 3, 19, 29, 44, 45] Q (Q + 2) M m ∧ m 19 = Q ∧ m 44 = Q + 2 ∧
      m (Q + 1) = 3 * n ∧ m 45 = R ∧ m 3 = 2 ∧ m 29 = n ∧ m 1 = 1) ?_ (fun M0 hM0 => ?_)
  · refine copy_seq' (add_seq' (add_seq' (add_seq' (store_seq' (add_seq' ?_)))))
    refine ExplLinear.at_mem (fun m => Keep [2, 19, 44] Q (Q + 2) M m ∧ m 19 = Q ∧ m 44 = Q + 2 ∧
      m (Q + 1) = 3 * n) ⟨fun z hz hab => ?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hM.one, ← hQ]
    all_goals (simp (config := {failIfUnchanged := false}) (disch := omega) only
      [Mem.update_self, Mem.update_of_ne, hM.one, hM.r21, ← hQ]; try omega)
    obtain ⟨k1, f19, f44, fQ⟩ := hM1
    have g : ∀ z, z ∉ [2, 19, 44] → z < Q → M1 z = M z := fun z hz h => k1 z hz (Or.inl h)
    have g50 : M1 50 = M 50 := g 50 (by simp) (by omega)
    have g21 : M1 21 = n := by rw [g 21 (by simp) (by omega), hM.r21]
    have g1 : M1 1 = 1 := by rw [g 1 (by simp) (by omega), hM.one]
    refine assign_seq' (sub_seq' (load_seq' (add_seq' (add_seq' (add_seq' (add_seq'
      (assign_seq' (copy_last' (T := 0) ?_))))))))
    refine ⟨fun z hz hab => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
      exact k1 z (by simp; omega) hab
    all_goals simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f19, f44, fQ, g50,
      g21, g1, e50]
    rw [g _ (by simp; omega) (by omega), hR]; ring
  obtain ⟨k0, f19, f44, fQ, f45, f3, f29, f1⟩ := hM0
  have g0 : ∀ z, z ∉ [2, 3, 19, 29, 44, 45] → z < Q → M0 z = M z :=
    fun z hz h => k0 z hz (Or.inl h)
  have hrk0 : ∀ x < n, M0 (R + x) = rX r k x := fun x hx => by
    rw [g0 _ (by simp; omega) (by omega), hrk x hx]
  let inv : Mem → Prop := fun m => ∃ c ≤ n, m 29 = n - c ∧ m 45 = R + c ∧ m 44 = Q + 2 + 3 * c ∧
    m 1 = 1 ∧ m 3 = 2 ∧ m 19 = Q ∧ Blk m (Q + 2) (encList Enc.encode ((colsOut r).take c)) ∧
    Keep [2, 29, 44, 45] (Q + 2) (Q + 2 + 3 * c) M0 m
  have hbody : ∀ m, inv m → m 29 ≠ 0 → ∃ t, RunsTo colBody (fun m' => m' = m)
      (fun m' => inv m' ∧ 11 * m' 29 + t + 2 ≤ 11 * m 29) t := by
    intro m ⟨c, hc, e29, e45, e44, e1, e3, e19, hb, hk⟩ hne
    have hcn : c < n := by omega
    have hl : (encList Enc.encode ((colsOut r).take c)).length = 3 * c := by
      rw [length_encList_singles _ (fun s hs => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hs); rfl), List.length_take,
        length_colsOut]; omega
    refine ⟨9, ?_⟩
    unfold colBody
    refine store_seq' (add_seq' (store_seq' (add_seq' ?_)))
    refine ExplLinear.at_mem (fun m' => Keep [44] (Q + 2 + 3 * c) (Q + 2 + 3 * c + 2) m m' ∧
      m' 44 = Q + 2 + 3 * c + 2 ∧ m' (Q + 2 + 3 * c) = 2 ∧ m' (Q + 2 + 3 * c + 1) = 1)
      ⟨fun z hz hab => ?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e1, e3]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e1, e3]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e1, e3]
    obtain ⟨k1, f44, fa, fb⟩ := hM1
    have g : ∀ z, z ≠ 44 → z < Q + 2 + 3 * c ∨ Q + 2 + 3 * c + 2 ≤ z → M1 z = m z :=
      fun z hz h => k1 z (by simp; exact hz) h
    have g45 : M1 45 = R + c := by rw [g 45 (by omega) (by omega), e45]
    have gR : M1 (R + c) = rX r k c := by
      rw [g _ (by omega) (by omega), hk _ (by simp; omega) (by omega), hrk0 c hcn]
    have g1' : M1 1 = 1 := by rw [g 1 (by omega) (by omega), e1]
    refine load_seq' (store_seq' (add_seq' (add_seq' ?_)))
    refine ExplLinear.at_mem (fun m' => (∀ z, z ≠ 2 → z ≠ 44 → z ≠ 45 → z ≠ Q + 2 + 3 * c + 2 →
      m' z = M1 z) ∧ m' 44 = Q + 2 + 3 * c + 3 ∧ m' (Q + 2 + 3 * c + 2) = rX r k c ∧
      m' 45 = R + c + 1) ⟨fun z a b c' d => ?_, ?_, ?_, ?_⟩ (fun M2 hM2 => ?_)
    all_goals simp (config := {failIfUnchanged := false}) (disch := omega) only
      [Mem.update_self, Mem.update_of_ne, g45, gR, f44, g1']
    obtain ⟨k2, f44', fc, f45'⟩ := hM2
    refine sub_last' ?_
    have h21 : M2 1 = 1 := by rw [k2 1 (by omega) (by omega) (by omega) (by omega), g1']
    rw [h21]
    set mf := M2.update 29 (M2 29 - 1)
    have hmf : ∀ z, z ≠ 2 → z ≠ 29 → z ≠ 44 → z ≠ 45 → z ≠ Q + 2 + 3 * c + 2 → mf z = M1 z :=
      fun z a b c' d e => by
        simp (disch := omega) only [mf, Mem.update_of_ne]; exact k2 z a c' d e
    refine ⟨⟨c + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mf, Mem.update_self]
      rw [k2 29 (by omega) (by omega) (by omega) (by omega), g 29 (by omega) (by omega), e29]
      omega
    · simp (disch := omega) only [mf, Mem.update_self, Mem.update_of_ne, f45']; ring
    · simp (disch := omega) only [mf, Mem.update_self, Mem.update_of_ne, f44']; ring
    · rw [hmf 1 (by omega) (by omega) (by omega) (by omega) (by omega),
        g 1 (by omega) (by omega), e1]
    · rw [hmf 3 (by omega) (by omega) (by omega) (by omega) (by omega),
        g 3 (by omega) (by omega), e3]
    · rw [hmf 19 (by omega) (by omega) (by omega) (by omega) (by omega),
        g 19 (by omega) (by omega), e19]
    · rw [encList_take_succ _ _ _ (by rw [length_colsOut]; exact hcn), Blk.append]
      refine ⟨hb.congr (fun z hz1 hz2 => ?_), ?_⟩
      · rw [hmf z (by omega) (by omega) (by omega) (by omega) (by omega),
          g z (by omega) (Or.inl (by omega))]
      · rw [getElem_colsOut r (by rw [length_colsOut]; exact hcn), hl]
        change Blk mf (Q + 2 + 3 * c) [2, 1, rX r k c]
        rw [Blk.cons, Blk.cons, Blk.cons]
        refine ⟨?_, ?_, ?_, Blk.nil _ _⟩
        · rw [hmf _ (by omega) (by omega) (by omega) (by omega) (by omega), fa]
        · rw [hmf _ (by omega) (by omega) (by omega) (by omega) (by omega), fb]
        · simp (disch := omega) only [mf, Mem.update_self, Mem.update_of_ne, fc]
    · intro z hz hab
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hmf z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 (by omega), g z hz.2.2.1 (by omega)]
      exact hk z (by simp; omega) (by omega)
    · simp only [mf, Mem.update_self]
      rw [k2 29 (by omega) (by omega) (by omega) (by omega), g 29 (by omega) (by omega), e29]
      omega
  have hloop := runsTo_whileNz_amort' (i := 29) wf_colBody inv (fun m => 11 * m 29) hbody M0
    ⟨0, by omega, by omega, by omega, by omega, f1, f3, f19, Blk.nil _ _,
      Keep.refl _ _ _ _⟩
  refine (hloop.mono (by simp only; omega)).weaken (fun m ⟨⟨c, hc, e29, e45, e44, e1, e3, e19, hb, hk⟩,
    h29⟩ => ?_)
  have hcn : c = n := by omega
  subst hcn
  have hnc : n = (colsOut r).length := (length_colsOut r).symm
  rw [hnc, List.take_length] at hb
  refine ⟨e19, e1, e44, ?_, fun z hz hab => ?_⟩
  · rw [Blk.frame_iff, length_encList_colsOut]
    refine ⟨?_, hb⟩
    rw [hk _ (by simp; omega) (by omega), fQ]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hk z (by simp; omega) (by omega)]
    exact k0 z (by simp; omega) (by omega)

/-! ## The palettes -/

/-- Copy the string number `idx` of a palette: its vertex `v = A[idx]`, its address `S[v]`, its
framed encoding of length `m ptr + 1`. -/
def strBody : Program :=
  seq (loadTo 2 12) (seq (addTo 2 11 2) (seq (loadTo 3 2) (seq (loadTo 4 3) (seq (addTo 4 4 1)
    (seq (cpAdv 3 4) (seq (addTo 12 12 1) (subTo 26 26 1)))))))

theorem wf_strBody : Wf strBody := by
  unfold strBody
  exact wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_addTo _ _ _) (wf_seq
    (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (wf_cpAdv _ _) (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_subTo _ _ _)))))))

/-- The registers the palette loop writes. -/
notation "Wstr" => [2, 3, 4, 12, 26, 44, 59, 60, 61, 62, 63]

/-- **The strings of palette `i`**, copied to `p`: `7 |E_i| + 15 N_i + 1` steps, `E_i` the
encoding of `P_i`. -/
theorem runsTo_strLoop {m0 : Mem} {r : RawTagged} {i p Q : ℕ}
    (hrec : RecOK r m0 (Fr r) Q i) (h11 : m0 11 = m0 (100 + 3 * i))
    (h12 : m0 12 = m0 (100 + 3 * i + 1)) (h26 : m0 26 = NX r i) (h44 : m0 44 = p)
    (h1 : m0 1 = 1) (hQp : Q ≤ p) (hF : 200 ≤ Fr r) :
    RunsTo (whileNz 26 strBody) (fun m => m = m0)
      (fun m => Blk m p (encList Enc.encode (PX r i)) ∧
        m 44 = p + (encList Enc.encode (PX r i)).length ∧ m 1 = 1 ∧
        Keep Wstr p (p + (encList Enc.encode (PX r i)).length) m0 m)
      (7 * (encList Enc.encode (PX r i)).length + 15 * NX r i + 1) := by
  set E := encList Enc.encode (PX r i) with hE
  set d := NX r i with hd
  set S := m0 (100 + 3 * i)
  set A := m0 (100 + 3 * i + 1)
  have hdn : d = (PX r i).length := NX_eq_length r i
  have hdn' : d ≤ r.1.length := NX_le r i
  have hAQ : A + 5 * r.1.length ≤ Q := hrec.hiA
  have hSQ : S + r.1.length ≤ Q := hrec.hiS
  have hFA : Fr r ≤ A := hrec.loA
  have hFS : Fr r ≤ S := hrec.loS
  let inv : Mem → Prop := fun m => ∃ idx ≤ d, m 26 = d - idx ∧ m 12 = A + idx ∧ m 11 = S ∧
    m 44 = p + (encList Enc.encode ((PX r i).take idx)).length ∧ m 1 = 1 ∧
    Blk m p (encList Enc.encode ((PX r i).take idx)) ∧
    Keep Wstr p (p + (encList Enc.encode ((PX r i).take idx)).length) m0 m
  have hbody : ∀ m, inv m → m 26 ≠ 0 → ∃ t, RunsTo strBody (fun m' => m' = m)
      (fun m' => inv m' ∧ 7 * (E.length - (m' 44 - p)) + 15 * m' 26 + t + 2 ≤
        7 * (E.length - (m 44 - p)) + 15 * m 26) t := by
    intro m ⟨idx, hidx, e26, e12, e11, e44, e1, hb, hk⟩ hne
    have hid : idx < d := by omega
    obtain ⟨hv, hget, hlo, hhi, hstr⟩ := hrec.pal idx hid
    set v := m0 (A + idx) with hv'
    set ptr := m0 (S + v) with hptr
    set sv := sX r i v with hsv
    have hpi : (PX r i)[idx]'(by omega) = sv := by
      rw [List.getElem?_eq_getElem (by omega)] at hget; exact Option.some.inj hget
    have gm : ∀ z, z ∉ Wstr → z < p → m z = m0 z := fun z hz h => hk z hz (Or.inl h)
    have gA : m (A + idx) = v := gm _ (by simp; omega) (by omega)
    have gS : m (S + v) = ptr := gm _ (by simp; omega) (by omega)
    have gp : m ptr = 2 * sv.length := by rw [gm _ (by simp; omega) (by omega)]; exact hstr.1
    have hblk : Blk m ptr (frame (Enc.encode sv)) := by
      refine strAt_iff_blk.1 (hstr.congr (fun z hz1 hz2 => gm z (by simp; omega) (by omega)))
    have hlen : (frame (Enc.encode sv)).length = 2 * sv.length + 1 := by
      simp only [RAM.frame, List.length_cons, ExplLinear.length_encode_nat_list]
    have hlt := encList_take_lt Enc.encode (PX r i) idx (by omega)
    rw [hpi, ← hE] at hlt
    have hlt' : (encList Enc.encode ((PX r i).take idx)).length + (2 * sv.length + 1) ≤ E.length := by
      have := ExplLinear.length_encode_nat_list sv; omega
    refine ⟨7 * (frame (Enc.encode sv)).length + 13, ?_⟩
    unfold strBody
    refine RunsTo.mono (T := (7 * (frame (Enc.encode sv)).length + 6 + (0 + 1 + 1)) + 1 + 1 + 1 +
      1 + 1) ?_ (by omega)
    refine load_seq' (add_seq' (load_seq' (load_seq' (add_seq' ?_))))
    refine ExplLinear.at_mem (fun m' => (∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 → m' z = m z) ∧
      m' 3 = ptr ∧ m' 4 = 2 * sv.length + 1) ⟨fun z a b c => ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
    all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e12, e11, gA,
      gS, gp, e1]; done)
    obtain ⟨k1, f3, f4⟩ := hM1
    have g44 : M1 44 = p + (encList Enc.encode ((PX r i).take idx)).length := by
      rw [k1 44 (by omega) (by omega) (by omega), e44]
    refine block_seq (T := 7 * (frame (Enc.encode sv)).length + 6) (T' := 0 + 1 + 1)
      (runsTo_cpAdv (M := M1) (src := 3) (ln := 4) (xs := frame (Enc.encode sv))
      (by omega) (by omega) (by rw [f3]; omega) (by rw [g44]; omega)
      (by rw [f3, g44]; have := hrec.hiS; omega)
      (by rw [f3]; exact hblk.congr (fun z h1 h2 => k1 z (by omega) (by omega) (by omega)))
      (by rw [f4, hlen])) (fun M2 ⟨hb2, hk2, h44'⟩ => ?_)
    refine add_seq' (sub_last' (T := 0) ?_)
    have k2 : ∀ z, z ∉ [44, 59, 60, 61, 62, 63] → z < M1 44 → M2 z = M1 z :=
      fun z hz h => hk2 z hz (Or.inl h)
    have e12' : M2 12 = A + idx := by
      rw [k2 12 (by simp) (by omega), k1 12 (by omega) (by omega) (by omega), e12]
    have e26' : M2 26 = d - idx := by
      rw [k2 26 (by simp) (by omega), k1 26 (by omega) (by omega) (by omega), e26]
    have e1' : M2 1 = 1 := by
      rw [k2 1 (by simp) (by omega), k1 1 (by omega) (by omega) (by omega), e1]
    have e11' : M2 11 = S := by
      rw [k2 11 (by simp) (by omega), k1 11 (by omega) (by omega) (by omega), e11]
    simp (disch := omega) only [Mem.update_of_ne, e12', e1', e26']
    set mf := (M2.update 12 (A + idx + 1)).update 26 (d - idx - 1)
    have hmf : ∀ z, z ≠ 12 → z ≠ 26 → mf z = M2 z := fun z a b => by
      simp (disch := omega) only [mf, Mem.update_of_ne]
    have hE1 : encList Enc.encode ((PX r i).take (idx + 1)) =
        encList Enc.encode ((PX r i).take idx) ++ frame (Enc.encode sv) := by
      rw [encList_take_succ _ _ _ (by omega), hpi]
    have e44f : mf 44 = p + (encList Enc.encode ((PX r i).take (idx + 1))).length := by
      rw [hmf 44 (by omega) (by omega), h44', g44, hE1, List.length_append]; ring
    refine ⟨⟨idx + 1, by omega, ?_, ?_, ?_, e44f, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mf, Mem.update_self]; omega
    · simp (disch := omega) only [mf, Mem.update_self, Mem.update_of_ne]; ring
    · rw [hmf 11 (by omega) (by omega), e11']
    · rw [hmf 1 (by omega) (by omega), e1']
    · rw [hE1, Blk.append]
      refine ⟨hb.congr (fun z hz1 hz2 => ?_), ?_⟩
      · rw [hmf z (by omega) (by omega), k2 z (by simp; omega) (by omega),
          k1 z (by omega) (by omega) (by omega)]
      · rw [← g44]
        exact hb2.congr (fun z hz1 hz2 => hmf z (by omega) (by omega))
    · intro z hz hab
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hmf z (by omega) (by omega)]
      rw [hE1, List.length_append] at hab
      rw [hk2 z (by simp; omega) (by rw [g44]; omega),
        k1 z (by omega) (by omega) (by omega)]
      exact hk z (by simp; omega) (by omega)
    · have h26 : mf 26 = d - idx - 1 := by simp only [mf, Mem.update_self]
      rw [h26, h44', g44, e44, e26, hlen]
      omega
  have hloop := runsTo_whileNz_amort' (i := 26) wf_strBody inv
    (fun m => 7 * (E.length - (m 44 - p)) + 15 * m 26) hbody m0
    ⟨0, by omega, by omega, by rw [h12]; rfl, h11, by rw [h44, List.take_zero]; rfl, h1, Blk.nil _ _,
      Keep.refl _ _ _ _⟩
  refine (hloop.mono (by simp only; rw [h44, h26]; omega)).weaken
    (fun m ⟨⟨idx, hidx, e26, e12, e11, e44, e1, hb, hk⟩, h0⟩ => ?_)
  have : idx = d := by omega
  subst this
  rw [hdn, List.take_length] at hb e44 hk
  exact ⟨hb, e44, e1, hk⟩

/-- One palette: its length cell, its strings, the length. -/
def palBody : Program :=
  seq (copyTo 10 44) (seq (addTo 44 44 1) (seq (loadTo 11 49) (seq (addTo 2 49 1)
    (seq (loadTo 12 2) (seq (addTo 2 2 1) (seq (loadTo 26 2) (seq (whileNz 26 strBody)
    (seq (subTo 2 44 10) (seq (subTo 2 2 1) (seq (storeTo 10 2) (seq (addTo 49 49 1)
    (seq (addTo 49 49 1) (seq (addTo 49 49 1) (subTo 28 28 1))))))))))))))

/-- The palettes of the rounds `0, …, k`. -/
def palsP : Program :=
  seq (assign 49 100) (seq (copyTo 28 54) (seq (subTo 28 28 1) (whileNz 28 palBody)))

theorem wf_palBody : Wf palBody := by
  unfold palBody
  wf_tac

/-- The registers the palettes write. -/
notation "Wpal" => [2, 3, 4, 10, 11, 12, 26, 28, 44, 49, 59, 60, 61, 62, 63]

/-- The cost of one palette. -/
noncomputable def palCost (r : RawTagged) (i : ℕ) : ℕ :=
  7 * (encList Enc.encode (PX r i)).length + 15 * NX r i + 20

theorem length_palsOut (r : RawTagged) : (palsOut r).length = kS r + 1 := by simp [palsOut]

theorem getElem_palsOut (r : RawTagged) {i : ℕ} (hi : i < (palsOut r).length) :
    (palsOut r)[i] = PX r i := by simp [palsOut]

/-- **The palettes**, written at `P0 = m 44`. -/
theorem runsTo_palsP {mB : Mem} {r : RawTagged} {Q : ℕ}
    (hrec : ∀ i ≤ kS r, RecOK r mB (Fr r) Q i) (h54 : mB 54 = kS r + 2) (h1 : mB 1 = 1)
    (hQ : Q ≤ mB 44) (hF : 200 ≤ Fr r) (hk : 100 + 3 * (kS r + 1) ≤ Fr r) :
    RunsTo palsP (fun m => m = mB)
      (fun m => Blk m (mB 44) (encList Enc.encode (palsOut r)) ∧
        m 44 = mB 44 + (encList Enc.encode (palsOut r)).length ∧ m 1 = 1 ∧
        Keep Wpal (mB 44) (mB 44 + (encList Enc.encode (palsOut r)).length) mB m)
      (3 + (∑ j ∈ Finset.range (kS r + 1), palCost r (kS r - j) + 1)) := by
  set k := kS r
  set P0 := mB 44
  set pals := palsOut r
  have hFQ : Fr r ≤ Q := by
    have := (hrec 0 (by omega)).loS; have := (hrec 0 (by omega)).hiS; omega
  let inv : Mem → Prop := fun m => ∃ i ≤ k + 1, m 28 = k + 1 - i ∧ m 49 = 100 + 3 * i ∧
    m 1 = 1 ∧ m 44 = P0 + (encList Enc.encode (pals.take i)).length ∧
    Blk m P0 (encList Enc.encode (pals.take i)) ∧
    Keep Wpal P0 (P0 + (encList Enc.encode (pals.take i)).length) mB m
  let Φ : Mem → ℕ := fun m => ∑ j ∈ Finset.range (m 28), palCost r (k - j)
  have hbody : ∀ m, inv m → m 28 ≠ 0 → ∃ t, RunsTo palBody (fun m' => m' = m)
      (fun m' => inv m' ∧ Φ m' + t + 2 ≤ Φ m) t := by
    intro m ⟨i, hi, e28, e49, e1, e44, hb, hkp⟩ hne
    have hik : i ≤ k := by omega
    set w := P0 + (encList Enc.encode (pals.take i)).length with hw
    have hRi := hrec i hik
    have gm : ∀ z, z ∉ Wpal → z < P0 → m z = mB z := fun z hz h => hkp z hz (Or.inl h)
    have gS : m (100 + 3 * i) = mB (100 + 3 * i) := gm _ (by simp; omega) (by omega)
    have gA : m (100 + 3 * i + 1) = mB (100 + 3 * i + 1) := gm _ (by simp; omega) (by omega)
    have gd : m (100 + 3 * i + 2) = NX r i := by
      rw [gm _ (by simp; omega) (by omega)]; exact hRi.d
    refine ⟨7 * (encList Enc.encode (PX r i)).length + 15 * NX r i + 15, ?_⟩
    unfold palBody
    refine RunsTo.mono (T := ((7 * (encList Enc.encode (PX r i)).length + 15 * NX r i + 1) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
      + 1 + 1 + 1 + 1 + 1 + 1 + 1) ?_ (by omega)
    refine copy_seq' (add_seq' (load_seq' (add_seq' (load_seq' (add_seq' (load_seq' ?_))))))
    refine ExplLinear.at_mem (fun m' => (∀ z, z ∉ [2, 10, 11, 12, 26, 44] → m' z = m z) ∧
      m' 10 = w ∧ m' 44 = w + 1 ∧ m' 11 = mB (100 + 3 * i) ∧
      m' 12 = mB (100 + 3 * i + 1) ∧ m' 26 = NX r i)
      ⟨fun z hz => ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp (disch := omega) only [Mem.update_of_ne]
    all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e49, e1,
      gS, gA, gd]; done)
    all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e44, e49, e1,
      gS, gA, gd, show 100 + 3 * i + 1 + 1 = 100 + 3 * i + 2 by ring]; done)
    obtain ⟨k1, f10, f44, f11, f12, f26⟩ := hM1
    have g1 : ∀ z, z ∉ Wpal → z < P0 → M1 z = mB z := fun z hz h => by
      rw [k1 z (by simp at hz ⊢; omega)]; exact gm z hz h
    have hrec1 : RecOK r M1 (Fr r) Q i := hRi.congr
      (fun c hc => g1 _ (by simp; omega) (by omega))
      (fun z h1 h2 => g1 z (by simp; omega) (by omega))
    have hS1 : M1 11 = M1 (100 + 3 * i) := by rw [f11, g1 _ (by simp; omega) (by omega)]
    have hA1 : M1 12 = M1 (100 + 3 * i + 1) := by rw [f12, g1 _ (by simp; omega) (by omega)]
    have e1' : M1 1 = 1 := by rw [k1 1 (by simp), e1]
    refine block_seq (T := 7 * (encList Enc.encode (PX r i)).length + 15 * NX r i + 1) (T' := 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (runsTo_strLoop hrec1 hS1 hA1 f26 f44 e1' (by omega) hF) (fun M2 ⟨hb2, h44', h1', hk2⟩ => ?_)
    have k2 : ∀ z, z ∉ Wstr → z < w + 1 → M2 z = M1 z := fun z hz h => hk2 z hz (Or.inl h)
    have f10' : M2 10 = w := by rw [k2 10 (by simp) (by omega), f10]
    have f49' : M2 49 = 100 + 3 * i := by
      rw [k2 49 (by simp) (by omega), k1 49 (by simp), e49]
    have f28' : M2 28 = k + 1 - i := by
      rw [k2 28 (by simp) (by omega), k1 28 (by simp), e28]
    refine sub_seq' (sub_seq' (store_seq' (add_seq' (add_seq' (add_seq' ?_)))))
    refine ExplLinear.at_mem (fun m' => (∀ z, z ≠ 2 → z ≠ 49 → z ≠ w → m' z = M2 z) ∧
      m' w = (encList Enc.encode (PX r i)).length ∧ m' 49 = 100 + 3 * (i + 1) ∧ m' 1 = 1 ∧ m' 28 = k + 1 - i)
      ⟨fun z a b c => ?_, ?_, ?_, ?_, ?_⟩ (fun M3 hM3 => ?_)
    all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h44', f10',
      h1', f49', f28']; done)
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h44', f10', h1', f49', f28']
      omega
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h44', f10', h1', f49', f28']
      ring
    obtain ⟨k3, fw, f49, f1, f28⟩ := hM3
    refine sub_last' (T := 0) ?_
    rw [f1, f28]
    set mf := M3.update 28 (k + 1 - i - 1)
    have hmf : ∀ z, z ≠ 2 → z ≠ 28 → z ≠ 49 → z ≠ w → mf z = M2 z := fun z a b c d => by
      simp (disch := omega) only [mf, Mem.update_of_ne]; exact k3 z a c d
    have hpi : pals[i]'(by rw [length_palsOut]; omega) = PX r i := getElem_palsOut r _
    have hE1 : encList Enc.encode (pals.take (i + 1)) =
        encList Enc.encode (pals.take i) ++ frame (encList Enc.encode (PX r i)) := by
      rw [encList_take_succ _ _ _ (by rw [length_palsOut]; omega), hpi]; rfl
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mf, Mem.update_self]; omega
    · rw [show mf 49 = M3 49 by simp (disch := omega) only [mf, Mem.update_of_ne], f49]
    · rw [show mf 1 = M3 1 by simp (disch := omega) only [mf, Mem.update_of_ne], f1]
    · rw [hmf 44 (by omega) (by omega) (by omega) (by omega), h44', hE1, List.length_append]
      simp only [RAM.frame, List.length_cons]; omega
    · rw [hE1, Blk.append, Blk.frame_iff]
      refine ⟨hb.congr (fun z hz1 hz2 => ?_), ?_, ?_⟩
      · rw [hmf z (by omega) (by omega) (by omega) (by omega), k2 z (by simp; omega) (by omega),
          k1 z (by simp; omega)]
      · rw [← hw, show mf w = M3 w by simp (disch := omega) only [mf, Mem.update_of_ne], fw]
      · rw [← hw]
        exact hb2.congr (fun z hz1 hz2 => hmf z (by omega) (by omega) (by omega) (by omega))
    · intro z hz hab
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hE1, List.length_append] at hab
      simp only [RAM.frame, List.length_cons] at hab
      rw [hmf z (by omega) (by omega) (by omega) (by omega), hk2 z (by simp; omega) (by omega),
        k1 z (by simp; omega)]
      exact hkp z (by simp; omega) (by omega)
    · simp only [Φ, mf, Mem.update_self, e28]
      obtain ⟨c, hc⟩ : ∃ c, k + 1 - i = c + 1 := ⟨k - i, by omega⟩
      rw [hc, Nat.add_sub_cancel, Finset.sum_range_succ]
      have : k - c = i := by omega
      rw [this]; unfold palCost; omega
  unfold palsP
  set mA := ((mB.update 49 100).update 28 (mB.update 49 100 54)).update 28
    (((mB.update 49 100).update 28 (mB.update 49 100 54)) 28 -
      ((mB.update 49 100).update 28 (mB.update 49 100 54)) 1) with hmA
  have a28 : mA 28 = k + 1 := by
    simp (disch := omega) only [hmA, Mem.update_self, Mem.update_of_ne, h54, h1]; omega
  have aK : ∀ z, z ≠ 28 → z ≠ 49 → mA z = mB z := fun z a b => by
    simp (disch := omega) only [hmA, Mem.update_of_ne]
  refine RunsTo.mono (T := (Φ mA + 1) + 1 + 1 + 1) ?_ (by simp only [Φ, a28]; omega)
  refine assign_seq' (copy_seq' (sub_seq' ?_))
  have a49 : mA 49 = 100 := by
    simp (disch := omega) only [hmA, Mem.update_self, Mem.update_of_ne]
  have hinit : inv mA := by
    refine ⟨0, by omega, by rw [a28]; rfl, a49, ?_, ?_, Blk.nil _ _, fun z hz hab => ?_⟩
    · rw [aK 1 (by omega) (by omega), h1]
    · rw [aK 44 (by omega) (by omega), List.take_zero]; rfl
    · exact aK z (by simp at hz; omega) (by simp at hz; omega)
  have hloop := runsTo_whileNz_amort' (i := 28) wf_palBody inv Φ hbody mA hinit
  show RunsTo _ (fun m => m = mA) _ _
  refine hloop.weaken (fun m ⟨⟨i, hi, e28, e49, e1, e44, hb, hkp⟩, h0⟩ => ?_)
  have : i = k + 1 := by omega
  subst this
  have hl : pals.take (k + 1) = pals := by
    rw [show k + 1 = pals.length by rw [length_palsOut], List.take_length]
  rw [hl] at hb e44 hkp
  exact ⟨hb, e44, e1, hkp⟩

/-! ## The edges and the input tag -/

/-- The length cell of the edges-and-tag part (`47`), the framed edges (copied from `15`), the
length cell of the tag (`48`), the input tag (copied from `17`). -/
def etP : Program :=
  seq (copyTo 47 44) (seq (addTo 44 44 1) (seq (loadTo 2 15) (seq (addTo 2 2 1)
    (seq (cpAdv 15 2) (seq (copyTo 48 44) (seq (addTo 44 44 1) (cpAdv 17 18)))))))

theorem runsTo_etP {M : Mem} {r : RawTagged} (hinp : Blk M (Fr r) (Lr r :: Enc.encode r))
    (h15 : M 15 = Eblk r) (h17 : M 17 = T0 r) (h18 : M 18 = etl r) (h1 : M 1 = 1)
    (hw : SA0 r ≤ M 44) :
    RunsTo etP (fun m => m = M) (fun m => m 47 = M 44 ∧ m 48 = M 44 + 1 + (eel r + 1) ∧
      m 44 = M 44 + 1 + (eel r + 1) + 1 + etl r ∧ m 1 = 1 ∧
      Blk m (M 44 + 1) (frame (encList Enc.encode r.2.1)) ∧
      Blk m (M 44 + 1 + (eel r + 1) + 1) (encList Enc.encode r.2.2) ∧
      Keep [2, 44, 47, 48, 59, 60, 61, 62, 63] (M 44) (M 44 + 1 + (eel r + 1) + 1 + etl r) M m)
      (7 * eel r + 7 * etl r + 25) := by
  obtain ⟨-, -, -, hEl, -, -, hTb, hEb⟩ := inp_layout hinp
  have hL := Lr_eq r
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hEE : (frame (encList Enc.encode r.2.1)).length = eel r + 1 := by
    simp [RAM.frame, eel]
  have hET : (encList Enc.encode r.2.2).length = etl r := rfl
  have hSA : Fr r + Lr r + 1 = SA0 r := rfl
  unfold etP
  refine RunsTo.mono (T := ((7 * (frame (encList Enc.encode r.2.1)).length + 6) +
    ((7 * (encList Enc.encode r.2.2).length + 6) + 1 + 1)) + 1 + 1 + 1 + 1) ?_
    (by rw [hEE, hET]; omega)
  refine copy_seq' (add_seq' (load_seq' (add_seq' ?_)))
  set M0 := (((M.update 47 (M 44)).update 44 ((M.update 47 (M 44)) 44 +
    (M.update 47 (M 44)) 1)).update 2 ((((M.update 47 (M 44)).update 44 ((M.update 47 (M 44)) 44 +
    (M.update 47 (M 44)) 1))) ((((M.update 47 (M 44)).update 44 ((M.update 47 (M 44)) 44 +
    (M.update 47 (M 44)) 1))) 15)))
  set M1 := M0.update 2 (M0 2 + M0 1)
  have K1 : ∀ z, z ≠ 2 → z ≠ 44 → z ≠ 47 → M1 z = M z := fun z a b c => by
    simp (disch := omega) only [M1, M0, Mem.update_of_ne]
  have f44 : M1 44 = M 44 + 1 := by
    simp (disch := omega) only [M1, M0, Mem.update_of_ne, Mem.update_self, h1]
  have f2 : M1 2 = eel r + 1 := by
    simp (disch := omega) only [M1, M0, Mem.update_of_ne, Mem.update_self, h15, h1]
    rw [Mem.update_of_ne _ _ (by unfold Eblk; omega), Mem.update_of_ne _ _ (by unfold Eblk; omega),
      hEl]
  refine block_seq (T := 7 * (frame (encList Enc.encode r.2.1)).length + 6)
    (T' := (7 * (encList Enc.encode r.2.2).length + 6) + 1 + 1)
    (runsTo_cpAdv (M := M1) (src := 15) (ln := 2) (xs := frame (encList Enc.encode r.2.1))
      (by omega) (by omega) (by rw [K1 15 (by omega) (by omega) (by omega), h15]; unfold Eblk; omega)
      (by rw [f44]; unfold SA0 at hw; omega)
      (by rw [K1 15 (by omega) (by omega) (by omega), h15, f2, f44]; unfold Eblk SA0 at *; omega)
      (by rw [K1 15 (by omega) (by omega) (by omega), h15]
          exact hEb.congr (fun z h1 h2 => K1 z (by unfold Eblk at h1; omega)
            (by unfold Eblk at h1; omega) (by unfold Eblk at h1; omega)))
      (by rw [f2, hEE])) (fun M2 ⟨hb2, hk2, h44⟩ => ?_)
  have k2 : ∀ z, z ∉ [44, 59, 60, 61, 62, 63] → z < M 44 + 1 → M2 z = M1 z := fun z hz h =>
    hk2 z hz (Or.inl (by rw [f44]; exact h))
  refine copy_seq' (add_seq' ?_)
  set M3 := (M2.update 48 (M2 44)).update 44 ((M2.update 48 (M2 44)) 44 + (M2.update 48 (M2 44)) 1)
  have K3 : ∀ z, z ≠ 44 → z ≠ 48 → M3 z = M2 z := fun z a b => by
    simp (disch := omega) only [M3, Mem.update_of_ne]
  have g1 : M2 1 = 1 := by rw [k2 1 (by simp) (by omega), K1 1 (by omega) (by omega) (by omega), h1]
  have g44 : M3 44 = M 44 + 1 + (eel r + 1) + 1 := by
    simp (disch := omega) only [M3, Mem.update_of_ne, Mem.update_self, g1, h44, f44, hEE]
  have g17 : M3 17 = T0 r := by
    rw [K3 17 (by omega) (by omega), k2 17 (by simp) (by omega), K1 17 (by omega) (by omega)
      (by omega), h17]
  have g18 : M3 18 = etl r := by
    rw [K3 18 (by omega) (by omega), k2 18 (by simp) (by omega), K1 18 (by omega) (by omega)
      (by omega), h18]
  have hT0 : T0 r + etl r ≤ SA0 r := by unfold T0 SA0; omega
  refine (runsTo_cpAdv (M := M3) (src := 17) (ln := 18) (xs := encList Enc.encode r.2.2)
    (by omega) (by omega) (by rw [g17]; unfold T0; omega) (by rw [g44]; unfold SA0 at hw; omega)
    (by rw [g17, g18, g44]; omega)
    (by rw [g17]
        exact hTb.congr (fun z h1 h2 => by
          rw [K3 z (by unfold T0 at h1; omega) (by unfold T0 at h1; omega),
            k2 z (by simp; unfold T0 at h1; omega) (by rw [hET] at h2; omega),
            K1 z (by unfold T0 at h1; omega) (by unfold T0 at h1; omega)
              (by unfold T0 at h1; omega)]))
    (by rw [g18, hET])).weaken (fun m ⟨hb3, hk3, h44'⟩ => ?_)
  rw [g44] at hb3 hk3 h44'
  have k3 : ∀ z, z ∉ [44, 59, 60, 61, 62, 63] → z < M 44 + 1 + (eel r + 1) + 1 → m z = M3 z :=
    fun z hz h => hk3 z hz (Or.inl h)
  refine ⟨?_, ?_, by rw [h44', hET], ?_, ?_, hb3, fun z hz hab => ?_⟩
  · rw [k3 47 (by simp) (by omega), K3 47 (by omega) (by omega), k2 47 (by simp) (by omega)]
    simp (disch := omega) only [M1, M0, Mem.update_of_ne, Mem.update_self]
  · rw [k3 48 (by simp) (by omega)]
    simp (disch := omega) only [M3, Mem.update_of_ne, Mem.update_self, h44, f44, hEE]
  · rw [k3 1 (by simp) (by omega), K3 1 (by omega) (by omega), g1]
  · rw [← f44]
    refine hb2.congr (fun z h1 h2 => ?_)
    rw [f44, hEE] at *
    rw [k3 z (by simp; omega) (by omega), K3 z (by omega) (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hk3 z (by simp; omega) (by rw [hET]; omega), K3 z (by omega) (by omega),
      hk2 z (by simp; omega) (by rw [f44, hEE]; omega),
      K1 z (by omega) (by omega) (by omega)]

/-! ## The length cells, and the move to `16` -/

/-- Fill the three length cells (tag, edges-and-tag, whole output). -/
def patchP : Program :=
  seq (subTo 2 44 48) (seq (subTo 2 2 1) (seq (storeTo 48 2) (seq (subTo 2 44 47)
    (seq (subTo 2 2 1) (seq (storeTo 47 2) (seq (subTo 2 44 19) (seq (subTo 2 2 1)
    (storeTo 19 2))))))))

/-- Move the framed output from `Q` to `16`. -/
def moveP : Program :=
  seq (copyTo 0 19) (seq (assign 1 16) (seq (subTo 2 44 19) (Arrays.copyBlock 0 1 2 3)))

theorem runsTo_finish {M : Mem} {Q : ℕ} {C X Y : List ℕ} (h19 : M 19 = Q) (hQ : 200 ≤ Q)
    (h1 : M 1 = 1) (h47 : M 47 = Q + 1 + (C.length + 1))
    (h48 : M 48 = M 47 + 1 + X.length) (h44 : M 44 = M 48 + 1 + Y.length)
    (hC : Blk M (Q + 1) (frame C)) (hX : Blk M (M 47 + 1) X) (hY : Blk M (M 48 + 1) Y) :
    RunsTo (seq patchP moveP) (fun m => m = M)
      (fun m => Blk m 16 (frame (frame C ++ frame (X ++ frame Y))))
      (7 * (frame C ++ frame (X ++ frame Y)).length + 29) := by
  set out := frame C ++ frame (X ++ frame Y) with hout
  have hlo : out.length = C.length + X.length + Y.length + 3 := by
    simp only [hout, RAM.frame, List.length_append, List.length_cons]; omega
  have hM44 : M 44 = Q + 1 + out.length := by rw [hlo, h44, h48, h47]; ring
  have hXY : (X ++ frame Y).length = X.length + Y.length + 1 := by
    simp only [RAM.frame, List.length_append, List.length_cons]; omega
  unfold patchP moveP
  refine RunsTo.mono (T := (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
    ((7 * (out.length + 1) + 5) + 1 + 1 + 1)) ?_ (by omega)
  refine block_seq (mid := fun m => (∀ z, z ≠ 2 → z ≠ Q → z ≠ M 47 → z ≠ M 48 → m z = M z) ∧
    m Q = out.length ∧ m (M 47) = (X ++ frame Y).length ∧ m (M 48) = Y.length) ?_
    (fun M1 hM1 => ?_)
  · refine sub_seq' (sub_seq' (store_seq' (sub_seq' (sub_seq' (store_seq' (sub_seq' (sub_seq'
      (store_last' ?_))))))))
    refine ⟨fun z a b c d => ?_, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h19, h44, h48, h47]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h19, h44, h48, h47]
      rw [hlo]; omega
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h19, h44, h48, h47]
      rw [hXY]; omega
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h19, h44, h48, h47]
      omega
  obtain ⟨k1, fQ, f2, f3⟩ := hM1
  have hfr : Blk M1 Q (frame out) := by
    obtain ⟨hC0, hC1⟩ := Blk.frame_iff.1 hC
    rw [Blk.frame_iff, hout, Blk.append, Blk.frame_iff, Blk.frame_iff, Blk.append, Blk.frame_iff]
    have e1 : Q + 1 + (frame C).length = M 47 := by rw [h47]; simp [RAM.frame]
    rw [e1, ← h48]
    refine ⟨fQ, ⟨?_, ?_⟩, f2, ?_, f3, ?_⟩
    · rw [k1 _ (by omega) (by omega) (by omega) (by omega)]; exact hC0
    · exact hC1.congr (fun z h1 h2 => k1 z (by omega) (by omega) (by omega) (by omega))
    · exact hX.congr (fun z h1 h2 => k1 z (by omega) (by omega) (by omega) (by omega))
    · exact hY.congr (fun z h1 h2 => k1 z (by omega) (by omega) (by omega) (by omega))
  have g19 : M1 19 = Q := by rw [k1 19 (by omega) (by omega) (by omega) (by omega), h19]
  have g44 : M1 44 = Q + 1 + out.length := by
    rw [k1 44 (by omega) (by omega) (by omega) (by omega), hM44]
  refine copy_seq' (assign_seq' (sub_seq' ?_))
  set M2 := ((M1.update 0 (M1 19)).update 1 16).update 2
    (((M1.update 0 (M1 19)).update 1 16) 44 - ((M1.update 0 (M1 19)).update 1 16) 19)
  have a0 : M2 0 = Q := by simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne, g19]
  have a1 : M2 1 = 16 := by simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne]
  have a2 : M2 2 = out.length + 1 := by
    simp (disch := omega) only [M2, Mem.update_self, Mem.update_of_ne, g19, g44]; omega
  have aK : ∀ z, 3 ≤ z → M2 z = M1 z := fun z hz => by
    simp (disch := omega) only [M2, Mem.update_of_ne]
  refine ((Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) M2 (by omega)
    (by omega) (Or.inl (by omega))).mono (by rw [a2])).weaken (fun m ⟨hc, _⟩ => ?_)
  intro j hj
  have hj' : j < M2 2 := by rw [a2]; simpa [RAM.frame] using hj
  have := hc j hj'
  rw [a1, a0, aK _ (by omega)] at this
  rw [this]; exact hfr j hj

/-! ## The output phase -/

/-- Write `X*` and move it to `16`. -/
def outP : Program := seq colP (seq etP (seq palsP (seq patchP moveP)))

/-- The time of the output phase. -/
noncomputable def tOut (r : RawTagged) : ℕ :=
  (15 + (11 * r.1.length + 1)) + ((7 * eel r + 7 * etl r + 25) +
    ((3 + (∑ j ∈ Finset.range (kS r + 1), palCost r (kS r - j) + 1)) +
      (7 * (Enc.encode (taggedOut r)).length + 29)))

/-- **The output phase**: from the state after the rounds, `X*` framed at `16`. -/
theorem runsTo_outP {M : Mem} {r : RawTagged} (hM : MInv r (kS r + 1) M) :
    RunsTo outP (fun m => m = M) (fun m => Blk m 16 (frame (Enc.encode (taggedOut r))))
      (tOut r) := by
  set n := r.1.length with hn
  set k := kS r with hk
  set Q := M 14 with hQ
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hL := Lr_eq r
  have hQ0 : SA0 r + n ≤ Q := hM.r14
  have hSA : Fr r + Lr r + 1 = SA0 r := rfl
  have hkn := hM.j_le
  have hnL := n_le_ecl r
  have hkF : 100 + 3 * (k + 1) ≤ Fr r := by unfold Fr; omega
  have hLl : Lr r = (Enc.encode r).length := rfl
  unfold outP tOut
  rw [encode_taggedOut]
  refine block_seq (runsTo_colP hM) (fun M1 ⟨e19, e1, e44, hC, k1⟩ => ?_)
  have g1 : ∀ z, z ∉ [2, 3, 19, 29, 44, 45] → z < Q → M1 z = M z :=
    fun z hz h => k1 z hz (Or.inl h)
  have hinp1 : Blk M1 (Fr r) (Lr r :: Enc.encode r) := hM.inp.congr (fun z h1 h2 =>
    g1 z (by simp; omega) (by simp at h2; unfold SA0 at hQ0; omega))
  refine block_seq (runsTo_etP hinp1
    (by rw [g1 15 (by simp) (by omega), hM.r15]) (by rw [g1 17 (by simp) (by omega), hM.r17])
    (by rw [g1 18 (by simp) (by omega), hM.r18]) e1 (by rw [e44]; omega))
    (fun M2 ⟨f47, f48, f44, f1, hEE, hET, k2⟩ => ?_)
  rw [e44] at f47 f48 f44 hEE hET k2
  set w1 := Q + 2 + 3 * n with hw1
  have g2 : ∀ z, z ∉ [2, 44, 47, 48, 59, 60, 61, 62, 63] → z < w1 → M2 z = M1 z :=
    fun z hz h => k2 z hz (Or.inl h)
  have hrec2 : ∀ i ≤ k, RecOK r M2 (Fr r) Q i := fun i hi =>
    (hM.recs i (by omega)).congr
      (fun c hc => by rw [g2 _ (by simp; omega) (by omega), g1 _ (by simp; omega) (by omega)])
      (fun z h1 h2 => by rw [g2 _ (by simp; omega) (by omega), g1 _ (by simp; omega) h2])
  refine block_seq (runsTo_palsP hrec2
    (by rw [g2 54 (by simp) (by omega), g1 54 (by simp) (by omega), hM.r54])
    f1 (by rw [f44]; omega) hF hkF) (fun M3 ⟨hb3, f44', f1', k3⟩ => ?_)
  rw [f44] at hb3 f44' k3
  set P0 := w1 + 1 + (eel r + 1) + 1 + etl r with hP0
  have g3 : ∀ z, z ∉ Wpal → z < P0 → M3 z = M2 z := fun z hz h => k3 z hz (Or.inl h)
  have hlC : (encList Enc.encode (colsOut r)).length = 3 * n := length_encList_colsOut r
  have hlX : (frame (encList Enc.encode r.2.1)).length = eel r + 1 := by simp [RAM.frame, eel]
  have hlT : (encList Enc.encode r.2.2).length = etl r := rfl
  have h47 : M3 47 = w1 := by rw [g3 47 (by simp) (by omega), f47]
  have h48 : M3 48 = w1 + 1 + (eel r + 1) := by rw [g3 48 (by simp) (by omega), f48]
  refine runsTo_finish (Q := Q)
    (by rw [g3 19 (by simp) (by omega), g2 19 (by simp) (by omega), e19])
    (by unfold SA0 at hQ0; omega) f1'
    (by rw [h47, hlC]; omega)
    (by rw [h48, h47, hlX])
    (by rw [f44', h48, List.length_append, hlT]; omega)
    (hC.congr (fun z h1 h2 => by
      simp only [RAM.frame, List.length_cons] at h2
      rw [g3 z (by simp; omega) (by omega), g2 z (by simp; omega) (by omega)]))
    (by rw [h47]; exact hEE.congr (fun z h1 h2 => by
      rw [hlX] at h2; exact g3 z (by simp; omega) (by omega)))
    (by
      rw [h48, Blk.append]
      refine ⟨hET.congr (fun z h1 h2 => by rw [hlT] at h2; exact g3 z (by simp; omega) (by omega)),
        ?_⟩
      rw [hlT]; exact hb3)

end TagLin

end Algo
