/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The sorting routines of
the fast program: a stable counting sort, radix sort, and dense ranks of a sorted list.
-/
import Workspace.Algo.WLFastSem
import Workspace.Algo.TagLinBase

/-!
# Radix sort on the RAM

Records are blocks of consecutive registers; a record is named by its address `x`, and its
field `j` is the register `x + j`.  The routines below sort an array of record addresses.

* `csP`: one pass of a stable counting sort of the array at `A` (length `len`) by the field
  at offset `d` (keys below `K`).  It uses the region `[Cnt, Cnt + K + len)`: the counts, then
  the output, which is copied back to `A`.  The result is `Algo.WLFast.csortL`
  (`runsTo_csP`), in `O(K + len)` steps.
* `radixP`: `L` passes, fields `f0 + L - 1` down to `f0`; the result is sorted by the list of
  the fields `f0, …, f0 + L - 1` (`runsTo_radixP`).
* `rankP`: along a sorted array, write into field `g` of every record its dense rank
  (`runsTo_rankP`).

Registers: `1` the constant `1`; `30` the array `A`, `31` its length, `32` the first field
`f0`, `33` the number of fields `L`, `34` the key bound `K`, `35` the region `Cnt`; `36`–`49`
scratch.

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

/-! ## A counted loop -/

/-- A run whose step count is computed along the proof, then bounded. -/
theorem RunsTo.of_le {P : Program} {pre post : Mem → Prop} {B : ℕ}
    (h : ∃ T, RunsTo P pre post T ∧ T ≤ B) : RunsTo P pre post B :=
  let ⟨_, h, hT⟩ := h; h.mono hT

/-- **A counted loop.**  The body runs `L` times, each time within `T` steps, and moves the
invariant from `I t` to `I (t + 1)`; register `c` counts down from `L`. -/
theorem runsTo_countLoop {c : ℕ} {P : Program} (hw : Wf P) (I : ℕ → Mem → Prop) (L T : ℕ)
    (hc : ∀ t m, I t m → m c = L - t ∧ t ≤ L)
    (hP : ∀ t m, t < L → I t m → RunsTo P (fun m' => m' = m) (I (t + 1)) T)
    (M : Mem) (hM : I 0 M) :
    RunsTo (whileNz c P) (fun m => m = M) (I L) (L * (T + 2) + 1) := by
  obtain ⟨s, hs⟩ := runsTo_whileNz_amortX (i := c) hw (fun m => ∃ t, I t m)
    (fun m => m c * (T + 2)) (fun m ⟨t, ht⟩ hne => by
      obtain ⟨h1, h2⟩ := hc t m ht
      have htL : t < L := by omega
      refine ⟨T, (hP t m htL ht).weaken (fun m' hm' => ⟨⟨t + 1, hm'⟩, ?_⟩)⟩
      obtain ⟨h1', _⟩ := hc (t + 1) m' hm'
      show m' c * (T + 2) + T + 2 ≤ m c * (T + 2)
      rw [h1', h1]
      have : L - t = (L - (t + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega) M ⟨0, hM⟩
  obtain ⟨M', ⟨⟨t, ht⟩, h0, hΦ⟩, hrun⟩ := hs.exact
  obtain ⟨e1, e2⟩ := hc t M' ht
  have htL : t = L := by omega
  subst htL
  obtain ⟨e3, _⟩ := hc 0 M hM
  refine (hrun.mono ?_).weaken (fun m hm => by rw [hm]; exact ht)
  rw [e3] at hΦ
  simp only [Nat.sub_zero] at hΦ
  nlinarith

/-! ## Lists in blocks -/

theorem blk_csortL {m : Mem} {P : ℕ} {key : ℕ → ℕ} {xs : List ℕ} :
    ∀ K : ℕ, (∀ c < K, Blk m (P + (csortL key c xs).length) (xs.filter (fun x => key x = c))) →
      Blk m P (csortL key K xs)
  | 0, _ => Blk.nil _ _
  | K + 1, h => by
      rw [csortL_succ, Blk.append]
      exact ⟨blk_csortL K (fun c hc => h c (by omega)), h K (by omega)⟩

theorem length_csortL_le {key : ℕ → ℕ} {xs : List ℕ} {c c' : ℕ} (h : c ≤ c') :
    (csortL key c xs).length ≤ (csortL key c' xs).length := by
  induction c' with
  | zero => obtain rfl : c = 0 := by omega
            exact le_refl _
  | succ c' ih =>
      rcases Nat.eq_or_lt_of_le h with e | e
      · rw [e]
      · rw [length_csortL_succ]; have := ih (by omega); omega

theorem length_csortL_of_lt {key : ℕ → ℕ} {xs : List ℕ} {K : ℕ} (hk : ∀ x ∈ xs, key x < K) :
    (csortL key K xs).length = xs.length := (csortL_perm hk).length_eq

theorem filter_take_succ {xs : List ℕ} {t : ℕ} (ht : t < xs.length) (P : ℕ → Bool) :
    (xs.take (t + 1)).filter P = (xs.take t).filter P ++ (if P xs[t] then [xs[t]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]

theorem length_filter_take_lt {xs : List ℕ} {t : ℕ} (ht : t < xs.length) {P : ℕ → Bool}
    (hP : P xs[t] = true) : ((xs.take t).filter P).length < (xs.filter P).length := by
  have h1 : ((xs.take (t + 1)).filter P).length ≤ (xs.filter P).length :=
    ((List.take_sublist _ _).filter P).length_le
  rw [filter_take_succ ht, List.length_append, if_pos hP] at h1
  simp at h1; omega

/-! ## One pass of counting sort -/

/-- Count the keys: `Cnt[key x] += 1` for every `x` of the array. -/
def cntBody : Program :=
  seq (loadTo 41 40) (seq (addTo 41 41 37) (seq (loadTo 41 41) (seq (addTo 41 41 35)
  (seq (loadTo 42 41) (seq (addTo 42 42 1) (seq (storeTo 41 42) (seq (addTo 40 40 1)
  (subTo 39 39 1))))))))

/-- The start addresses of the buckets: `Cnt[c] := Bout + (keys below c)`. -/
def pfxBody : Program :=
  seq (loadTo 41 40) (seq (storeTo 40 43) (seq (addTo 43 43 41) (seq (addTo 40 40 1)
  (subTo 39 39 1))))

/-- Place every `x` at the next free cell of its bucket. -/
def plcBody : Program :=
  seq (loadTo 41 40) (seq (addTo 42 41 37) (seq (loadTo 42 42) (seq (addTo 42 42 35)
  (seq (loadTo 44 42) (seq (storeTo 44 41) (seq (addTo 44 44 1) (seq (storeTo 42 44)
  (seq (addTo 40 40 1) (subTo 39 39 1)))))))))

/-- Start a pass over the array. -/
def arrPre : Program := seq (copyTo 39 31) (copyTo 40 30)

/-- Start the prefix sums. -/
def pfxPre : Program := seq (copyTo 39 34) (seq (copyTo 40 35) (copyTo 43 36))

theorem runsTo_arrPre (M : Mem) :
    RunsTo arrPre (fun m => m = M) (fun m => m = (M.update 39 (M 31)).update 40 (M 30)) 2 := by
  unfold arrPre; rt; rfl

theorem runsTo_pfxPre (M : Mem) :
    RunsTo pfxPre (fun m => m = M)
      (fun m => m = ((M.update 39 (M 34)).update 40 (M 35)).update 43 (M 36)) 3 := by
  unfold pfxPre; rt; rfl

/-- **One pass of a stable counting sort** of the array at `R30` (length `R31`) by the field
at offset `R37`, keys below `R34`, in the region at `R35`. -/
def csP : Program :=
  seq (addTo 36 35 34) (seq (Arrays.fillZero 35 34 45) (seq arrPre (seq (whileNz 39 cntBody)
  (seq pfxPre (seq (whileNz 39 pfxBody) (seq arrPre (seq (whileNz 39 plcBody)
  (Arrays.copyBlock 36 30 31 45))))))))

theorem wf_csP : Wf csP := by
  unfold csP cntBody pfxBody plcBody arrPre pfxPre Arrays.fillZero Arrays.fillPre Arrays.fillBody
    Arrays.copyBlock Arrays.copyPre Arrays.copyBody
  wf_tac

section Pass

variable (M0 : Mem) (xs : List ℕ) (A Cnt K d : ℕ)

/-- The key of a record. -/
abbrev keyOf (x : ℕ) : ℕ := M0 (x + d)

/-- The count loop after `t` entries. -/
def CntI (M1 : Mem) (t : ℕ) (m : Mem) : Prop :=
  t ≤ xs.length ∧ m 39 = xs.length - t ∧ m 40 = A + t ∧
  (∀ c < K, m (Cnt + c) = ((xs.take t).filter (fun x => keyOf M0 d x = c)).length) ∧
  Keep [39, 40, 41, 42] Cnt (Cnt + K) M1 m

theorem runsTo_cntBody {M1 m : Mem} {t : ℕ} (ht : t < xs.length) (hI : CntI M0 xs A Cnt K d M1 t m)
    (hA : Blk M1 A xs) (hkey : ∀ x ∈ xs, M1 (x + d) = M0 (x + d)) (hK : ∀ x ∈ xs, keyOf M0 d x < K)
    (hrec : ∀ x ∈ xs, 50 ≤ x + d ∧ x + d < A) (hACnt : A + xs.length ≤ Cnt) (h50 : 50 ≤ A)
    (h1 : M1 1 = 1) (h35 : M1 35 = Cnt) (h37 : M1 37 = d) :
    RunsTo cntBody (fun m' => m' = m) (CntI M0 xs A Cnt K d M1 (t + 1)) 9 := by
  obtain ⟨-, e39, e40, hcnt, hk⟩ := hI
  have g : ∀ z, z ≠ 39 → z ≠ 40 → z ≠ 41 → z ≠ 42 → z < Cnt → m z = M1 z := fun z a b c e f =>
    hk z (by simp; omega) (Or.inl f)
  have hx : m (A + t) = xs[t] := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA t ht
  have hmem : xs[t] ∈ xs := List.getElem_mem ht
  have hkx : m (xs[t] + d) = keyOf M0 d xs[t] := by
    have := hrec _ hmem
    rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), hkey _ hmem]
  have hc0 := hK _ hmem
  have hr := hrec _ hmem
  set c0 := keyOf M0 d xs[t] with hc0def
  have c1 : m 1 = 1 := by rw [g 1 (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have c35 : m 35 = Cnt := by rw [g 35 (by omega) (by omega) (by omega) (by omega) (by omega), h35]
  have c37 : m 37 = d := by rw [g 37 (by omega) (by omega) (by omega) (by omega) (by omega), h37]
  unfold cntBody
  rt
  unfold CntI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e40, e39, c1, c35, c37, hx, hkx]
  refine ⟨by omega, by omega, by omega, fun c hc => ?_, ?_⟩
  · rw [filter_take_succ ht, List.length_append, ← hcnt c hc]
    by_cases hcc : c = c0
    · subst hcc
      rw [show c0 + Cnt = Cnt + c0 by omega, Mem.update_self, ← hc0def]
      simp
    · have hne : Cnt + c ≠ c0 + Cnt := by omega
      rw [Mem.update_of_ne _ _ hne]
      simp (disch := omega) only [Mem.update_of_ne]
      have : ¬ (keyOf M0 d xs[t] = c) := fun e => hcc (by rw [← e])
      simp [this]
  · intro z hz hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hk z (by simp; omega) hab

/-- The prefix-sum loop after `t` buckets. -/
def PfxI (M2 : Mem) (t : ℕ) (m : Mem) : Prop :=
  t ≤ K ∧ m 39 = K - t ∧ m 40 = Cnt + t ∧
  m 43 = Cnt + K + (csortL (keyOf M0 d) t xs).length ∧
  (∀ c < t, m (Cnt + c) = Cnt + K + (csortL (keyOf M0 d) c xs).length) ∧
  (∀ c, t ≤ c → c < K → m (Cnt + c) = M2 (Cnt + c)) ∧
  Keep [39, 40, 41, 43] Cnt (Cnt + K) M2 m

theorem runsTo_pfxBody {M2 m : Mem} {t : ℕ} (ht : t < K) (hI : PfxI M0 xs Cnt K d M2 t m)
    (hcnt : ∀ c < K, M2 (Cnt + c) = (xs.filter (fun x => keyOf M0 d x = c)).length)
    (h50 : 50 ≤ Cnt) (h1 : M2 1 = 1) :
    RunsTo pfxBody (fun m' => m' = m) (PfxI M0 xs Cnt K d M2 (t + 1)) 5 := by
  obtain ⟨-, e39, e40, e43, hlo, hhi, hk⟩ := hI
  have c1 : m 1 = 1 := by rw [hk 1 (by simp) (by omega), h1]
  have hv : m (Cnt + t) = (xs.filter (fun x => keyOf M0 d x = t)).length := by
    rw [hhi t le_rfl ht, hcnt t ht]
  unfold pfxBody
  rt
  unfold PfxI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e40, e39, e43, c1, hv]
  refine ⟨by omega, by omega, by omega, by rw [length_csortL_succ]; ring, fun c hc => ?_,
    fun c hc1 hc2 => ?_, ?_⟩
  · rcases Nat.lt_or_ge c t with h | h
    · simp (disch := omega) only [Mem.update_of_ne]; exact hlo c h
    · obtain rfl : c = t := by omega
      simp (disch := omega) only [Mem.update_self]
  · simp (disch := omega) only [Mem.update_of_ne]; exact hhi c (by omega) hc2
  · intro z hz hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hk z (by simp; omega) hab

/-- The placement loop after `t` entries. -/
def PlcI (M3 : Mem) (t : ℕ) (m : Mem) : Prop :=
  t ≤ xs.length ∧ m 39 = xs.length - t ∧ m 40 = A + t ∧
  (∀ c < K, m (Cnt + c) = Cnt + K + (csortL (keyOf M0 d) c xs).length +
    ((xs.take t).filter (fun x => keyOf M0 d x = c)).length) ∧
  (∀ c < K, Blk m (Cnt + K + (csortL (keyOf M0 d) c xs).length)
    ((xs.take t).filter (fun x => keyOf M0 d x = c))) ∧
  Keep [39, 40, 41, 42, 44] Cnt (Cnt + K + xs.length) M3 m

theorem length_filter_take_le (xs : List ℕ) (t : ℕ) (P : ℕ → Bool) :
    ((xs.take t).filter P).length ≤ (xs.filter P).length :=
  ((List.take_sublist _ _).filter P).length_le

theorem runsTo_plcBody {M3 m : Mem} {t : ℕ} (ht : t < xs.length) (hI : PlcI M0 xs A Cnt K d M3 t m)
    (hA : Blk M3 A xs) (hkey : ∀ x ∈ xs, M3 (x + d) = M0 (x + d)) (hK : ∀ x ∈ xs, keyOf M0 d x < K)
    (hrec : ∀ x ∈ xs, 50 ≤ x + d ∧ x + d < A) (hACnt : A + xs.length ≤ Cnt) (h50 : 50 ≤ A)
    (h1 : M3 1 = 1) (h35 : M3 35 = Cnt) (h37 : M3 37 = d) :
    RunsTo plcBody (fun m' => m' = m) (PlcI M0 xs A Cnt K d M3 (t + 1)) 10 := by
  obtain ⟨-, e39, e40, hpos, hblk, hk⟩ := hI
  have g : ∀ z, z ≠ 39 → z ≠ 40 → z ≠ 41 → z ≠ 42 → z ≠ 44 → z < Cnt → m z = M3 z :=
    fun z a b c e f h => hk z (by simp; omega) (Or.inl h)
  have hx : m (A + t) = xs[t] := by
    rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hA t ht
  have hmem : xs[t] ∈ xs := List.getElem_mem ht
  have hc0 := hK _ hmem
  have hr := hrec _ hmem
  have hkx : m (xs[t] + d) = keyOf M0 d xs[t] := by
    rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hkey _ hmem]
  set c0 := keyOf M0 d xs[t] with hc0def
  have c1 : m 1 = 1 := by
    rw [g 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  have c35 : m 35 = Cnt := by
    rw [g 35 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h35]
  have c37 : m 37 = d := by
    rw [g 37 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h37]
  -- the position of the entry
  set st := fun c => (csortL (keyOf M0 d) c xs).length with hst
  set f := fun c => ((xs.take t).filter (fun x => keyOf M0 d x = c)).length with hf
  have hf0 : f c0 < (xs.filter (fun x => keyOf M0 d x = c0)).length :=
    length_filter_take_lt ht (P := fun x => decide (keyOf M0 d x = c0)) (by simp [c0])
  have hstc : ∀ c, st (c + 1) = st c + (xs.filter (fun x => keyOf M0 d x = c)).length :=
    fun c => length_csortL_succ _ _ _
  have hstmono : ∀ c c', c ≤ c' → st c ≤ st c' := fun c c' h => length_csortL_le h
  have hstK : st K = xs.length := length_csortL_of_lt hK
  have hfle : ∀ c, f c ≤ (xs.filter (fun x => keyOf M0 d x = c)).length :=
    fun c => length_filter_take_le xs t _
  have hpos0 : m (Cnt + c0) = Cnt + K + st c0 + f c0 := hpos c0 hc0
  have hend : st c0 + f c0 < xs.length := by
    have := hstc c0; have := hstmono (c0 + 1) K (by omega); omega
  unfold plcBody
  rt
  unfold PlcI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e40, e39, c1, c35, c37, hx, hkx,
    show c0 + Cnt = Cnt + c0 by omega, hpos0]
  refine ⟨by omega, by omega, by omega, fun c hc => ?_, fun c hc => ?_, ?_⟩
  · rw [filter_take_succ ht, List.length_append]
    by_cases hcc : c = c0
    · subst hcc
      rw [Mem.update_self, ← hc0def]
      simp [f, st]; ring
    · have hne : Cnt + c ≠ Cnt + c0 := by omega
      rw [Mem.update_of_ne _ _ hne]
      simp (disch := omega) only [Mem.update_of_ne]
      have : ¬ (keyOf M0 d xs[t] = c) := fun e => hcc (by rw [← e])
      rw [hpos c hc]; simp [this]
  · rw [filter_take_succ ht]
    by_cases hcc : c = c0
    · subst hcc
      rw [if_pos (by simp [c0]), Blk.append, Blk.cons]
      refine ⟨?_, ?_, Blk.nil _ _⟩
      · refine (hblk c0 hc).congr (fun z h1 h2 => ?_)
        have : f c0 = ((xs.take t).filter (fun x => keyOf M0 d x = c0)).length := rfl
        have : st c0 = (csortL (keyOf M0 d) c0 xs).length := rfl
        simp (disch := omega) only [Mem.update_of_ne]
      · simp (disch := omega) only [Mem.update_of_ne]
        simp [f, st]
    · have : ¬ (keyOf M0 d xs[t] = c) := fun e => hcc (by rw [← e])
      rw [if_neg (by simpa using this), List.append_nil]
      refine (hblk c hc).congr (fun z h1 h2 => ?_)
      have hfc := hfle c
      have hsep : z ≠ Cnt + K + st c0 + f c0 := by
        rcases Nat.lt_or_gt_of_ne hcc with h | h
        · have := hstc c; have := hstmono (c + 1) c0 (by omega)
          change z < Cnt + K + st c + f c at h2; omega
        · have := hstc c0; have := hstmono (c0 + 1) c (by omega)
          change Cnt + K + st c ≤ z at h1; omega
      simp (disch := omega) only [Mem.update_of_ne]
  · intro z hz hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hk z (by simp; omega) hab

/-- The registers of the sort routine. -/
def sortW : List ℕ := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]

/-- The registers one pass writes. -/
def csW : List ℕ := [36, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]

/-- The step count of one pass. -/
def tCs (K len : ℕ) : ℕ := 12 * K + 30 * len + 21

/-- **One pass of counting sort**: the array at `A` holds `csortL key K xs` afterwards, where
`key x` is the field at offset `d` of the record `x`. -/
theorem runsTo_csP (hA : Blk M0 A xs) (hK : ∀ x ∈ xs, keyOf M0 d x < K)
    (hrec : ∀ x ∈ xs, 50 ≤ x + d ∧ x + d < A) (hACnt : A + xs.length ≤ Cnt) (h50 : 50 ≤ A)
    (h1 : M0 1 = 1) (h30 : M0 30 = A) (h31 : M0 31 = xs.length) (h34 : M0 34 = K)
    (h35 : M0 35 = Cnt) (h37 : M0 37 = d) :
    RunsTo csP (fun m => m = M0) (fun m => Blk m A (csortL (keyOf M0 d) K xs) ∧
      Keep csW A (Cnt + K + xs.length) M0 m) (tCs K xs.length) := by
  set len := xs.length with hlen
  unfold csP
  refine RunsTo.mono (T := (5 * K + 5 + (2 + ((len * (9 + 2) + 1) + (3 + ((K * (5 + 2) + 1) +
    (2 + ((len * (10 + 2) + 1) + (7 * len + 5)))))))) + 1) ?_ (by unfold tCs; ring_nf; omega)
  refine add_seq' ?_
  set Ma := M0.update 36 (M0 35 + M0 34) with hMa
  have ha36 : Ma 36 = Cnt + K := by rw [hMa, Mem.update_self, h35, h34]
  have haK : ∀ z, z ≠ 36 → Ma z = M0 z := fun z hz => Mem.update_of_ne _ _ hz
  -- zero the counts
  refine block_seq ((Arrays.runsTo_fillZero 35 34 45 (by omega) (by omega) Ma
    (by rw [haK 35 (by omega), h35]; omega)).mono (by rw [haK 34 (by omega), h34])) (fun M1 ⟨z1, k1⟩ => ?_)
  rw [haK 35 (by omega), haK 34 (by omega), h35, h34] at z1 k1
  have g1 : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M1 z = M0 z := fun z hz hab => by
    rw [k1 z (by omega) (by simp [sortW] at hz ⊢; omega), haK z (by simp [sortW] at hz; omega)]
  have g1' : M1 36 = Cnt + K := by rw [k1 36 (by omega) (by simp), ha36]
  -- start the count loop
  refine block_seq (runsTo_arrPre M1) (fun M1' hM1' => ?_)
  have r31 : M1 31 = len := by rw [g1 31 (by simp [sortW]) (by omega), h31]
  have r30 : M1 30 = A := by rw [g1 30 (by simp [sortW]) (by omega), h30]
  have gM1' : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M1' z = M0 z := fun z hz hab => by
    rw [hM1', Mem.update_of_ne _ _ (by simp [sortW] at hz; omega),
      Mem.update_of_ne _ _ (by simp [sortW] at hz; omega), g1 z hz hab]
  have hA1 : Blk M1' A xs := hA.congr (fun z h1 h2 => gM1' z (by simp [sortW]; omega) (by omega))
  have hkey1 : ∀ x ∈ xs, M1' (x + d) = M0 (x + d) := fun x hx => by
    have := hrec x hx; exact gM1' _ (by simp [sortW]; omega) (by omega)
  have i0 : CntI M0 xs A Cnt K d M1' 0 M1' := by
    refine ⟨by omega, by rw [hM1', Mem.update_of_ne _ _ (by omega), Mem.update_self, r31]; simp [hlen],
      by rw [hM1', Mem.update_self, r30]; simp, fun c hc => ?_, Keep.refl _ _ _ _⟩
    rw [hM1', Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega),
      z1 _ (by omega) (by omega)]
    simp
  have hloop1 := runsTo_countLoop (c := 39) (by unfold cntBody; wf_tac) (CntI M0 xs A Cnt K d M1')
    len 9 (fun t m hI => ⟨hI.2.1, hI.1⟩)
    (fun t m ht hI => runsTo_cntBody M0 xs A Cnt K d ht hI hA1 hkey1 hK hrec hACnt h50
      (by rw [gM1' 1 (by simp [sortW]) (by omega), h1])
      (by rw [gM1' 35 (by simp [sortW]) (by omega), h35])
      (by rw [hM1', Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega),
        k1 37 (by omega) (by simp), haK 37 (by omega), h37]))
    M1' i0
  refine block_seq hloop1 (fun M2 ⟨_, _, _, hc2, k2⟩ => ?_)
  rw [List.take_length] at hc2
  have g2 : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M2 z = M0 z := fun z hz hab => by
    rw [k2 z (by simp [sortW] at hz ⊢; omega) (by omega), gM1' z hz hab]
  have x36 : M2 36 = Cnt + K := by
    rw [k2 36 (by simp) (by omega), hM1', Mem.update_of_ne _ _ (by omega),
      Mem.update_of_ne _ _ (by omega), g1']
  have x37 : M2 37 = d := by
    rw [k2 37 (by simp) (by omega), hM1', Mem.update_of_ne _ _ (by omega),
      Mem.update_of_ne _ _ (by omega), k1 37 (by omega) (by simp), haK 37 (by omega), h37]
  -- the prefix sums
  refine block_seq (runsTo_pfxPre M2) (fun M2' hM2' => ?_)
  have e34 : M2 34 = K := by rw [g2 34 (by simp [sortW]) (by omega), h34]
  have e35 : M2 35 = Cnt := by rw [g2 35 (by simp [sortW]) (by omega), h35]
  have gM2' : ∀ z, z ≠ 39 → z ≠ 40 → z ≠ 43 → M2' z = M2 z := fun z a b c => by
    rw [hM2']; simp (disch := omega) only [Mem.update_of_ne]
  have j0 : PfxI M0 xs Cnt K d M2' 0 M2' := by
    refine ⟨by omega, ?_, ?_, ?_, fun c hc => absurd hc (by omega), fun c _ _ => rfl,
      Keep.refl _ _ _ _⟩
    · rw [hM2']; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, e34]; simp
    · rw [hM2']; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, e35]; simp
    · rw [hM2']; simp (disch := omega) only [Mem.update_self, x36]; simp
  have hloop2 := runsTo_countLoop (c := 39) (by unfold pfxBody; wf_tac) (PfxI M0 xs Cnt K d M2')
    K 5 (fun t m hI => ⟨hI.2.1, hI.1⟩)
    (fun t m ht hI => runsTo_pfxBody M0 xs Cnt K d ht hI
      (fun c hc => by rw [gM2' _ (by omega) (by omega) (by omega), hc2 c hc]) (by omega)
      (by rw [gM2' 1 (by omega) (by omega) (by omega), g2 1 (by simp [sortW]) (by omega), h1]))
    M2' j0
  refine block_seq hloop2 (fun M3 ⟨_, _, _, _, hp3, _, k3⟩ => ?_)
  have g3 : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M3 z = M0 z := fun z hz hab => by
    rw [k3 z (by simp [sortW] at hz ⊢; omega) (by omega),
      gM2' z (by simp [sortW] at hz; omega) (by simp [sortW] at hz; omega)
        (by simp [sortW] at hz; omega), g2 z hz hab]
  have y36 : M3 36 = Cnt + K := by
    rw [k3 36 (by simp) (by omega), gM2' 36 (by omega) (by omega) (by omega), x36]
  have y37 : M3 37 = d := by
    rw [k3 37 (by simp) (by omega), gM2' 37 (by omega) (by omega) (by omega), x37]
  -- the placement
  refine block_seq (runsTo_arrPre M3) (fun M3' hM3' => ?_)
  have gM3' : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M3' z = M0 z := fun z hz hab => by
    rw [hM3', Mem.update_of_ne _ _ (by simp [sortW] at hz; omega),
      Mem.update_of_ne _ _ (by simp [sortW] at hz; omega), g3 z hz hab]
  have hA3 : Blk M3' A xs := hA.congr (fun z h1 h2 => gM3' z (by simp [sortW]; omega) (by omega))
  have hkey3 : ∀ x ∈ xs, M3' (x + d) = M0 (x + d) := fun x hx => by
    have := hrec x hx; exact gM3' _ (by simp [sortW]; omega) (by omega)
  have l0 : PlcI M0 xs A Cnt K d M3' 0 M3' := by
    refine ⟨by omega, ?_, ?_, fun c hc => ?_, fun c _ => by simp; exact Blk.nil _ _,
      Keep.refl _ _ _ _⟩
    · rw [hM3']; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      rw [g3 31 (by simp [sortW]) (by omega), h31]; simp [hlen]
    · rw [hM3']; simp only [Mem.update_self]
      rw [g3 30 (by simp [sortW]) (by omega), h30]; simp
    · rw [hM3']; simp (disch := omega) only [Mem.update_of_ne]
      rw [hp3 c hc]; simp
  have hloop3 := runsTo_countLoop (c := 39) (by unfold plcBody; wf_tac) (PlcI M0 xs A Cnt K d M3')
    len 10 (fun t m hI => ⟨hI.2.1, hI.1⟩)
    (fun t m ht hI => runsTo_plcBody M0 xs A Cnt K d ht hI hA3 hkey3 hK hrec hACnt h50
      (by rw [gM3' 1 (by simp [sortW]) (by omega), h1])
      (by rw [gM3' 35 (by simp [sortW]) (by omega), h35])
      (by rw [hM3', Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega), y37]))
    M3' l0
  refine block_seq hloop3 (fun M4 ⟨_, _, _, _, hb4, k4⟩ => ?_)
  rw [List.take_length] at hb4
  have g4 : ∀ z, z ∉ sortW → (z < Cnt ∨ Cnt + K + len ≤ z) → M4 z = M0 z := fun z hz hab => by
    rw [k4 z (by simp [sortW] at hz ⊢; omega) (by omega), gM3' z hz hab]
  have hsorted : Blk M4 (Cnt + K) (csortL (keyOf M0 d) K xs) :=
    blk_csortL K (fun c hc => hb4 c hc)
  have hlenS : (csortL (keyOf M0 d) K xs).length = len := length_csortL_of_lt hK
  have z36 : M4 36 = Cnt + K := by
    rw [k4 36 (by simp) (by omega), hM3', Mem.update_of_ne _ _ (by omega),
      Mem.update_of_ne _ _ (by omega), y36]
  have z30 : M4 30 = A := by rw [g4 30 (by simp [sortW]) (by omega), h30]
  have z31 : M4 31 = len := by rw [g4 31 (by simp [sortW]) (by omega), h31]
  -- copy back
  refine ((Arrays.runsTo_copyBlock 36 30 31 45 (by omega) (by omega) (by omega) M4
    (by rw [z36]; omega) (by rw [z30]; omega) (by rw [z30, z36]; omega)).mono
    (by rw [z31])).weaken (fun m ⟨hc, hk⟩ => ⟨fun j hj => ?_, fun z hz hab => ?_⟩)
  · rw [hlenS] at hj
    rw [z30, z31, z36] at hc
    rw [hc j hj]
    exact hsorted j (by rw [hlenS]; exact hj)
  · rw [z30, z31] at hk
    rw [hk z (by omega) (by simp [csW] at hz ⊢; omega)]
    by_cases hz' : z ∈ sortW
    · have : z = 37 ∨ z = 38 := by simp [sortW, csW] at hz hz' ⊢; omega
      rcases this with rfl | rfl
      · rw [k4 37 (by simp) (by omega), hM3', Mem.update_of_ne _ _ (by omega),
          Mem.update_of_ne _ _ (by omega), y37, h37]
      · rw [k4 38 (by simp) (by omega), hM3', Mem.update_of_ne _ _ (by omega),
          Mem.update_of_ne _ _ (by omega), k3 38 (by simp) (by omega),
          gM2' 38 (by omega) (by omega) (by omega), k2 38 (by simp) (by omega), hM1',
          Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega),
          k1 38 (by omega) (by simp), haK 38 (by omega)]
    · exact g4 z hz' (by omega)

end Pass

/-! ## Radix sort -/

/-- The fields `f0, …, f0 + L - 1` of the record `x`, read in the memory `M`. -/
def recL (M : Mem) (f0 L x : ℕ) : List ℕ := (List.range L).map (fun j => M (x + f0 + j))

@[simp] theorem length_recL (M : Mem) (f0 L x : ℕ) : (recL M f0 L x).length = L := by simp [recL]

theorem drop_recL {M : Mem} {f0 L x j : ℕ} (hj : j < L) :
    (recL M f0 L x).drop j = M (x + f0 + j) :: (recL M f0 L x).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [recL]

/-- One radix pass: the next field, then one counting-sort pass. -/
def radBody : Program := seq (subTo 37 37 1) (seq csP (subTo 38 38 1))

/-- Start: the field past the last one, and the number of passes. -/
def radPre : Program := seq (addTo 37 32 33) (copyTo 38 33)

/-- **Radix sort** of the array at `R30` (length `R31`) by the fields `R32, …, R32 + R33 - 1`,
keys below `R34`, in the region at `R35`. -/
def radixP : Program := seq radPre (whileNz 38 radBody)

theorem wf_radBody : Wf radBody := by
  unfold radBody; exact wf_seq (by wf_tac) (wf_seq wf_csP (by wf_tac))

/-- The radix loop after `t` passes. -/
def RadI (M0 : Mem) (xs : List ℕ) (A Cnt K f0 L : ℕ) (t : ℕ) (m : Mem) : Prop :=
  t ≤ L ∧ m 38 = L - t ∧ m 37 = f0 + L - t ∧
  (∃ ys, Blk m A ys ∧ ys.Perm xs ∧
    ys.Pairwise (fun a b => (recL M0 f0 L a).drop (L - t) ≤ (recL M0 f0 L b).drop (L - t))) ∧
  Keep sortW A (Cnt + K + xs.length) M0 m

theorem runsTo_radBody {M0 m : Mem} {xs : List ℕ} {A Cnt K f0 L t : ℕ} (ht : t < L)
    (hI : RadI M0 xs A Cnt K f0 L t m)
    (hK : ∀ x ∈ xs, ∀ j < L, M0 (x + f0 + j) < K)
    (hrec : ∀ x ∈ xs, ∀ j < L, 50 ≤ x + f0 + j ∧ x + f0 + j < A) (hACnt : A + xs.length ≤ Cnt)
    (h50 : 50 ≤ A) (h1 : M0 1 = 1) (h30 : M0 30 = A) (h31 : M0 31 = xs.length) (h34 : M0 34 = K)
    (h35 : M0 35 = Cnt) :
    RunsTo radBody (fun m' => m' = m) (RadI M0 xs A Cnt K f0 L (t + 1))
      ((tCs K xs.length + 1) + 1) := by
  obtain ⟨-, e38, e37, ⟨ys, hys, hperm, hpw⟩, hk⟩ := hI
  have g : ∀ z, z < 36 → m z = M0 z := fun z hz => hk z (by simp [sortW]; omega) (by omega)
  set j := L - t - 1 with hj
  have hLt : L - t = j + 1 := by omega
  unfold radBody
  refine sub_seq' ?_
  set m1 := m.update 37 (m 37 - m 1) with hm1
  have hd : m1 37 = f0 + j := by rw [hm1, Mem.update_self, e37, g 1 (by omega), h1]; omega
  have hlen : ys.length = xs.length := hperm.length_eq
  have hmem : ∀ x ∈ ys, x ∈ xs := fun x hx => hperm.subset hx
  have hkey : ∀ x ∈ ys, keyOf m1 (f0 + j) x = M0 (x + f0 + j) := fun x hx => by
    have := hrec x (hmem x hx) j (by omega)
    show m1 (x + (f0 + j)) = _
    rw [hm1, Mem.update_of_ne _ _ (by omega), hk _ (by simp [sortW]; omega) (by omega),
      Nat.add_assoc]
  have hcs := runsTo_csP m1 ys A Cnt K (f0 + j)
    (hys.update (by omega)) (fun x hx => by rw [hkey x hx]; exact hK x (hmem x hx) j (by omega))
    (fun x hx => by have := hrec x (hmem x hx) j (by omega); omega) (by omega) h50
    (by rw [hm1, Mem.update_of_ne _ _ (by omega), g 1 (by omega), h1])
    (by rw [hm1, Mem.update_of_ne _ _ (by omega), g 30 (by omega), h30])
    (by rw [hm1, Mem.update_of_ne _ _ (by omega), g 31 (by omega), h31, hlen])
    (by rw [hm1, Mem.update_of_ne _ _ (by omega), g 34 (by omega), h34])
    (by rw [hm1, Mem.update_of_ne _ _ (by omega), g 35 (by omega), h35]) hd
  rw [hlen] at hcs
  refine block_seq hcs (fun m2 ⟨hb2, hk2⟩ => ?_)
  refine sub_last' ?_
  have h38 : m2 38 = L - t := by
    rw [hk2 38 (by simp [csW]) (by omega), hm1, Mem.update_of_ne _ _ (by omega), e38]
  have h37' : m2 37 = f0 + j := by rw [hk2 37 (by simp [csW]) (by omega), hd]
  have h1' : m2 1 = 1 := by
    rw [hk2 1 (by simp [csW]) (by omega), hm1, Mem.update_of_ne _ _ (by omega), g 1 (by omega), h1]
  have hKys : ∀ x ∈ ys, keyOf m1 (f0 + j) x < K := fun x hx => by
    rw [hkey x hx]; exact hK x (hmem x hx) j (by omega)
  refine ⟨by omega, by rw [Mem.update_self, h38, h1']; omega,
    by rw [Mem.update_of_ne _ _ (by omega), h37']; omega,
    ⟨csortL (keyOf m1 (f0 + j)) K ys, hb2.update (by omega), (csortL_perm hKys).trans hperm, ?_⟩,
    fun z hz hab => ?_⟩
  · have hpw' := csortL_pairwise (key := keyOf m1 (f0 + j)) (K := K) hpw
    refine hpw'.imp_of_mem (fun {a b} ha hb hab => ?_)
    have ha' := (mem_csortL.1 ha).1
    have hb' := (mem_csortL.1 hb).1
    rw [hkey a ha', hkey b hb'] at hab
    rw [show L - (t + 1) = j by omega, drop_recL (x := a) (j := j) (by omega),
      drop_recL (x := b) (j := j) (by omega), cons_le_cons_iff']
    rw [hLt] at hab
    exact hab
  · simp only [sortW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ (by omega), hk2 z (by simp [csW]; omega) hab, hm1,
      Mem.update_of_ne _ _ (by omega), hk z (by simp [sortW]; omega) hab]

theorem runsTo_radPre (M : Mem) :
    RunsTo radPre (fun m => m = M)
      (fun m => m = (M.update 37 (M 32 + M 33)).update 38 (M 33)) 2 := by
  unfold radPre; rt; rfl

/-- The step count of radix sort. -/
def tRadix (K len L : ℕ) : ℕ := L * (tCs K len + 4) + 3

/-- **Radix sort.**  Afterwards the array at `A` holds a permutation of `xs`, sorted by the
fields `f0, …, f0 + L - 1` (lexicographically). -/
theorem runsTo_radixP {M0 : Mem} {xs : List ℕ} {A Cnt K f0 L : ℕ} (hA : Blk M0 A xs)
    (hK : ∀ x ∈ xs, ∀ j < L, M0 (x + f0 + j) < K)
    (hrec : ∀ x ∈ xs, ∀ j < L, 50 ≤ x + f0 + j ∧ x + f0 + j < A) (hACnt : A + xs.length ≤ Cnt)
    (h50 : 50 ≤ A) (h1 : M0 1 = 1) (h30 : M0 30 = A) (h31 : M0 31 = xs.length) (h32 : M0 32 = f0)
    (h33 : M0 33 = L) (h34 : M0 34 = K) (h35 : M0 35 = Cnt) :
    RunsTo radixP (fun m => m = M0) (fun m =>
      (∃ ys, Blk m A ys ∧ ys.Perm xs ∧ ys.Pairwise (fun a b => recL M0 f0 L a ≤ recL M0 f0 L b)) ∧
      Keep sortW A (Cnt + K + xs.length) M0 m) (tRadix K xs.length L) := by
  unfold radixP tRadix
  refine RunsTo.mono (T := 2 + (L * (((tCs K xs.length + 1) + 1) + 2) + 1)) ?_ (by ring_nf; omega)
  refine block_seq (runsTo_radPre M0) (fun M1 hM1 => ?_)
  have i0 : RadI M0 xs A Cnt K f0 L 0 M1 := by
    refine ⟨by omega, by rw [hM1, Mem.update_self, h33]; rfl,
      by rw [hM1, Mem.update_of_ne _ _ (by omega), Mem.update_self, h32, h33]; rfl,
      ⟨xs, hA.congr (fun z h1 h2 => ?_), List.Perm.refl _, ?_⟩, fun z hz hab => ?_⟩
    · have := hrec
      rw [hM1, Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega)]
    · refine List.pairwise_of_forall_mem_list (fun a _ b _ => ?_)
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.drop_eq_nil_of_le (by simp)]
    · simp only [sortW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hM1, Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega)]
  have g1 : ∀ z, z < 36 → M1 z = M0 z := fun z hz => by
    rw [hM1, Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega)]
  refine (runsTo_countLoop (c := 38) wf_radBody (RadI M0 xs A Cnt K f0 L) L
    ((tCs K xs.length + 1) + 1) (fun t m hI => ⟨hI.2.1, hI.1⟩)
    (fun t m ht hI => runsTo_radBody ht hI hK hrec hACnt h50 h1 h30 h31 h34 h35) M1 i0).weaken
    (fun m ⟨_, _, _, ⟨ys, hb, hp, hpw⟩, hk⟩ => ⟨⟨ys, hb, hp, ?_⟩, hk⟩)
  simpa using hpw

/-! ## Dense ranks along a sorted array -/

/-- The differences of two sequences, summed over the first `j` places. -/
def dsum (a b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => dsum a b j + (a j - b j) + (b j - a j)

theorem dsum_eq_zero_iff (a b : ℕ → ℕ) : ∀ j, dsum a b j = 0 ↔ ∀ i < j, a i = b i
  | 0 => by simp [dsum]
  | j + 1 => by
      rw [dsum]
      constructor
      · intro h i hi
        rcases Nat.lt_or_ge i j with h' | h'
        · exact (dsum_eq_zero_iff a b j).1 (by omega) i h'
        · obtain rfl : i = j := by omega
          omega
      · intro h
        have h1 := (dsum_eq_zero_iff a b j).2 (fun i hi => h i (by omega))
        have h2 := h j (by omega)
        omega

theorem recL_eq_iff {M : Mem} {f0 L x y : ℕ} :
    recL M f0 L x = recL M f0 L y ↔ ∀ j < L, M (x + f0 + j) = M (y + f0 + j) := by
  unfold recL
  constructor
  · intro h j hj
    have := congrArg (fun l => l[j]?) h
    simpa [List.getElem?_map, List.getElem?_range hj] using this
  · intro h
    exact List.map_congr_left (fun j hj => h j (List.mem_range.1 hj))

/-- Compare the fields of the records `R39` and `R41`: `R42` becomes `0` exactly when they
agree. -/
def cmpBody : Program :=
  seq (loadTo 46 43) (seq (loadTo 47 44) (seq (subTo 48 46 47) (seq (addTo 42 42 48)
  (seq (subTo 48 47 46) (seq (addTo 42 42 48) (seq (addTo 43 43 1) (seq (addTo 44 44 1)
  (subTo 45 45 1))))))))

def cmpPre : Program := seq (assign 42 0) (seq (addTo 43 39 32) (seq (addTo 44 41 32) (copyTo 45 33)))

/-- One record of the scan: compare it with the previous one, bump the rank if they differ,
write the rank. -/
def rkBody : Program :=
  seq (loadTo 41 36) (seq (seq cmpPre (whileNz 45 cmpBody)) (seq (ifz 42 (addTo 38 38 1) [])
  (seq (addTo 40 41 34) (seq (storeTo 40 38) (seq (copyTo 39 41) (seq (addTo 36 36 1)
  (subTo 37 37 1)))))))

/-- The first record: rank `0`. -/
def rkPre : Program :=
  seq (copyTo 36 30) (seq (subTo 37 31 1) (seq (assign 38 0) (seq (loadTo 39 36)
  (seq (addTo 40 39 34) (seq (storeTo 40 38) (addTo 36 36 1))))))

/-- **Dense ranks**: along the sorted array at `R30` (length `R31`), write into the field at
offset `R34` of every record the number of distinct values of the fields `R32, …,
R32 + R33 - 1` below its own. -/
def rankP : Program := ifz 31 (seq rkPre (whileNz 37 rkBody)) []

theorem wf_cmpBody : Wf cmpBody := by unfold cmpBody; wf_tac

theorem wf_rkBody : Wf rkBody := by
  unfold rkBody cmpPre
  exact wf_seq (by wf_tac) (wf_seq (wf_seq (by wf_tac) (wf_whileNz wf_cmpBody)) (by wf_tac))

/-- The registers of the scan. -/
def rkW : List ℕ := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]

section Rank

variable (M0 : Mem) (ys : List ℕ) (f0 L g : ℕ)

/-- The memory agrees with `M0` except at the scan's registers and the rank fields. -/
def RkFrame (m : Mem) : Prop := ∀ z, z ∉ rkW → (∀ x ∈ ys, z ≠ x + g) → m z = M0 z

/-- The compare loop after `j` fields. -/
def CmpI (p c : ℕ) (m0 : Mem) (j : ℕ) (m : Mem) : Prop :=
  j ≤ L ∧ m 45 = L - j ∧ m 43 = p + f0 + j ∧ m 44 = c + f0 + j ∧
  m 42 = dsum (fun i => M0 (p + f0 + i)) (fun i => M0 (c + f0 + i)) j ∧
  ∀ z, z ≠ 42 → z ≠ 43 → z ≠ 44 → z ≠ 45 → z ≠ 46 → z ≠ 47 → z ≠ 48 → m z = m0 z

theorem runsTo_cmpBody {p c : ℕ} {m0 m : Mem} {j : ℕ} (hj : j < L) (hI : CmpI M0 f0 L p c m0 j m)
    (hp : m0 (p + f0 + j) = M0 (p + f0 + j)) (hc : m0 (c + f0 + j) = M0 (c + f0 + j))
    (hp50 : 49 < p + f0 + j) (hc50 : 49 < c + f0 + j) (h1 : m0 1 = 1) :
    RunsTo cmpBody (fun m' => m' = m) (CmpI M0 f0 L p c m0 (j + 1)) 9 := by
  obtain ⟨-, e45, e43, e44, e42, hk⟩ := hI
  have c1 : m 1 = 1 := by rw [hk 1 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega), h1]
  have rp : m (p + f0 + j) = M0 (p + f0 + j) := by
    rw [hk _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hp]
  have rc : m (c + f0 + j) = M0 (c + f0 + j) := by
    rw [hk _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hc]
  unfold cmpBody
  rt
  unfold CmpI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e45, e43, e44, e42, c1, rp, rc]
  refine ⟨by omega, by omega, by ring, by ring, by simp only [dsum], fun z a b c d e f g' => ?_⟩
  simp (disch := omega) only [Mem.update_of_ne]
  exact hk z a b c d e f g'

theorem runsTo_cmp {p c : ℕ} {m0 : Mem} (h39 : m0 39 = p) (h41 : m0 41 = c) (h32 : m0 32 = f0)
    (h33 : m0 33 = L) (h1 : m0 1 = 1)
    (hp : ∀ j < L, m0 (p + f0 + j) = M0 (p + f0 + j) ∧ 49 < p + f0 + j)
    (hc : ∀ j < L, m0 (c + f0 + j) = M0 (c + f0 + j) ∧ 49 < c + f0 + j) :
    RunsTo (seq cmpPre (whileNz 45 cmpBody)) (fun m => m = m0) (CmpI M0 f0 L p c m0 L)
      (4 + (L * (9 + 2) + 1)) := by
  unfold cmpPre
  refine block_seq (P := seq (assign 42 0) (seq (addTo 43 39 32) (seq (addTo 44 41 32)
    (copyTo 45 33)))) (mid := CmpI M0 f0 L p c m0 0) ?_ (fun m1 hm1 => ?_)
  · rt
    unfold CmpI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h39, h41, h32, h33]
    refine ⟨by omega, by omega, by ring, by ring, rfl, fun z a b c d e f g' => ?_⟩
    simp (disch := omega) only [Mem.update_of_ne]
  · refine runsTo_countLoop (c := 45) wf_cmpBody (CmpI M0 f0 L p c m0) L 9
      (fun t m hI => ⟨hI.2.1, hI.1⟩)
      (fun t m ht hI => runsTo_cmpBody M0 f0 L ht hI (hp t ht).1 (hc t ht).1 (hp t ht).2
        (hc t ht).2 h1) m1 hm1

/-- The scan after the record at position `i`. -/
def RkI (A : ℕ) (i : ℕ) (m : Mem) : Prop :=
  ∃ hi : i < ys.length, m 36 = A + i + 1 ∧ m 37 = ys.length - 1 - i ∧
    m 38 = drank (ys.map (recL M0 f0 L)) (recL M0 f0 L ys[i]) ∧ m 39 = ys[i] ∧
    (∀ i' (h : i' ≤ i), m (ys[i'] + g) = drank (ys.map (recL M0 f0 L)) (recL M0 f0 L ys[i'])) ∧
    RkFrame M0 ys g m

theorem runsTo_rkBody {A i : ℕ} {m : Mem} (hi : i + 1 < ys.length) (hI : RkI M0 ys f0 L g A i m)
    (hA : Blk M0 A ys) (hs : ys.Pairwise (fun a b => recL M0 f0 L a ≤ recL M0 f0 L b))
    (hnd : ys.Nodup) (hrec : ∀ x ∈ ys, ∀ j < L, 50 ≤ x + f0 + j ∧ x + f0 + j < A)
    (hg : ∀ x ∈ ys, 50 ≤ x + g ∧ x + g < A)
    (hsep : ∀ x ∈ ys, ∀ x' ∈ ys, ∀ j < L, x + g ≠ x' + f0 + j)
    (h1 : M0 1 = 1) (h32 : M0 32 = f0) (h33 : M0 33 = L) (h34 : M0 34 = g) :
    RunsTo rkBody (fun m' => m' = m) (RkI M0 ys f0 L g A (i + 1))
      (((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1) := by
  obtain ⟨_, e36, e37, e38, e39, hw, hf⟩ := hI
  have hA50 : 50 < A := by have := hg _ (List.getElem_mem hi); omega
  have hW : ∀ z, z < 36 → m z = M0 z := fun z hz =>
    hf z (by simp [rkW]; omega) (fun x hx => by have := hg x hx; omega)
  have hcur : m (A + (i + 1)) = ys[i + 1] := by
    rw [hf _ (by simp [rkW]; omega) (fun x hx => by have := hg x hx; omega)]
    exact hA (i + 1) hi
  set R := ys.map (recL M0 f0 L) with hR
  have hRs : R.Pairwise (· ≤ ·) := by rw [hR, List.pairwise_map]; exact hs
  unfold rkBody
  refine load_seq' ?_
  set m1 := m.update 41 (m (m 36)) with hm1
  have r41 : m1 41 = ys[i + 1] := by
    rw [hm1, Mem.update_self, e36, show A + i + 1 = A + (i + 1) by ring, hcur]
  have r1 : ∀ z, z ≠ 41 → m1 z = m z := fun z hz => Mem.update_of_ne _ _ hz
  have hkeys : ∀ x ∈ ys, ∀ j < L, m1 (x + f0 + j) = M0 (x + f0 + j) ∧ 49 < x + f0 + j :=
    fun x hx j hj => by
      have := hrec x hx j hj
      refine ⟨?_, by omega⟩
      rw [r1 _ (by omega), hf _ (by simp [rkW]; omega) (fun x' hx' => (hsep x' hx' x hx j hj).symm)]
  have hmi : ys[i] ∈ ys := List.getElem_mem _
  have hmi1 : ys[i + 1] ∈ ys := List.getElem_mem _
  refine block_seq (runsTo_cmp M0 f0 L (p := ys[i]) (c := ys[i + 1]) (m0 := m1)
    (by rw [r1 39 (by omega), e39]) r41
    (by rw [r1 32 (by omega), hW 32 (by omega), h32]) (by rw [r1 33 (by omega), hW 33 (by omega), h33])
    (by rw [r1 1 (by omega), hW 1 (by omega), h1])
    (hkeys _ hmi) (hkeys _ hmi1)) (fun m2 ⟨_, _, _, _, e42, hk2⟩ => ?_)
  -- the rank of the next record
  have hsucc := drank_sorted_succ hRs (i := i) (by simp [hR]; omega)
  simp only [hR, List.getElem_map] at hsucc
  have hflag : m2 42 = 0 ↔ recL M0 f0 L ys[i + 1] = recL M0 f0 L ys[i] := by
    rw [e42, dsum_eq_zero_iff, recL_eq_iff]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  have g2 : ∀ z, z ≠ 41 → z ≠ 42 → z ≠ 43 → z ≠ 44 → z ≠ 45 → z ≠ 46 → z ≠ 47 → z ≠ 48 →
      m2 z = m z := fun z a b c d e f g' h' => by rw [hk2 z b c d e f g' h', r1 z a]
  have r38 : m2 38 = drank R (recL M0 f0 L ys[i]) := by
    rw [g2 38 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), e38]
  refine RunsTo.mono (T := 3 + 5) ?_ le_rfl
  refine block_seq (P := ifz 42 (addTo 38 38 1) []) (T := 3)
    (mid := fun m3 => m3 38 = drank R (recL M0 f0 L ys[i + 1]) ∧
      ∀ z, z ≠ 38 → m3 z = m2 z) ?_ (fun m3 ⟨e38', hk3⟩ => ?_)
  · by_cases h0 : m2 42 = 0
    · refine (ifz_eq' h0 (runsTo_nil (fun m hm => ?_)) (by wf_tac)).mono (by omega)
      subst hm
      refine ⟨?_, fun z _ => rfl⟩
      rw [r38, hsucc, if_pos (hflag.1 h0)]; rfl
    · refine (ifz_ne' h0 (runsTo_addTo 38 38 1 (fun m hm => ?_)) Algo.ExplLinear.wf_nil).mono (by omega)
      subst hm
      refine ⟨?_, fun z hz => Mem.update_of_ne _ _ hz⟩
      rw [Mem.update_self, r38, hsucc, if_neg (fun e => h0 (hflag.2 e)),
        g2 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hW 1 (by omega), h1]
  -- write the rank, move on
  have s34 : m3 34 = g := by
    rw [hk3 34 (by omega), g2 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hW 34 (by omega), h34]
  have s41 : m3 41 = ys[i + 1] := by
    rw [hk3 41 (by omega), hk2 41 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), r41]
  have s36 : m3 36 = A + i + 1 := by
    rw [hk3 36 (by omega), g2 36 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), e36]
  have s37 : m3 37 = ys.length - 1 - i := by
    rw [hk3 37 (by omega), g2 37 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), e37]
  have s1 : m3 1 = 1 := by
    rw [hk3 1 (by omega), g2 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hW 1 (by omega), h1]
  have hgi1 := hg _ hmi1
  refine add_seq' (store_seq' (copy_seq' (add_seq' (sub_last' ?_))))
  simp only [Mem.update_self]
  refine ⟨hi, ?_, ?_, ?_, ?_, fun i' hi' => ?_, fun z hz hne => ?_⟩
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, s36, s1]; ring
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, s37, s1]; omega
  · simp (disch := omega) only [Mem.update_of_ne, s41, s34]; exact e38'
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, s41, s34]
  · rcases Nat.eq_or_lt_of_le hi' with rfl | hlt
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, s41, s34]; exact e38'
    · have hne : ys[i'] + g ≠ ys[i + 1] + g := by
        intro e
        have := (List.Nodup.getElem_inj_iff hnd).1 (Nat.add_right_cancel e)
        omega
      have hgi := hg _ (List.getElem_mem (show i' < ys.length by omega))
      simp (disch := omega) only [Mem.update_of_ne, s41, s34]
      rw [hk3 _ (by omega), g2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      exact hw i' (by omega)
  · simp only [rkW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    have hz' : z ≠ ys[i + 1] + g := hne _ hmi1
    simp (disch := omega) only [Mem.update_of_ne, s41, s34]
    rw [hk3 z (by omega), g2 z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    exact hf z (by simp [rkW]; omega) hne

/-- The step count of the scan. -/
def tRank (len L : ℕ) : ℕ := len * (11 * L + 16) + 12

/-- **Dense ranks along a sorted array.**  Afterwards the field at offset `g` of every record
`x` of the array holds the number of distinct values of `recL M0 f0 L` below its own. -/
theorem runsTo_rankP {A : ℕ} (hA : Blk M0 A ys)
    (hs : ys.Pairwise (fun a b => recL M0 f0 L a ≤ recL M0 f0 L b))
    (hnd : ys.Nodup) (hrec : ∀ x ∈ ys, ∀ j < L, 50 ≤ x + f0 + j ∧ x + f0 + j < A)
    (hg : ∀ x ∈ ys, 50 ≤ x + g ∧ x + g < A)
    (hsep : ∀ x ∈ ys, ∀ x' ∈ ys, ∀ j < L, x + g ≠ x' + f0 + j)
    (h1 : M0 1 = 1) (h30 : M0 30 = A) (h31 : M0 31 = ys.length) (h32 : M0 32 = f0)
    (h33 : M0 33 = L) (h34 : M0 34 = g) :
    RunsTo rankP (fun m => m = M0) (fun m =>
      (∀ x ∈ ys, m (x + g) = drank (ys.map (recL M0 f0 L)) (recL M0 f0 L x)) ∧ RkFrame M0 ys g m)
      (tRank ys.length L) := by
  unfold rankP tRank
  rcases Nat.eq_zero_or_pos ys.length with h0 | hpos
  · have hnil : ys = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    refine (ifz_eq' (M := M0) (i := 31) (by rw [h31]; rfl) (runsTo_nil (fun m hm => ?_)) ?_).mono (by omega)
    · subst hm; exact ⟨fun x hx => absurd hx (by simp), fun z _ _ => rfl⟩
    · exact wf_seq (by unfold rkPre; wf_tac) (wf_whileNz wf_rkBody)
  · have hA50 : 50 < A := by have := hg _ (List.getElem_mem hpos); omega
    refine (ifz_ne' (M := M0) (i := 31) (by rw [h31]; omega) ?_ Algo.ExplLinear.wf_nil).mono
      (T := (7 + ((ys.length - 1) * ((((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1) + 2) + 1)) + 2)
      (by
        have : (ys.length - 1) * (((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1 + 2) ≤
            ys.length * (11 * L + 16) := by
          calc (ys.length - 1) * (((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1 + 2)
              ≤ ys.length * (((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1 + 2) :=
                Nat.mul_le_mul_right _ (by omega)
            _ = ys.length * (11 * L + 16) := by ring
        omega)
    have hy0 : ys[0] ∈ ys := List.getElem_mem hpos
    have hg0 := hg _ hy0
    have hA0 : M0 A = ys[0] := by simpa using hA 0 hpos
    have hdr0 : drank (ys.map (recL M0 f0 L)) (recL M0 f0 L ys[0]) = 0 := by
      have := drank_sorted_zero (L := ys.map (recL M0 f0 L)) (by rw [List.pairwise_map]; exact hs)
        (by simpa using hpos)
      simpa using this
    refine block_seq (P := rkPre) (mid := RkI M0 ys f0 L g A 0) ?_ (fun m1 hm1 => ?_)
    · unfold rkPre
      rt
      unfold RkI RkFrame
      simp only [Mem.update_self]
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h30, h1, h31, h34, hA0]
      refine ⟨hpos, trivial, by omega, by rw [hdr0], trivial, fun i' hi' => ?_, fun z hz hne => ?_⟩
      · obtain rfl : i' = 0 := by omega
        simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; rw [hdr0]
      · simp only [rkW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        have hz0 := hne _ hy0
        simp (disch := omega) only [Mem.update_of_ne]
    · refine (runsTo_countLoop (c := 37) wf_rkBody (RkI M0 ys f0 L g A) (ys.length - 1)
        (((4 + (L * (9 + 2) + 1)) + (3 + 5)) + 1)
        (fun t m ⟨ht, _, e37, _⟩ => ⟨by omega, by omega⟩)
        (fun t m ht hI => runsTo_rkBody M0 ys f0 L g (by omega) hI hA hs hnd hrec hg hsep h1 h32 h33
          h34) m1 hm1).weaken (fun m ⟨hi, _, _, _, _, hw, hf⟩ => ⟨fun x hx => ?_, hf⟩)
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hx
      exact hw i' (by omega)

end Rank

end WLFast

end Algo
