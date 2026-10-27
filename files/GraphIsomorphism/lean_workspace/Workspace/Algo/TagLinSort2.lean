/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  The sorting routine,
second part: one string, all strings, and the ranks.
-/
import Workspace.Algo.TagLinSort

/-!
# Sorting strings on the RAM: the outer loops

`runsTo_insertOne` processes one string (scan, then insert or record a duplicate),
`runsTo_vertexLoop` all of them, and `runsTo_sortProg` adds the positions and the ranks.  See
`Workspace/Algo/TagLinSort.lean` for the algorithm and the registers.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact

/-- The registers the sort writes. -/
notation "Wsort" => [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29,
  30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

/-- The state of the loop over the strings, after the strings `0, …, x - 1`. -/
structure VCtx (n SA A : ℕ) (str : ℕ → List ℕ) (M0 : Mem) (x : ℕ) (Dl : List ℕ) (m : Mem) :
    Prop where
  sort : SortCtx n SA A str Dl m
  keep : Keep Wsort A (A + n + n + n + n + n) M0 m
  r14 : m 14 = A + n + n + n + n + n
  r28 : m 28 = x
  xle : x ≤ n
  dlt : ∀ v ∈ Dl, v < x
  reps : ∀ y < x, ∃ v ∈ Dl, m (A + n + n + y) = v ∧ str v = str y

theorem length_le_of_lt {str : ℕ → List ℕ} {Dl : List ℕ} (hs : (Dl.map str).Pairwise (· < ·))
    {x : ℕ} (hx : ∀ v ∈ Dl, v < x) : Dl.length ≤ x := by
  have hnd : Dl.Nodup := by
    have : (Dl.map str).Nodup := hs.imp (fun h => ne_of_lt h)
    exact List.Nodup.of_map _ this
  have hsub : Dl.toFinset ⊆ Finset.range x := by
    intro v hv; simp only [List.mem_toFinset] at hv; simpa using hx v hv
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
  exact this


/-- A sort context lives below `A + 2n` and in the fixed registers. -/
theorem SortCtx.congr {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M m : Mem}
    (h : SortCtx n SA A str Dl M) {W : List ℕ} {b : ℕ} (hk : Keep W (A + n + n) b M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 20 ∧ z ≠ 21 ∧ z ≠ 22 ∧ z ≠ 23 ∧ z ≠ 24 ∧ z ≠ 25 ∧
      z ≠ 26 ∧ z ≠ 27) : SortCtx n SA A str Dl m := by
  have hA : 64 ≤ A := by have := h.env.hSA; have := h.env.hSAn; omega
  have hd : Dl.length ≤ n := by
    have hnd : Dl.Nodup := List.Nodup.of_map _ (h.sorted.imp (fun h => ne_of_lt h))
    have hsub : Dl.toFinset ⊆ Finset.range n := by
      intro v hv; rw [List.mem_toFinset] at hv; simpa using h.dlt v hv
    have := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
  refine ⟨h.env.of_keep hk (by omega) (fun z hz => by have := hW z hz; omega), ?_, ?_, h.dlt,
    h.sorted, ?_⟩
  · rw [hk 23 (fun h' => by have := hW 23 h'; omega) (by omega), h.r23]
  · exact Blk.congr h.blk (fun z hz1 hz2 => hk z (fun h' => by have := hW z h'; omega)
      (by omega))
  · intro i hi
    rw [hk _ (fun h' => by have := hW _ h'; omega) (by omega), h.lcps i hi]

theorem insMem_out {M : Mem} {A n d p x z : ℕ} (hpd : p ≤ d) (hdn : d < n) (hx : x < n)
    (hz : z < A ∨ A + n + n + n + n + n ≤ z) : insMem M A n d p x z = M z := by
  unfold insMem shiftMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem insMem_rep {M : Mem} {A n d p x y : ℕ} (hpd : p ≤ d) (hdn : d < n) (hyx : y ≠ x) :
    insMem M A n d p x (A + n + n + y) = M (A + n + n + y) := by
  unfold insMem shiftMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem wf_scanInit : Wf scanInit := by unfold scanInit; wf_tac

theorem wf_insertOne : Wf insertOne := by
  unfold insertOne
  exact wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_loadTo _ _) (wf_seq
    (Layout.wf_loadTo _ _) (wf_seq (wf_ifz (wf_seq wf_scanInit wf_scanLoop)
      (wf_seq (Layout.wf_assign _ _) (Layout.wf_assign _ _)))
      (wf_ifz wf_insertB (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_storeTo _ _))))))

/-- **One string.**  String `x` is scanned against the representatives and inserted, or
recorded as a duplicate, within `22 |s| + 81 d + 110` steps. -/
theorem runsTo_insertOne {n SA A : ℕ} {str : ℕ → List ℕ} {M0 M : Mem} {x : ℕ} {Dl : List ℕ}
    (hV : VCtx n SA A str M0 x Dl M) (hx : x < n) :
    RunsTo insertOne (fun m => m = M) (fun m => ∃ Dl', VCtx n SA A str M0 (x + 1) Dl'
      (m.update 28 (x + 1)) ∧ m 29 = M 29 ∧ m 28 = x)
      (22 * (str x).length + 81 * Dl.length + 110) := by
  have hS := hV.sort
  have hE := hS.env
  have hA : 64 ≤ A := by have := hE.hSA; have := hE.hSAn; omega
  have hdx : Dl.length ≤ x := length_le_of_lt hS.sorted hV.dlt
  set s := str x with hsdef
  set sp := M (SA + x) with hspdef
  have hsp : 64 ≤ sp := hE.sp64 x hx
  have hspA : sp + 1 + 2 * s.length ≤ A := hE.spA x hx
  have hss : StrAt M sp s := hE.strs x hx
  -- the string `x`
  set M1 := ((M.update 2 (SA + x)).update 30 sp).update 31 (2 * s.length) with hM1
  have hrun1 : RunsTo (addTo 2 20 28) (fun m => m = M) (fun m => m = M.update 2 (SA + x)) 1 :=
    runsTo_addTo 2 20 28 (fun m hm => by rw [hm, hE.r20, hV.r28])
  have hrun1b : RunsTo (loadTo 30 2) (fun m => m = M.update 2 (SA + x))
      (fun m => m = (M.update 2 (SA + x)).update 30 sp) 1 :=
    runsTo_loadTo 30 2 (fun m hm => by
      rw [hm, Mem.update_self, Mem.update_of_ne _ _ (by have := hE.hSA; omega)])
  have hrun1c : RunsTo (loadTo 31 30) (fun m => m = (M.update 2 (SA + x)).update 30 sp)
      (fun m => m = M1) 1 :=
    runsTo_loadTo 31 30 (fun m hm => by
      rw [hm, hM1, Mem.update_self, Mem.update_of_ne _ _ (by omega),
        Mem.update_of_ne _ _ (by omega), hss.1])
  have ho1 : Outside [2, 30, 31] M M1 := by rw [hM1]; outside_tac (Outside.refl [2, 30, 31] M)
  have e30 : M1 30 = sp := by rw [hM1]; simp (disch := omega) only [Mem.update_self,
    Mem.update_of_ne]
  have e31 : M1 31 = 2 * s.length := by rw [hM1, Mem.update_self]
  clear_value M1
  have hS1 : SortCtx n SA A str Dl M1 := hS.of_outside ho1 (by intro z hz; simp at hz; omega)
  have hss1 : StrAt M1 sp s := hss.congr (fun z hz1 hz2 => ho1 z (by simp; omega))
  have f28 : M1 28 = x := by rw [ho1 28 (by simp), hV.r28]
  -- the scan (or nothing, when the list is empty)
  obtain ⟨M3, t3, hrun3, ho3, hres, ht3⟩ : ∃ M3 t3, RunsTo (ifz 23 (seq scanInit scanLoop)
      (seq (assign 39 0) (assign 12 1))) (fun m => m = M1) (fun m => m = M3) t3 ∧
      Outside Wsc M1 M3 ∧ ScanRes str Dl s M3 ∧ t3 ≤ 22 * s.length + 70 * Dl.length + 77 := by
    by_cases hd : Dl.length = 0
    · refine ⟨(M1.update 39 0).update 12 1, 4, ?_, ?_, ?_, by omega⟩
      · refine ifz_eq' (by rw [hS1.r23]; exact hd) ?_ (wf_seq wf_scanInit wf_scanLoop)
        exact assign_seq' (assign_last' rfl)
      · outside_tac (Outside.refl Wsc M1)
      · refine Or.inr ⟨by simp, ?_, fun i' hi' => ?_, fun i' _ h => by omega, fun h => ?_,
          fun h => ?_⟩
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne] at hi'; omega
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne] at h; omega
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne] at h; omega
    · set M2 := (((M1.update 32 0).update 33 0).update 34 0).update 38 1 with hM2
      have hrun2 : RunsTo scanInit (fun m => m = M1) (fun m => m = M2) 4 := by
        unfold scanInit; exact assign_seq' (assign_seq' (assign_seq' (assign_last' rfl)))
      have hI2 : ScanInv M1 str Dl s M2 := by
        refine ⟨by rw [hM2]; outside_tac (Outside.refl Wsc M1), by rw [hM2, Mem.update_self],
          fun _ => ?_, fun h => by rw [hM2, Mem.update_self] at h; omega⟩
        unfold ScanPos
        simp (disch := omega) only [hM2, Mem.update_self, Mem.update_of_ne]
        refine ⟨by omega, 0, rfl, by omega, by omega, fun j hj => by omega,
          fun i' hi' => by omega, fun h => by omega⟩
      obtain ⟨t, ht⟩ := runsTo_scanLoop hS1 e30 e31 hsp hspA hss1 M2 hI2
      obtain ⟨M3, ⟨⟨ho3, _, _, hres3⟩, h38, hpot⟩, hrun3⟩ := ht.exact
      refine ⟨M3, 4 + t + 2, ifz_ne' (by rw [hS1.r23]; exact hd) (hrun2.seq hrun3)
        (wf_seq (Layout.wf_assign _ _) (Layout.wf_assign _ _)), ho3, hres3 h38, ?_⟩
      have : scanPot Dl s M2 = 22 * s.length + 70 * Dl.length + 70 := by
        unfold scanPot; simp (disch := omega) only [hM2, Mem.update_self, Mem.update_of_ne]
        omega
      omega
  have hS3 : SortCtx n SA A str Dl M3 := hS1.of_outside ho3 (by intro z hz; simp at hz; omega)
  have g28 : M3 28 = x := by rw [ho3 28 (by simp), f28]
  have g29 : M3 29 = M 29 := by rw [ho3 29 (by simp), ho1 29 (by simp)]
  have g14 : M3 14 = M 14 := by rw [ho3 14 (by simp), ho1 14 (by simp)]
  have hk13 : Keep Wsort A (A + n + n + n + n + n) M M3 :=
    Keep.of_outside ((ho1.trans ho3).mono (by intro z hz; simp at hz ⊢; omega))
  have hkeep3 : Keep Wsort A (A + n + n + n + n + n) M0 M3 :=
    hV.keep.trans hk13 (fun z hz => hz) le_rfl le_rfl
  have hrep3 : ∀ y, M3 (A + n + n + y) = M (A + n + n + y) := fun y => by
    rw [ho3 _ (by simp; omega), ho1 _ (by simp; omega)]
  have hdn : Dl.length < n := by omega
  have e1 := hS3.env.one
  have eBound : ∀ t4 : ℕ, t4 ≤ 11 * Dl.length + 22 →
      1 + (1 + (1 + (t3 + t4))) ≤ 22 * (str x).length + 81 * Dl.length + 110 := by
    intro t4 ht4; rw [← hsdef]; omega
  -- insert, or record the duplicate
  rcases hres with ⟨h12, i', hi', h13, heq⟩ | ⟨h12, hpd, hlt, hgt, ha, hb⟩
  · -- a duplicate
    have hrun4 : RunsTo (ifz 12 insertB (seq (addTo 2 26 28) (storeTo 2 13)))
        (fun m => m = M3) (fun m => m = (M3.update 2 (A + n + n + x)).update (A + n + n + x)
          (Dl.getD i' 0)) 4 := by
      refine ifz_eq' (T := 2) h12 ?_ wf_insertB
      refine add_seq' (store_last' ?_)
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hS3.env.r26, g28, h13]
    refine ((hrun1.seq (hrun1b.seq (hrun1c.seq (hrun3.seq hrun4)))).mono
      (eBound 4 (by omega))).weaken (fun m hm => ?_)
    subst hm
    set M4 := (M3.update 2 (A + n + n + x)).update (A + n + n + x) (Dl.getD i' 0) with hM4
    have f4 : ∀ z, z ≠ 2 → z ≠ A + n + n + x → M4 z = M3 z := fun z h1 h2 => by
      rw [hM4, Mem.update_of_ne _ _ h2, Mem.update_of_ne _ _ h1]
    refine ⟨Dl, ⟨?_, ?_, ?_, by simp, by omega, fun v hv => by have := hV.dlt v hv; omega,
      fun y hy => ?_⟩, ?_, ?_⟩
    · refine hS3.congr (W := [2, 28]) (b := A + n + n + n + n + n) (fun z hz hr => ?_)
        (by intro z hz; simp at hz; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [Mem.update_of_ne _ _ hz.2, f4 z hz.1 (by omega)]
    · refine hkeep3.trans (W' := [2, 28]) (a' := A) (b' := A + n + n + n + n + n)
        (fun z hz hr => ?_) (by intro z hz; simp at hz ⊢; omega) le_rfl le_rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [Mem.update_of_ne _ _ hz.2, f4 z hz.1 (by omega)]
    · rw [Mem.update_of_ne _ _ (by decide), f4 14 (by decide) (by omega), g14, hV.r14]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
      · obtain ⟨v, hv, hvm, hvs⟩ := hV.reps y hy
        refine ⟨v, hv, ?_, hvs⟩
        rw [Mem.update_of_ne _ _ (by omega), f4 _ (by omega) (by omega), hrep3, hvm]
      · refine ⟨Dl.getD i' 0, ?_, ?_, heq⟩
        · rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
        · rw [Mem.update_of_ne _ _ (by omega), hM4, Mem.update_self]
    · rw [f4 29 (by decide) (by omega), g29]
    · rw [f4 28 (by decide) (by omega), g28]
  · -- an insertion at `p`
    obtain ⟨M4, ⟨hm4, h23'⟩, hrun4⟩ := (runsTo_insertB e1 hS3.env.r21 hS3.env.r22 hS3.r23
      hS3.env.r25 hS3.env.r26 g28 rfl hpd hdn hA).exact
    have hrun4' : RunsTo (ifz 12 insertB (seq (addTo 2 26 28) (storeTo 2 13)))
        (fun m => m = M3) (fun m => m = M4) (11 * (Dl.length - M3 39) + 20 + 2) :=
      ifz_ne' (by rw [h12]; omega) hrun4 (wf_seq (Layout.wf_addTo _ _ _)
        (Layout.wf_storeTo _ _))
    refine ((hrun1.seq (hrun1b.seq (hrun1c.seq (hrun3.seq hrun4')))).mono
      (eBound _ (by omega))).weaken (fun m hm => ?_)
    subst m
    have hS4 := sortCtx_insert hS3 hx ⟨hpd, hlt, hgt, ha, hb⟩ hdn hm4 h23'
    have f4 : ∀ z, z ∉ [2, 3, 4, 5, 6, 7, 23] → (z < A ∨ A + n + n + n + n + n ≤ z) →
        M4 z = M3 z := fun z hz hr => by rw [hm4 z hz, insMem_out hpd hdn hx hr]
    refine ⟨insL Dl (M3 39) x, ⟨?_, ?_, ?_, by simp, by omega, fun v hv => ?_,
      fun y hy => ?_⟩, ?_, ?_⟩
    · exact hS4.of_outside (W := [28]) (fun z hz => Mem.update_of_ne _ _ (by simpa using hz))
        (by intro z hz; simp at hz; omega)
    · refine hkeep3.trans (W' := [2, 3, 4, 5, 6, 7, 23, 28]) (a' := A)
        (b' := A + n + n + n + n + n) (fun z hz hr => ?_) (by intro z hz; simp at hz ⊢; omega)
        le_rfl le_rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [Mem.update_of_ne _ _ hz.2.2.2.2.2.2.2, f4 z (by simp; omega) hr]
    · rw [Mem.update_of_ne _ _ (by decide), f4 14 (by simp) (by omega), g14, hV.r14]
    · simp only [insL, List.mem_append, List.mem_cons] at hv
      rcases hv with hv | rfl | hv
      · have := hV.dlt v (List.mem_of_mem_take hv); omega
      · omega
      · have := hV.dlt v (List.mem_of_mem_drop hv); omega
    · have hmem : ∀ v ∈ Dl, v ∈ insL Dl (M3 39) x := fun v hv => by
        simp only [insL, List.mem_append, List.mem_cons]
        rw [← List.take_append_drop (M3 39) Dl] at hv
        rcases List.mem_append.1 hv with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
      · obtain ⟨v, hv, hvm, hvs⟩ := hV.reps y hy
        refine ⟨v, hmem v hv, ?_, hvs⟩
        rw [Mem.update_of_ne _ _ (by omega), hm4 _ (by simp; omega), insMem_rep hpd hdn (by omega),
          hrep3, hvm]
      · refine ⟨y, by simp [insL], ?_, rfl⟩
        rw [Mem.update_of_ne _ _ (by omega), hm4 _ (by simp; omega)]
        unfold insMem; rw [if_pos rfl]
    · rw [hm4 29 (by simp), insMem_out hpd hdn hx (by omega), g29]
    · rw [hm4 28 (by simp), insMem_out hpd hdn hx (by omega), g28]

/-! ## All strings -/

theorem VCtx.upd {n SA A : ℕ} {str : ℕ → List ℕ} {M0 m : Mem} {x : ℕ} {Dl : List ℕ}
    (h : VCtx n SA A str M0 x Dl m) {z : ℕ} (hz : z = 29) (v : ℕ) :
    VCtx n SA A str M0 x Dl (m.update z v) := by
  subst hz
  have hA : 64 ≤ A := by have := h.sort.env.hSA; have := h.sort.env.hSAn; omega
  refine ⟨h.sort.of_outside (W := [29]) (fun z hz => Mem.update_of_ne _ _ (by simpa using hz))
    (by intro z hz; simp at hz; omega), h.keep.upd (Or.inl (by simp)) v, ?_, ?_, h.xle, h.dlt,
    fun y hy => ?_⟩
  · rw [Mem.update_of_ne _ _ (by decide), h.r14]
  · rw [Mem.update_of_ne _ _ (by decide), h.r28]
  · obtain ⟨w, hw, hwm, hws⟩ := h.reps y hy
    exact ⟨w, hw, by rw [Mem.update_of_ne _ _ (by omega), hwm], hws⟩

theorem wf_insertOne' : Wf (seq insertOne (seq (addTo 28 28 1) (subTo 29 29 1))) :=
  wf_seq wf_insertOne (by wf_tac)

/-- The potential of the loop over the strings. -/
def vPot (n : ℕ) (str : ℕ → List ℕ) (m : Mem) : ℕ :=
  22 * ∑ y ∈ Finset.Ico (m 28) n, (str y).length + (81 * n + 116) * m 29

theorem runsTo_vertexLoop {n SA A : ℕ} {str : ℕ → List ℕ} {M0 M : Mem} {x : ℕ} {Dl : List ℕ}
    (hV : VCtx n SA A str M0 x Dl M) (h29 : M 29 + x = n) :
    ∃ t, RunsTo vertexLoop (fun m => m = M) (fun m => (∃ Dl', VCtx n SA A str M0 n Dl' m) ∧
      vPot n str m + t ≤ vPot n str M + 1) t := by
  have key := runsTo_whileNz_amortX (i := 29) wf_insertOne'
    (fun m => ∃ x Dl, VCtx n SA A str M0 x Dl m ∧ m 29 + x = n) (vPot n str) ?_ M
    ⟨x, Dl, hV, h29⟩
  · obtain ⟨t, ht⟩ := key
    refine ⟨t, ht.weaken (fun m ⟨⟨x', Dl', hV', h'⟩, h0, hpot⟩ => ⟨⟨Dl', ?_⟩, hpot⟩)⟩
    have : x' = n := by omega
    subst this; exact hV'
  intro M ⟨x, Dl, hV, h29⟩ hne
  have hx : x < n := by omega
  obtain ⟨M1, ⟨Dl', hV1, h29', h28'⟩, hrun1⟩ := (runsTo_insertOne hV hx).exact
  have e1 : M1 1 = 1 := by
    have := hV1.sort.env.one; rwa [Mem.update_of_ne _ _ (by decide)] at this
  have hrun2 : RunsTo (seq (addTo 28 28 1) (subTo 29 29 1)) (fun m => m = M1)
      (fun m => m = (M1.update 28 (x + 1)).update 29 (M 29 - 1)) 2 := by
    refine add_seq' (sub_last' ?_)
    rw [h28', e1, Mem.update_of_ne _ _ (by decide), h29', Mem.update_of_ne _ _ (by decide), e1]
  refine ⟨_, (hrun1.seq hrun2).weaken (fun m hm => ?_)⟩
  subst hm
  have hdx : Dl.length ≤ x := length_le_of_lt hV.sort.sorted hV.dlt
  have hΦ : vPot n str M = 22 * (str x).length + 22 * ∑ y ∈ Finset.Ico (x + 1) n,
      (str y).length + (81 * n + 116) * (M 29 - 1) + (81 * n + 116) := by
    unfold vPot
    rw [hV.r28, Finset.sum_eq_sum_Ico_succ_bot hx]
    have : M 29 = M 29 - 1 + 1 := by omega
    conv_lhs => rw [this]
    ring
  have hΦ' : vPot n str ((M1.update 28 (x + 1)).update 29 (M 29 - 1)) =
      22 * ∑ y ∈ Finset.Ico (x + 1) n, (str y).length + (81 * n + 116) * (M 29 - 1) := by
    unfold vPot
    simp only [Mem.update_self, Mem.update_of_ne _ _ (show (28 : ℕ) ≠ 29 by decide)]
  refine ⟨⟨x + 1, Dl', hV1.upd rfl _, by simp; omega⟩, ?_⟩
  rw [hΦ, hΦ']
  have : 81 * Dl.length ≤ 81 * n := by omega
  omega

/-! ## The positions and the ranks -/

theorem SortCtx.nodup {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {m : Mem}
    (h : SortCtx n SA A str Dl m) : Dl.Nodup :=
  List.Nodup.of_map _ (h.sorted.imp (fun h => ne_of_lt h))

theorem SortCtx.length_le {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {m : Mem}
    (h : SortCtx n SA A str Dl m) : Dl.length ≤ n :=
  length_le_of_lt h.sorted h.dlt

theorem getD_inj_of_nodup {Dl : List ℕ} (hnd : Dl.Nodup) {i j : ℕ} (hi : i < Dl.length)
    (hj : j < Dl.length) (h : Dl.getD i 0 = Dl.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (hnd.getElem_inj_iff).1 h

theorem wf_posBody : Wf (seq (addTo 2 22 32) (seq (loadTo 2 2) (seq (addTo 2 27 2)
    (seq (storeTo 2 32) (seq (addTo 32 32 1) (subTo 29 29 1)))))) := by wf_tac

/-- `pos[D[i]] = i` for every `i < d`, in `8d + 3` steps. -/
theorem runsTo_posLoop {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M : Mem}
    (hS : SortCtx n SA A str Dl M) :
    RunsTo posLoop (fun m => m = M) (fun m => Keep [2, 29, 32] (A + n + n + n)
      (A + n + n + n + n) M m ∧ ∀ i < Dl.length, m (A + n + n + n + Dl.getD i 0) = i)
      (8 * Dl.length + 3) := by
  have hE := hS.env
  have hA : 64 ≤ A := by have := hE.hSA; have := hE.hSAn; omega
  have hdn := hS.length_le
  have hnd := hS.nodup
  set d := Dl.length with hd
  set M1 := (M.update 32 0).update 29 d with hM1
  have eM1 : (M.update 32 0).update 29 ((M.update 32 0) 23) = M1 := by
    rw [hM1, Mem.update_of_ne _ _ (by decide), hS.r23]
  have key := runsTo_whileNz_amortX (i := 29) wf_posBody
    (fun m => ∃ k ≤ d, m 32 = k ∧ m 29 + k = d ∧
      Keep [2, 29, 32] (A + n + n + n) (A + n + n + n + n) M m ∧
      ∀ i < k, m (A + n + n + n + Dl.getD i 0) = i) (fun m => 8 * m 29) ?_ M1
    ⟨0, by omega, by rw [hM1, Mem.update_of_ne _ _ (by decide), Mem.update_self],
      by simp [hM1], fun z hz _ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        rw [hM1, Mem.update_of_ne _ _ hz.2.1, Mem.update_of_ne _ _ hz.2.2],
      fun i hi => by omega⟩
  · obtain ⟨t, ht⟩ := key
    unfold posLoop
    have h8 : 8 * M1 29 = 8 * d := by rw [hM1, Mem.update_self]
    obtain ⟨M2, ⟨⟨k, hk, h32, h29, hkeep, hpos⟩, h0, hpot⟩, hrun⟩ := ht.exact
    refine (assign_seq' (copy_seq' (T := 8 * d + 1) (post := fun m => m = M2) ?_)).weaken
      (fun m hm => ?_)
    · rw [eM1]; simp only [h8] at hpot; exact hrun.mono (by omega)
    · subst hm
      have : k = d := by omega
      subst this
      exact ⟨hkeep, hpos⟩
  · intro m ⟨k, hk, h32, h29, hkeep, hpos⟩ hne
    have hkd : k < d := by omega
    have e1 : m 1 = 1 := by rw [hkeep 1 (by simp) (by omega), hE.one]
    have e22 : m 22 = A := by rw [hkeep 22 (by simp) (by omega), hE.r22]
    have e27 : m 27 = A + n + n + n := by rw [hkeep 27 (by simp) (by omega), hE.r27]
    obtain ⟨gD, gn⟩ := hS.getD hkd
    have eD : m (A + k) = Dl.getD k 0 := by rw [hkeep _ (by simp; omega) (by omega), gD]
    refine ⟨6, ?_⟩
    rt
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e22, e27, h32, eD]
    refine ⟨⟨k + 1, by omega, rfl, by omega, ?_, fun i hi => ?_⟩, by omega⟩
    · refine (((((hkeep.upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd
        (Or.inl (by simp)) _).upd (Or.inr ⟨by omega, by omega⟩) _).upd
        (Or.inl (by simp)) _).upd (Or.inl (by simp)) _
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have hne' : A + n + n + n + Dl.getD i 0 ≠ A + n + n + n + Dl.getD k 0 := by
          intro h
          have hid : i < d := by omega
          have := getD_inj_of_nodup hnd hid hkd (by omega)
          omega
        rw [Mem.update_of_ne _ _ hne']
        have gi := (hS.getD (i := i) (by omega)).2
        have := hA
        simp (disch := omega) only [Mem.update_of_ne]
        exact hpos i hi
      · rw [Mem.update_self]

theorem wf_rankBody : Wf (seq (addTo 2 26 28) (seq (loadTo 2 2)
    (seq (addTo 2 27 2) (seq (loadTo 2 2) (seq (addTo 4 24 28) (seq (storeTo 4 2)
      (seq (addTo 28 28 1) (subTo 29 29 1)))))))) := by wf_tac

/-- `rank[y] = pos[rep[y]]` for every `y < n`, in `10n + 3` steps. -/
theorem runsTo_rankLoop {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M : Mem}
    (hS : SortCtx n SA A str Dl M)
    (hrep : ∀ y < n, ∃ v ∈ Dl, M (A + n + n + y) = v ∧ str v = str y)
    (hpos : ∀ i < Dl.length, M (A + n + n + n + Dl.getD i 0) = i) :
    RunsTo rankLoop (fun m => m = M) (fun m => Keep [2, 4, 28, 29] (A + n + n + n + n)
      (A + n + n + n + n + n) M m ∧ ∀ y < n, ∃ i < Dl.length,
        m (A + n + n + n + n + y) = i ∧ str (Dl.getD i 0) = str y) (10 * n + 3) := by
  have hE := hS.env
  have hA : 64 ≤ A := by have := hE.hSA; have := hE.hSAn; omega
  set M1 := (M.update 28 0).update 29 n with hM1
  have eM1 : (M.update 28 0).update 29 ((M.update 28 0) 21) = M1 := by
    rw [hM1, Mem.update_of_ne _ _ (by decide), hE.r21]
  have key := runsTo_whileNz_amortX (i := 29) wf_rankBody
    (fun m => ∃ y ≤ n, m 28 = y ∧ m 29 + y = n ∧
      Keep [2, 4, 28, 29] (A + n + n + n + n) (A + n + n + n + n + n) M m ∧
      ∀ y' < y, ∃ i < Dl.length, m (A + n + n + n + n + y') = i ∧ str (Dl.getD i 0) = str y')
    (fun m => 10 * m 29) ?_ M1
    ⟨0, by omega, by rw [hM1, Mem.update_of_ne _ _ (by decide), Mem.update_self],
      by simp [hM1], fun z hz _ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        rw [hM1, Mem.update_of_ne _ _ hz.2.2.2, Mem.update_of_ne _ _ hz.2.2.1],
      fun i hi => by omega⟩
  · obtain ⟨t, ht⟩ := key
    unfold rankLoop
    have h8 : 10 * M1 29 = 10 * n := by rw [hM1, Mem.update_self]
    obtain ⟨M2, ⟨⟨y, hy, h28, h29, hkeep, hrk⟩, h0, hpot⟩, hrun⟩ := ht.exact
    refine (assign_seq' (copy_seq' (T := 10 * n + 1) (post := fun m => m = M2) ?_)).weaken
      (fun m hm => ?_)
    · rw [eM1]; simp only [h8] at hpot; exact hrun.mono (by omega)
    · subst hm
      have : y = n := by omega
      subst this
      exact ⟨hkeep, hrk⟩
  · intro m ⟨y, hy, h28, h29, hkeep, hrk⟩ hne
    have hyn : y < n := by omega
    have e1 : m 1 = 1 := by rw [hkeep 1 (by simp) (by omega), hE.one]
    have e26 : m 26 = A + n + n := by rw [hkeep 26 (by simp) (by omega), hE.r26]
    have e27 : m 27 = A + n + n + n := by rw [hkeep 27 (by simp) (by omega), hE.r27]
    have e24 : m 24 = A + n + n + n + n := by rw [hkeep 24 (by simp) (by omega), hE.r24]
    obtain ⟨v, hv, hvm, hvs⟩ := hrep y hyn
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hv
    have hvi : Dl.getD i 0 = v := by rw [List.getD_eq_getElem _ _ hi, hiv]
    have hvn : v < n := hS.dlt v hv
    have eR : m (A + n + n + y) = v := by rw [hkeep _ (by simp; omega) (by omega), hvm]
    have eP : m (A + n + n + n + v) = i := by
      rw [hkeep _ (by simp; omega) (by omega), ← hvi, hpos i hi]
    refine ⟨8, ?_⟩
    rt
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e24, e26, e27, h28, eR, eP]
    refine ⟨⟨y + 1, by omega, rfl, by omega, ?_, fun y' hy' => ?_⟩, by omega⟩
    · refine (((((((hkeep.upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd
        (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd
        (Or.inr ⟨by omega, by omega⟩) _).upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hy' with hy' | rfl
      · obtain ⟨i', hi', h1, h2⟩ := hrk y' hy'
        refine ⟨i', hi', ?_, h2⟩
        simp (disch := omega) only [Mem.update_of_ne]
        exact h1
      · refine ⟨i, hi, ?_, by rw [hvi, hvs]⟩
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]

/-! ## The whole sort -/

/-- The input of the sort: `n` strings, the address of string `v` at `SA + v`, all of them
below the free address `A` (register `14`). -/
structure SortIn (n SA A : ℕ) (str : ℕ → List ℕ) (m : Mem) : Prop where
  one : m 1 = 1
  r14 : m 14 = A
  r20 : m 20 = SA
  r21 : m 21 = n
  hSA : 64 ≤ SA
  hSAn : SA + n ≤ A
  sp64 : ∀ v < n, 64 ≤ m (SA + v)
  spA : ∀ v < n, m (SA + v) + 1 + 2 * (str v).length ≤ A
  strs : ∀ v < n, StrAt m (m (SA + v)) (str v)

/-- The output of the sort: the sorted representatives `Dl` (in `SortCtx`), every string has
a representative, and `rank[y]` (at `A + 4n + y`) is the index of the string `y` in the sorted
list. -/
structure SortOut (n SA A : ℕ) (str : ℕ → List ℕ) (M : Mem) (Dl : List ℕ) (m : Mem) : Prop where
  sort : SortCtx n SA A str Dl m
  keep : Keep Wsort A (A + n + n + n + n + n) M m
  r14 : m 14 = A + n + n + n + n + n
  rank : ∀ y < n, ∃ i < Dl.length, m (A + n + n + n + n + y) = i ∧ str (Dl.getD i 0) = str y

theorem wf_vertexLoop : Wf vertexLoop := by unfold vertexLoop; exact wf_whileNz wf_insertOne'

/-- **The sorting routine**, in `22 Σ |string| + 81 n² + 134 n + 16` steps. -/
theorem runsTo_sortProg {n SA A : ℕ} {str : ℕ → List ℕ} {M : Mem} (hI : SortIn n SA A str M) :
    RunsTo sortProg (fun m => m = M) (fun m => ∃ Dl, SortOut n SA A str M Dl m)
      (22 * ∑ y ∈ Finset.range n, (str y).length + 81 * n * n + 134 * n + 16) := by
  have hA : 64 ≤ A := by have := hI.hSA; have := hI.hSAn; omega
  set M1 := ((((((((M.update 22 A).update 25 (A + n)).update 26 (A + n + n)).update 27
    (A + n + n + n)).update 24 (A + n + n + n + n)).update 14 (A + n + n + n + n + n)).update
    23 0).update 28 0).update 29 n with hM1
  have hrun1 : RunsTo sortInit (fun m => m = M) (fun m => m = M1) 9 := by
    unfold sortInit
    rt
    rw [hM1]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hI.r14, hI.r21]
  have ho1 : Outside [22, 25, 26, 27, 24, 14, 23, 28, 29] M M1 := by
    rw [hM1]; outside_tac (Outside.refl [22, 25, 26, 27, 24, 14, 23, 28, 29] M)
  have g : ∀ z, 64 ≤ z → M1 z = M z := fun z hz => ho1 z (by simp; omega)
  have hV1 : VCtx n SA A str M 0 [] M1 := by
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.hSA, hI.hSAn, fun v hv => ?_, fun v hv => ?_,
      fun v hv => ?_⟩, ?_, fun _ h => by simp at h, fun v hv => by simp at hv, by simp,
      fun i hi => by simp at hi⟩, Keep.of_outside (ho1.mono (by intro z hz; simp at hz ⊢; omega)),
      ?_, ?_, Nat.zero_le _, fun v hv => by simp at hv, fun y hy => by omega⟩
    all_goals first
      | (rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hI.one,
          hI.r20, hI.r21, List.length_nil]; done)
      | skip
    · rw [g _ (by have := hI.hSA; omega)]; exact hI.sp64 v hv
    · rw [g _ (by have := hI.hSA; omega)]; exact hI.spA v hv
    · rw [g _ (by have := hI.hSA; omega)]
      exact (hI.strs v hv).congr (fun z hz1 _ => g z (by have := hI.sp64 v hv; omega))
  obtain ⟨t, ht⟩ := runsTo_vertexLoop hV1 (by simp [hM1])
  obtain ⟨M2, ⟨⟨Dl, hV2⟩, hpot⟩, hrun2⟩ := ht.exact
  have hP1 : vPot n str M1 = 22 * ∑ y ∈ Finset.range n, (str y).length + (81 * n + 116) * n := by
    unfold vPot
    rw [Finset.range_eq_Ico]
    simp (disch := omega) only [hM1, Mem.update_self, Mem.update_of_ne]
  have hS2 := hV2.sort
  have hdn := hS2.length_le
  obtain ⟨M3, ⟨hk3, hpos3⟩, hrun3⟩ := (runsTo_posLoop hS2).exact
  have hS3 : SortCtx n SA A str Dl M3 := hS2.congr (hk3.mono (a' := A + n + n)
    (b' := A + n + n + n + n + n) (fun z hz => hz) (by omega) (by omega))
    (by intro z hz; simp at hz; omega)
  have hrep3 : ∀ y < n, ∃ v ∈ Dl, M3 (A + n + n + y) = v ∧ str v = str y := fun y hy => by
    obtain ⟨v, hv, h1, h2⟩ := hV2.reps y hy
    exact ⟨v, hv, by rw [hk3 _ (by simp; omega) (by omega), h1], h2⟩
  obtain ⟨M4, ⟨hk4, hrk4⟩, hrun4⟩ := (runsTo_rankLoop hS3 hrep3 hpos3).exact
  unfold sortProg
  refine ((hrun1.seq (hrun2.seq (hrun3.seq hrun4))).mono ?_).weaken (fun m hm => ⟨Dl, ?_⟩)
  · rw [hP1] at hpot
    have : 8 * Dl.length ≤ 8 * n := by omega
    nlinarith
  subst hm
  refine ⟨hS3.congr (hk4.mono (a' := A + n + n) (b' := A + n + n + n + n + n) (fun z hz => hz)
    (by omega) (by omega)) (by intro z hz; simp at hz; omega), ?_, ?_, hrk4⟩
  · refine (hV2.keep.trans (Keep.mono hk3 (a' := A) (b' := A + n + n + n + n + n)
      (by intro z hz; simp at hz ⊢; omega) (by omega) (by omega)) (fun z hz => hz) le_rfl
      le_rfl).trans (Keep.mono hk4 (a' := A) (b' := A + n + n + n + n + n)
      (by intro z hz; simp at hz ⊢; omega) (by omega) (by omega)) (fun z hz => hz) le_rfl le_rfl
  · rw [hk4 14 (by simp) (by omega), hk3 14 (by simp) (by omega), hV2.r14]

end TagLin

end Algo
