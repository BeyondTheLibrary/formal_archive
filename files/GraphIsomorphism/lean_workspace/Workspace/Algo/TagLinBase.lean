/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  RAM tools shared by the
routines of `Workspace/Algo/TagLinSort.lean` and `Workspace/Algo/TagLinMain.lean`.
-/
import Workspace.Algo.ExplLinear
import Workspace.Algo.TagLinLcp

/-!
# Tools for the step-exact tagged refinement

* `RAM.Exact.runsTo_whileNz_amortX`: the amortized loop rule of `Workspace/Machine/Exact.lean`
  in a form that can be nested.  The loop, started in `M`, runs some `t` steps and ends in a
  memory `m'` with `Φ m' + t ≤ Φ M + 1`: the steps are paid by the potential actually used, not
  by the whole potential of `M`.
* `Keep W a b M m`: `m` differs from `M` only at the registers `W` and in the region `[a, b)`.
* `StrAt m p s`: the string `s` is stored at `p` in its framed encoding
  `[2|s|, 1, s₀, 1, s₁, …]`, the format of the colors in the input.

No axiom, no `sorry`.
-/

namespace RAM

namespace Exact

/-- **The amortized while rule, nestable form.**  As `runsTo_whileNz_amort`, but the loop's
own step count `t` is returned together with `Φ m' + t ≤ Φ M + 1`. -/
theorem runsTo_whileNz_amortX {i : ℕ} {P : Program} (hw : Wf P) (inv : Mem → Prop)
    (Φ : Mem → ℕ)
    (hP : ∀ M, inv M → M i ≠ 0 → ∃ t, RunsTo P (fun m => m = M)
      (fun m' => inv m' ∧ Φ m' + t + 2 ≤ Φ M) t) :
    ∀ M, inv M → ∃ t, RunsTo (whileNz i P) (fun m => m = M)
      (fun m' => inv m' ∧ m' i = 0 ∧ Φ m' + t ≤ Φ M + 1) t := by
  set W := whileNz i P with hW
  have hjz : ∀ m : Mem, W[(⟨0, m⟩ : Config).pc]? = some (Instr.jz i (P.length + 2)) :=
    fun _ => rfl
  have hjump : W[1 + P.length]? = some (Instr.jump 0) := by
    simp [hW, whileNz, Nat.add_comm]
  have hexit : ∀ m : Mem, m i = 0 → run W ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
    intro m h0
    rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
    simp [exec, h0]
  have key : ∀ (N : ℕ) (m : Mem), inv m → Φ m ≤ N →
      ∃ k m', run W ⟨0, m⟩ k = ⟨W.length, m'⟩ ∧ inv m' ∧ m' i = 0 ∧ Φ m' + k ≤ Φ m + 1 := by
    intro N
    induction N with
    | zero =>
        intro m hm hΦ
        by_cases h0 : m i = 0
        · exact ⟨1, m, by rw [hexit m h0]; simp [hW, whileNz], hm, h0, by omega⟩
        · obtain ⟨t, ht⟩ := hP m hm h0
          obtain ⟨k, -, m', -, ⟨-, hle⟩, -⟩ := ht.halt_at rfl
          omega
    | succ N ih =>
        intro m hm hΦ
        by_cases h0 : m i = 0
        · exact ⟨1, m, by rw [hexit m h0]; simp [hW, whileNz], hm, h0, by omega⟩
        · obtain ⟨t, ht⟩ := hP m hm h0
          obtain ⟨k, hkT, m', hkrun, ⟨hinv', hle⟩, hkmin⟩ := ht.halt_at rfl
          obtain ⟨k', m'', hk'run, hinv'', h0'', hΦ''⟩ := ih m' hinv' (by omega)
          have hstep : run W ⟨0, m⟩ 1 = ⟨1, m⟩ := by
            rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
            simp [exec, h0]
          have hbody : run W ⟨1, m⟩ k = ⟨1 + P.length, m'⟩ := by
            rw [run_block (A := [Instr.jz i (P.length + 2)]) (Q := P)
              (B := [Instr.jump 0]) (by simp [hW, whileNz]) (by simp) k hkmin, hkrun]
          have hback : run W ⟨1 + P.length, m'⟩ 1 = ⟨0, m'⟩ := by
            rw [run_succ, run_zero, step_of_get (by simpa using hjump) (by simp)]
            simp [exec]
          refine ⟨1 + k + 1 + k', m'', ?_, hinv'', h0'', by omega⟩
          rw [run_add, run_add, run_add, hstep, hbody, hback, hk'run]
  intro M hM
  obtain ⟨k, m', hrun, hinv, h0, hΦ⟩ := key _ M hM le_rfl
  refine ⟨k, wf_whileNz hw, ?_⟩
  rintro m rfl
  exact ⟨k, le_rfl, by rw [hrun]; exact halted_of_pc_length rfl, by rw [hrun]; exact ⟨hinv, h0,
    hΦ⟩⟩

/-- A run from one memory ends in one memory. -/
theorem _root_.RAM.RunsTo.exact {P : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo P (fun m => m = M) post T) :
    ∃ M', post M' ∧ RunsTo P (fun m => m = M) (fun m => m = M') T := by
  obtain ⟨k, hk, hhalt, hpost⟩ := h.spec M rfl
  exact ⟨_, hpost, ⟨h.wf, fun m hm => by subst hm; exact ⟨k, hk, hhalt, rfl⟩⟩⟩


/-! ## Pointwise rules with a free time bound -/

theorem assign_seq' {x c : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x c) post T) :
    RunsTo (seq (assign x c) Q) (fun m => m = M) post (T + 1) :=
  (assign_seq h).mono (by omega)

theorem copy_seq' {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y)) post T) :
    RunsTo (seq (copyTo x y) Q) (fun m => m = M) post (T + 1) :=
  (copy_seq h).mono (by omega)

theorem add_seq' {x y z : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y + M z)) post T) :
    RunsTo (seq (addTo x y z) Q) (fun m => m = M) post (T + 1) :=
  (add_seq h).mono (by omega)

theorem sub_seq' {x y z : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y - M z)) post T) :
    RunsTo (seq (subTo x y z) Q) (fun m => m = M) post (T + 1) :=
  (sub_seq h).mono (by omega)

theorem load_seq' {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M (M y))) post T) :
    RunsTo (seq (loadTo x y) Q) (fun m => m = M) post (T + 1) :=
  (load_seq h).mono (by omega)

theorem store_seq' {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update (M x) (M y)) post T) :
    RunsTo (seq (storeTo x y) Q) (fun m => m = M) post (T + 1) :=
  (store_seq h).mono (by omega)

theorem assign_last' {x c : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ} (h : post (M.update x c)) :
    RunsTo (assign x c) (fun m => m = M) post (T + 1) :=
  (assign_last h).mono (by omega)

theorem copy_last' {x y : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : post (M.update x (M y))) : RunsTo (copyTo x y) (fun m => m = M) post (T + 1) :=
  (copy_last h).mono (by omega)

theorem add_last' {x y z : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : post (M.update x (M y + M z))) : RunsTo (addTo x y z) (fun m => m = M) post (T + 1) :=
  (add_last h).mono (by omega)

theorem sub_last' {x y z : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : post (M.update x (M y - M z))) : RunsTo (subTo x y z) (fun m => m = M) post (T + 1) :=
  (sub_last h).mono (by omega)

theorem load_last' {x y : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : post (M.update x (M (M y)))) : RunsTo (loadTo x y) (fun m => m = M) post (T + 1) :=
  (load_last h).mono (by omega)

theorem store_last' {x y : ℕ} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : post (M.update (M x) (M y))) : RunsTo (storeTo x y) (fun m => m = M) post (T + 1) :=
  (store_last h).mono (by omega)

theorem nil_last' {M : Mem} {post : Mem → Prop} {T : ℕ} (h : post M) :
    RunsTo ([] : Program) (fun m => m = M) post T :=
  (runsTo_nil (fun m hm => by subst hm; exact h)).mono (by omega)

/-- `ifz` from one memory, with a free time bound. -/
theorem ifz_ne' {i : ℕ} {P Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (hi : M i ≠ 0) (hP : RunsTo P (fun m => m = M) post T) (hQ : Wf Q) :
    RunsTo (ifz i P Q) (fun m => m = M) post (T + 2) := ifz_ne hi hP hQ

theorem ifz_eq' {i : ℕ} {P Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (hi : M i = 0) (hQ : RunsTo Q (fun m => m = M) post T) (hP : Wf P) :
    RunsTo (ifz i P Q) (fun m => m = M) post (T + 2) := ifz_eq hi hQ hP

/-- Straight-line code: strip the instructions one by one. -/
syntax "rt" : tactic
macro_rules
  | `(tactic| rt) => `(tactic| repeat (first
      | refine RAM.Exact.assign_seq' ?_ | refine RAM.Exact.copy_seq' ?_
      | refine RAM.Exact.add_seq' ?_ | refine RAM.Exact.sub_seq' ?_
      | refine RAM.Exact.load_seq' ?_ | refine RAM.Exact.store_seq' ?_
      | refine RAM.Exact.assign_last' ?_ | refine RAM.Exact.copy_last' ?_
      | refine RAM.Exact.add_last' ?_ | refine RAM.Exact.sub_last' ?_
      | refine RAM.Exact.load_last' ?_ | refine RAM.Exact.store_last' ?_))

/-- Well-formedness of a program built from the combinators. -/
syntax "wf_tac" : tactic
macro_rules
  | `(tactic| wf_tac) => `(tactic| repeat (first
      | apply RAM.wf_seq | apply RAM.wf_ifz | apply RAM.wf_whileNz
      | apply RAM.Layout.wf_assign | apply RAM.Layout.wf_copyTo | apply RAM.Layout.wf_addTo
      | apply RAM.Layout.wf_subTo | apply RAM.Layout.wf_loadTo | apply RAM.Layout.wf_storeTo
      | exact Algo.ExplLinear.wf_nil))

/-! ## Frames and strings in memory -/

/-- `m` differs from `M` only at the registers `W` and in the region `[a, b)`. -/
def Keep (W : List ℕ) (a b : ℕ) (M m : Mem) : Prop :=
  ∀ z, z ∉ W → (z < a ∨ b ≤ z) → m z = M z

theorem Keep.refl (W : List ℕ) (a b : ℕ) (M : Mem) : Keep W a b M M := fun _ _ _ => rfl

theorem Keep.trans {W W' : List ℕ} {a b a' b' : ℕ} {M m m' : Mem} (h : Keep W a b M m)
    (h' : Keep W' a' b' m m') (hW : ∀ z ∈ W', z ∈ W) (ha : a ≤ a') (hb : b' ≤ b) :
    Keep W a b M m' := by
  intro z hz hab
  rw [h' z (fun h'' => hz (hW z h'')) (by omega), h z hz hab]

theorem Keep.of_outside {W : List ℕ} {a b : ℕ} {M m : Mem} (h : Outside W M m) :
    Keep W a b M m := fun z hz _ => h z hz

theorem Keep.mono {W W' : List ℕ} {a b a' b' : ℕ} {M m : Mem} (h : Keep W a b M m)
    (hW : ∀ z ∈ W, z ∈ W') (ha : a' ≤ a) (hb : b ≤ b') : Keep W' a' b' M m :=
  fun z hz hab => h z (fun h' => hz (hW z h')) (by omega)

theorem Keep.upd {W : List ℕ} {a b : ℕ} {M m : Mem} (h : Keep W a b M m) {z : ℕ}
    (hz : z ∈ W ∨ (a ≤ z ∧ z < b)) (v : ℕ) : Keep W a b M (m.update z v) := by
  intro y hy hab
  have hyz : y ≠ z := by
    rintro rfl; rcases hz with hz | hz
    · exact hy hz
    · omega
  rw [Mem.update_of_ne _ _ hyz]
  exact h y hy hab

/-- The string `s` stored at `p` in its framed encoding `[2|s|, 1, s₀, 1, s₁, …]`. -/
def StrAt (m : Mem) (p : ℕ) (s : List ℕ) : Prop :=
  m p = 2 * s.length ∧ ∀ j (h : j < s.length), m (p + 1 + 2 * j) = 1 ∧ m (p + 2 + 2 * j) = s[j]

theorem blk_encList_nat_iff {m : Mem} {s : List ℕ} : ∀ {p : ℕ},
    Blk m p (encList Enc.encode s) ↔
      ∀ j (h : j < s.length), m (p + 2 * j) = 1 ∧ m (p + 1 + 2 * j) = s[j] := by
  induction s with
  | nil => intro p; simp [encList, Blk.nil]
  | cons a s ih =>
    intro p
    rw [Blk.encList_cons]
    change m p = 1 ∧ Blk m (p + 1) [a] ∧ Blk m (p + 1 + 1) (encList Enc.encode s) ↔ _
    rw [Blk.cons, ih]
    simp only [Blk.nil, and_true]
    constructor
    · rintro ⟨h1, h2, h3⟩ j hj
      rcases j with _ | j
      · exact ⟨by simpa using h1, by simpa using h2⟩
      · have := h3 j (by simp at hj; omega)
        simp only [List.getElem_cons_succ]
        rw [show p + 2 * (j + 1) = p + 1 + 1 + 2 * j by ring,
          show p + 1 + 2 * (j + 1) = p + 1 + 1 + 1 + 2 * j by ring]
        exact this
    · intro h
      have h0 := h 0 (by simp)
      refine ⟨by simpa using h0.1, by simpa using h0.2, fun j hj => ?_⟩
      have := h (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show p + 2 * (j + 1) = p + 1 + 1 + 2 * j by ring,
        show p + 1 + 2 * (j + 1) = p + 1 + 1 + 1 + 2 * j by ring] at this
      exact this

theorem strAt_iff_blk {m : Mem} {p : ℕ} {s : List ℕ} :
    StrAt m p s ↔ Blk m p (RAM.frame (Enc.encode s)) := by
  rw [Blk.frame_iff, Algo.ExplLinear.length_encode_nat_list]
  change _ ↔ _ ∧ Blk m (p + 1) (encList Enc.encode s)
  rw [blk_encList_nat_iff]
  unfold StrAt
  refine and_congr_right fun _ => ?_
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [show p + 1 + 1 + 2 * j = p + 2 + 2 * j by omega]

theorem StrAt.congr {m m' : Mem} {p : ℕ} {s : List ℕ} (h : StrAt m p s)
    (hm : ∀ z, p ≤ z → z < p + 1 + 2 * s.length → m' z = m z) : StrAt m' p s := by
  refine ⟨by rw [hm p le_rfl (by omega), h.1], fun j hj => ?_⟩
  rw [hm _ (by omega) (by omega), hm _ (by omega) (by omega)]
  exact h.2 j hj

/-- The letter `j` of a stored string, at the doubled offset `2j`. -/
theorem StrAt.letter {m : Mem} {p : ℕ} {s : List ℕ} (h : StrAt m p s) {j : ℕ}
    (hj : j < s.length) : m (p + 2 * j + 1 + 1) = s[j] := by
  rw [show p + 2 * j + 1 + 1 = p + 2 + 2 * j by omega]; exact (h.2 j hj).2

end Exact

end RAM
