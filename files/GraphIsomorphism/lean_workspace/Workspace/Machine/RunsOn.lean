import Workspace.Machine.Iterate
import Workspace.Machine.Bridge

/-!
# Running times that depend on the input, not only on its size

The clean classes of `Workspace/Machine/Offset.lean` bound the running time by a function of
the input *size*. Corollaries 1.1.3 and 1.1.4 of the paper bound it by a function of the size
and of a second parameter of the input (the length of the largest orbit, the largest color
multiplicity). Such a bound is not a function of the size, so this file works one input at a
time.

`RAM.RunsOn K P a b T` says that `P`, started in the workspace convention at offset `K` on the
encoding of `a`, halts within `T` steps holding the encoding of `b` in the same convention.
A clean routine gives one such run per input (`RAM.CleanComputeAt.runsOn`), and runs compose
like the clean classes: in sequence, in pairs, and in a bounded loop, each time with the cost
of the given runs.

## Main results

* `RAM.RunsOn.seq`, `RAM.RunsOn.pair`: composition;
* `RAM.runsOn_iterate`: `whileNz (K + 2) Q` iterates a step `N` times, when every step has a run
  and the runs along the iteration cost at most `B`;
* `RAM.RunsOn.bridge`: a run at offset `16` gives a run of the top-level convention, framed by
  `up` and `down`.
-/

namespace RAM

variable {α β γ σ α' β' : Type*}

/-- **One run of a routine of the workspace convention**: started on the encoding of `a` at
offset `K`, the program halts within `T` steps holding the encoding of `b` at offset `K`. -/
def RunsOn [Enc α] [Enc β] (K : ℕ) (P : Program) (a : α) (b : β) (T : ℕ) : Prop :=
  RunsTo P (fun m => m = initMemAt K (Enc.encode a)) (fun m' => m' = initMemAt K (Enc.encode b)) T

theorem CleanComputeAt.runsOn [Enc α] [Enc β] {K : ℕ} {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : CleanComputeAt K P f T) (a : α) : RunsOn K P a (f a) (T (Enc.size a)) := h a

theorem RunsOn.mono [Enc α] [Enc β] {K : ℕ} {P : Program} {a : α} {b : β} {T T' : ℕ}
    (h : RunsOn K P a b T) (hT : T ≤ T') : RunsOn K P a b T' := RunsTo.mono h hT

theorem RunsOn.seq [Enc α] [Enc β] [Enc γ] {K : ℕ} {P Q : Program} {a : α} {b : β} {c : γ}
    {T T' : ℕ} (hP : RunsOn K P a b T) (hQ : RunsOn K Q b c T') :
    RunsOn K (RAM.seq P Q) a c (T + T') := RunsTo.seq hP hQ

/-- Two runs with the same encoding are the same run. -/
theorem RunsOn.congr [Enc α] [Enc β] [Enc α'] [Enc β'] {K : ℕ} {P : Program} {a : α} {b : β}
    {a' : α'} {b' : β'} {T : ℕ} (h : RunsOn K P a b T) (ha : Enc.encode a' = Enc.encode a)
    (hb : Enc.encode b' = Enc.encode b) : RunsOn K P a' b' T := by
  unfold RunsOn at h ⊢
  rw [ha, hb]
  exact h

/-- **Pairing of two runs** on the same input, with the cost of `RAM.Pairing.runsTo_pairProg`. -/
theorem RunsOn.pair [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K) {Pf Pg : Program} {a : α}
    {b : β} {c : γ} {Tf Tg : ℕ} (hf : RunsOn K Pf a b Tf) (hg : RunsOn K Pg a c Tg) :
    RunsOn K (Pairing.pairProg K Pf Pg) a (b, c)
      (19 * Enc.size a + 19 * Enc.size b + 19 * Enc.size c + 10 * Tf + 10 * Tg + 11 * K + 200) := by
  have hpair : Enc.encode (b, c)
      = ((Enc.encode b).length :: Enc.encode b) ++ ((Enc.encode c).length :: Enc.encode c) := rfl
  have h := Pairing.runsTo_pairProg (K := K) (E := Enc.encode a) (F := Enc.encode b)
    (G := Enc.encode c) hK hf hg
  rw [← hpair] at h
  refine h.mono ?_
  have hE : (Enc.encode a).length ≤ Enc.size a := le_of_lt (length_lt_listSize _)
  have hF : (Enc.encode b).length ≤ Enc.size b := le_of_lt (length_lt_listSize _)
  have hG : (Enc.encode c).length ≤ Enc.size c := le_of_lt (length_lt_listSize _)
  omega

/-- **Bounded iteration, one run per step.**  If every state `(k, s)` has a run of `Q` to
`(k - 1, step s)` costing `W (k, s)`, and the runs at the states the iteration passes through
cost at most `B`, then `whileNz (K + 2) Q` iterates `step` exactly `N` times in
`N * (B + 2) + 1` steps.  This is `RAM.runsTo_iterateAt` with a cost per state instead of a
cost per size. -/
theorem runsOn_iterate [Enc σ] {K : ℕ} {Q : Program} {step : σ → σ} {W : ℕ × σ → ℕ}
    (hQ : ∀ p : ℕ × σ, RunsOn K Q p ((p.1 - 1, step p.2) : ℕ × σ) (W p))
    (N : ℕ) (s₀ : σ) (B : ℕ)
    (hB : ∀ j < N, W ((N - j, step^[j] s₀) : ℕ × σ) ≤ B) :
    RunsOn K (whileNz (K + 2) Q) ((N, s₀) : ℕ × σ) ((0, step^[N] s₀) : ℕ × σ)
      (N * (B + 2) + 1) := by
  set inv : Mem → Prop :=
    fun m => ∃ j ≤ N, m = initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hinv
  have hbody : ∀ n : ℕ, RunsTo Q (fun m => inv m ∧ m (K + 2) ≠ 0 ∧ m (K + 2) = n)
      (fun m' => inv m' ∧ m' (K + 2) < n) B := by
    intro n
    refine ⟨(hQ ((0 : ℕ), s₀)).wf, fun m hm => ?_⟩
    obtain ⟨⟨j, hjN, rfl⟩, hne, hμ⟩ := hm
    rw [initMemAt_prod_counter] at hne hμ
    have hj : j < N := by omega
    obtain ⟨k, hk, hhalt, hmem⟩ :=
      (hQ ((N - j, step^[j] s₀) : ℕ × σ)).spec _ rfl
    refine ⟨k, le_trans hk (hB j hj), hhalt, ?_⟩
    rw [hmem]
    have key : (((N - j, step^[j] s₀) : ℕ × σ).1 - 1, step ((N - j, step^[j] s₀) : ℕ × σ).2)
        = ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) := by
      have h1 : N - j - 1 = N - (j + 1) := by omega
      simp [h1, Function.iterate_succ_apply']
    rw [key]
    exact ⟨⟨j + 1, by omega, rfl⟩, by rw [initMemAt_prod_counter]; omega⟩
  have hN : ∀ m, inv m → m (K + 2) ≤ N := by
    rintro m ⟨j, hjN, rfl⟩
    rw [initMemAt_prod_counter]
    omega
  refine ((runsTo_whileNz (μ := fun m => m (K + 2)) hbody hN).conseq ?_ ?_ (le_refl _))
  · rintro m rfl
    exact ⟨0, Nat.zero_le _, by simp⟩
  · rintro m' ⟨⟨j, hjN, rfl⟩, hz⟩
    rw [initMemAt_prod_counter] at hz
    have hjeq : j = N := by omega
    subst hjeq
    rw [Nat.sub_self]

/-- **The bridge for one run.**  A run at offset `16`, framed by `up` and `down`, is a run of
the top-level convention: the program halts within the stated number of steps with the output
encoding `b`. -/
theorem RunsOn.bridge [Enc α] [Enc β] {P : Program} {a : α} {b : β} {T : ℕ}
    (h : RunsOn 16 P a b T) :
    ∃ k ≤ (18 * Enc.size a + 78) + (T + (7 * Enc.size b + 34)),
      Halted (RAM.seq Bridge.up (RAM.seq P Bridge.down))
          (run (RAM.seq Bridge.up (RAM.seq P Bridge.down)) (Config.init (Enc.encode a)) k) ∧
        OutputAt (run (RAM.seq Bridge.up (RAM.seq P Bridge.down)) (Config.init (Enc.encode a)) k).mem
          (Enc.encode b) := by
  have h1 : (Enc.encode a).length < Enc.size a := length_encode_lt a
  have h2 : (Enc.encode b).length < Enc.size b := length_encode_lt b
  have hbound : (18 * (Enc.encode a).length + 78) + (T + (7 * (Enc.encode b).length + 34))
      ≤ (18 * Enc.size a + 78) + (T + (7 * Enc.size b + 34)) := by omega
  obtain ⟨k, hk, hhalt, hout⟩ :=
    ((Bridge.runsTo_bridge h).mono hbound).spec (initMem (Enc.encode a)) rfl
  exact ⟨k, hk, hhalt, hout⟩

end RAM
