/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the running time `n^{O(k)}` of Theorems 8.1.2 and 8.1.5 for every `k`.
-/
import Workspace.Algo.DesignOut
import Workspace.Algo.DesignReadNamesValidity
import Workspace.Algo.PadRAM
import Workspace.Machine.Pow

/-!
# Theorems 8.1.2 and 8.1.5: the time bound `n^{O(k)}` for every arity

Theorems 8.1.2 and 8.1.5 say *"Then in time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a
string `x⃗ …`"*.  `Workspace/Algo/DesignScan.lean` and `Workspace/Algo/DesignOut.lean` prove the
procedure quasipolynomial when `k ≤ (log₂ n + 1)^{c₀}` (the use in Sec. 13).  This file proves
the bound for **every** arity `k ≤ n`, in the form `poly(size) · n^{O(k)}`:

```
time ≤ C · (size of the input + 1)^d · (n + 1)^{d·k}
```

with `C` and `d` absolute constants (`Algo.theorem_8_1_5_ram`, `Algo.theorem_8_1_2_ram`).

The factor `poly(size)` cannot be dropped.  The input is a list of relations, and nothing
bounds its length in terms of `n`; the paper's `n^{O(k)}` counts the work on the table of
`k`-tuples, the input being of size `n^{O(k)}` in its applications.  See the the corrected paper
entry on §8.

## How the bound is obtained

The loops of the procedure run over `n^ℓ` strings and over the `k^k` maps of `𝔐_k`, which are
not polynomial in the input size.  So the routine first writes `n^k` zeros next to the input
(`Algo.exists_padProg`); on the padded input every loop is polynomial, with the guard
`k ≤ n ∧ n^k ≤ (number of zeros)` in place of the guard `k ≤ (log₂ n + 1)^{c₀}` of
`Workspace/Algo/WLGuarded.lean`.  The loops are the same (`Algo.tabStep`, `Algo.scanStep`), and
under both guards the two routines agree (`Algo.padPipeline321_eq`, `Algo.padDesignProcedure_eq`).
For `k ≤ n` the guard `k ≤ (log₂ n + 1)^k` holds (`Algo.le_guardBound_self`), so every
specification lemma of `Workspace/Algo/DesignOut.lean` applies at `c₀ = k`.

No axiom and no `sorry`.
-/

namespace RAM

variable {α β σ : Type*}

/-- **Bounded iteration from a set-up, polynomial time.**  The polynomial counterpart of
`RAM.QuasiPolyFun.iterateSetup`: the state bound is asked only along the orbit of the start
state. -/
theorem PolyFun.iterateSetup [Enc α] [Enc β] [Enc σ] {setUp : α → ℕ × σ} {step : σ → σ}
    {readOff : σ → β} {q p : ℕ → ℕ}
    (hsetUp : PolyFun setUp)
    (hstep : PolyFun (fun x : ℕ × σ => (x.1 - 1, step x.2)))
    (hread : PolyFun readOff)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ (setUp a).1, Enc.size (step^[j] (setUp a).2) ≤ p (Enc.size a))
    (hpb : PolyBound p) :
    PolyFun (fun a => readOff (step^[(setUp a).1] (setUp a).2)) := by
  obtain ⟨cq, dq, hcq⟩ := hqb
  obtain ⟨cp, dp, hcp⟩ := hpb
  set P : ℕ → ℕ := fun n => 2 * (cq * (n + 1) ^ dq + 2) + 2 * (cp * (n + 1) ^ dp) with hPdef
  have hPb : PolyBound P :=
    ((polyBound_const 2).mul ((polyBound_witness cq dq).add (polyBound_const 2))).add
      ((polyBound_const 2).mul (polyBound_witness cp dp))
  have hpair : ∀ (a : α), ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ P (Enc.size a) := by
    intro a j hj
    have h1 := Combine.size_pair_le ((setUp a).1 - j) (step^[j] (setUp a).2)
    have h2 : Enc.size ((setUp a).1 - j) = Nat.size ((setUp a).1 - j) + 2 := Small.size_nat _
    have h3 : Nat.size ((setUp a).1 - j) ≤ (setUp a).1 - j := size_le_self _
    have h4 := hq a
    have h5 := hcq (Enc.size a)
    have h6 := hp a j hj
    have h7 := hcp (Enc.size a)
    simp only [hPdef]
    omega
  obtain ⟨P₁, T₁, hT₁, hP₁⟩ := hsetUp.time
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hstep.time
  obtain ⟨P₃, T₃, ⟨c₃, d₃, hc₃⟩, hP₃⟩ := ((polyFun_snd (α := ℕ) (β := σ)).comp hread).time
  refine ⟨polyTimeCleanAt_recursion (setUp := setUp) (step := step) (readOff := readOff)
    (T₂ := fun n => c * (n + 1) ^ d) (T₃ := fun n => c₃ * (n + 1) ^ d₃)
    (p := fun n => c * (P n + 1) ^ d) (q := q) (u := fun n => c₃ * (P n + 1) ^ d₃)
    hP₁ hT₁ (hQ.mono hc) (hP₃.mono hc₃) hq ⟨cq, dq, hcq⟩ ?_
    ((polyBound_witness c d).comp hPb) ?_ ((polyBound_witness c₃ d₃).comp hPb), ?_⟩
  · intro a j hj
    exact polyBound_witness_mono c d (hpair a j (le_of_lt hj))
  · intro a
    have h := hpair a (setUp a).1 (le_refl _)
    rw [Nat.sub_self] at h
    exact polyBound_witness_mono c₃ d₃ h
  · have hf₁ : SizeBound (fun a : α => step^[(setUp a).1] (setUp a).2) :=
      ⟨cp, dp, fun a => le_trans (hp a (setUp a).1 (le_refl _)) (hcp _)⟩
    exact hf₁.comp hread.size

end RAM

namespace Algo

open Babai RAM
open scoped Classical

/-! ## The guard and the counting -/

/-- The guard of the padded routines: the arity is at most the number of vertices, and the pad
has at least `n^k` entries. -/
def PadOk (k n P : ℕ) : Prop := k ≤ n ∧ n ^ k ≤ P

instance (k n P : ℕ) : Decidable (PadOk k n P) := by unfold PadOk; infer_instance

theorem pow_le_of_padOk {k n P j : ℕ} (h : PadOk k n P) (hj : j ≤ k) : n ^ j ≤ P + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hk : k = 0 := by have := h.1; omega
    have : j = 0 := by omega
    subst this; simp
  · exact le_trans (Nat.pow_le_pow_right hn hj) (le_trans h.2 (Nat.le_succ _))

theorem pow_le_of_padOk' {k n P j : ℕ} (h : PadOk k n P) (hj : j ≤ k) : k ^ j ≤ P + 1 :=
  le_trans (Nat.pow_le_pow_left h.1 j) (pow_le_of_padOk h hj)

theorem polyFun_padOk {γ : Type} [Enc γ] {k n P : γ → ℕ} (hk : PolyFun k) (hn : PolyFun n)
    (hP : PolyFun P) (hks : ∀ a, k a ≤ Enc.size a) :
    PolyFun (fun a => decide (PadOk (k a) (n a) (P a))) := by
  have hpow : PolyFun (fun a => n a ^ k a) :=
    PolyFun.pow hn hk (q := id) hks polyBound_id
  refine (PolyFun.ite (hk.le hn) (hpow.le hP) (polyFun_const false)).of_eq (fun a => ?_)
  by_cases h1 : k a ≤ n a <;> by_cases h2 : n a ^ k a ≤ P a <;> simp [PadOk, h1, h2]

/-- One polynomial bound for every state of the padded loops. -/
def padBound (N : ℕ) : ℕ :=
  8 * N + 8 * (1 + (N + 1) * (2 * (1 + N * (2 * (N + 2) + 1)) + 1))
    + 8 * (1 + N * (2 * (N + 2) + 1)) + 40

theorem polyBound_padBound : PolyBound padBound := by
  have h1 : PolyBound (fun N : ℕ => 1 + N * (2 * (N + 2) + 1)) :=
    (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul
      (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))
  have h2 : PolyBound (fun N : ℕ => 1 + (N + 1) * (2 * (1 + N * (2 * (N + 2) + 1)) + 1)) :=
    (polyBound_const 1).add ((polyBound_id.add (polyBound_const 1)).mul
      (((polyBound_const 2).mul h1).add (polyBound_const 1)))
  exact ((((polyBound_const 8).mul polyBound_id).add ((polyBound_const 8).mul h2)).add
    ((polyBound_const 8).mul h1)).add (polyBound_const 40)

/-- A tuple of length `j ≤ N` over entries of size `≤ N + 2`. -/
theorem size_tuple_le_pad {dom : List ℕ} {N j : ℕ} (hent : ∀ x ∈ dom, Enc.size x ≤ N + 2)
    (hj : j ≤ N) {t : List ℕ} (ht : t ∈ tuplesOf dom j) :
    Enc.size t ≤ 1 + N * (2 * (N + 2) + 1) := by
  obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom j t).1 ht
  have h := size_list_le_of_entries t (N + 2) (fun x hx => hent x (hmem x hx))
  rw [hlen] at h
  have h2 : j * (2 * (N + 2) + 1) ≤ N * (2 * (N + 2) + 1) := Nat.mul_le_mul_right _ hj
  omega

/-- The list of the `j`-tuples, when there are at most `N + 1` of them. -/
theorem size_tuplesOf_le_pad {dom : List ℕ} {N j : ℕ} (hent : ∀ x ∈ dom, Enc.size x ≤ N + 2)
    (hj : j ≤ N) (hc : dom.length ^ j ≤ N + 1) :
    Enc.size (tuplesOf dom j) ≤ 1 + (N + 1) * (2 * (1 + N * (2 * (N + 2) + 1)) + 1) := by
  have h := size_list_le_of_entries (tuplesOf dom j) (1 + N * (2 * (N + 2) + 1))
    (fun t ht => size_tuple_le_pad hent hj ht)
  rw [length_tuplesOf] at h
  have h2 : dom.length ^ j * (2 * (1 + N * (2 * (N + 2) + 1)) + 1)
      ≤ (N + 1) * (2 * (1 + N * (2 * (N + 2) + 1)) + 1) := Nat.mul_le_mul_right _ hc
  omega

/-! ## The table of `k`-tuples, padded -/

/-- The input of the padded table builder: `((ks, dom), pad)`. -/
abbrev PadTabIn : Type := (List ℕ × List ℕ) × List ℕ

/-- The set-up: `k` rounds from the empty tuple when the guard holds, none otherwise. -/
def padTabSetUp (a : PadTabIn) : ℕ × (List ℕ × List (List ℕ)) :=
  if PadOk a.1.1.length a.1.2.length a.2.length then (a.1.1.length, (a.1.2, [[]]))
  else (0, (a.1.2, []))

/-- **The table of `k`-tuples on the padded input.** -/
def padTable (a : PadTabIn) : RawWL := tabRead (tabStep^[(padTabSetUp a).1] (padTabSetUp a).2)

theorem padTable_of_guard {a : PadTabIn} (hg : PadOk a.1.1.length a.1.2.length a.2.length) :
    padTable a = tupleTable a.1.2 a.1.1.length := by
  have hset : padTabSetUp a = (a.1.1.length, (a.1.2, [[]])) := if_pos hg
  rw [padTable, hset]
  show tabRead (tabStep^[a.1.1.length] ((a.1.2, [[]]) : List ℕ × List (List ℕ))) = _
  rw [tabStep_iterate]
  rfl

theorem fst_padTable (a : PadTabIn) : (padTable a).1 = a.1.2 := by
  by_cases hg : PadOk a.1.1.length a.1.2.length a.2.length
  · rw [padTable_of_guard hg]; rfl
  · have hset : padTabSetUp a = (0, (a.1.2, [])) := if_neg hg
    rw [padTable, hset]; rfl

theorem size_padTabState_le (a : PadTabIn) (j : ℕ) (hj : j ≤ (padTabSetUp a).1) :
    Enc.size (tabStep^[j] (padTabSetUp a).2) ≤ padBound (Enc.size a) := by
  set N := Enc.size a with hN
  have hdomN : Enc.size a.1.2 ≤ N := (size_snd_le' a.1).trans (size_fst_le' a)
  have hkN : a.1.1.length ≤ N :=
    (length_le_size _).trans ((size_fst_le' a.1).trans (size_fst_le' a))
  have hPN : a.2.length ≤ N := (length_le_size _).trans (size_snd_le' a)
  by_cases hg : PadOk a.1.1.length a.1.2.length a.2.length
  · have hset : padTabSetUp a = (a.1.1.length, (a.1.2, [[]])) := if_pos hg
    have hj' : j ≤ a.1.1.length := by rw [hset] at hj; exact hj
    rw [hset]
    show Enc.size (tabStep^[j] ((a.1.2, [[]]) : List ℕ × List (List ℕ))) ≤ _
    rw [tabStep_iterate]
    have hent : ∀ x ∈ a.1.2, Enc.size x ≤ N + 2 := fun x hx =>
      le_trans (size_mem_le hx) (by omega)
    have hc : a.1.2.length ^ j ≤ N + 1 :=
      le_trans (pow_le_of_padOk hg hj') (by omega)
    have hl := size_tuplesOf_le_pad hent (le_trans hj' hkN) hc
    have hp := size_pair_le' ((a.1.2, tuplesOf a.1.2 j) : List ℕ × List (List ℕ))
    simp only at hp
    unfold padBound
    omega
  · have hset : padTabSetUp a = (0, (a.1.2, [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    rw [hset]
    show Enc.size ((a.1.2, []) : List ℕ × List (List ℕ)) ≤ _
    have hp := size_pair_le' ((a.1.2, []) : List ℕ × List (List ℕ))
    have h1 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    simp only at hp
    unfold padBound
    omega

theorem polyFun_padTabSetUp : PolyFun padTabSetUp := by
  have hk : PolyFun (fun a : PadTabIn => a.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  have hn : PolyFun (fun a : PadTabIn => a.1.2.length) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_length
  have hP : PolyFun (fun a : PadTabIn => a.2.length) := polyFun_snd.comp polyFun_length
  have hks : ∀ a : PadTabIn, a.1.1.length ≤ Enc.size a := fun a =>
    (length_le_size _).trans ((size_fst_le' a.1).trans (size_fst_le' a))
  have hyes : PolyFun (fun a : PadTabIn =>
      ((a.1.1.length, (a.1.2, [[]])) : ℕ × (List ℕ × List (List ℕ)))) :=
    hk.pair ((polyFun_fst.comp polyFun_snd).pair (polyFun_const [[]]))
  have hno : PolyFun (fun a : PadTabIn =>
      ((0, (a.1.2, [])) : ℕ × (List ℕ × List (List ℕ)))) :=
    (polyFun_const 0).pair ((polyFun_fst.comp polyFun_snd).pair (polyFun_const []))
  refine (PolyFun.ite (polyFun_padOk hk hn hP hks) hyes hno).of_eq (fun a => ?_)
  by_cases h : PadOk a.1.1.length a.1.2.length a.2.length <;> simp [padTabSetUp, h]

/-- **The padded table builder is a `RAM.PolyFun`**, with the arity in the input and no bound on
it other than the guard. -/
theorem polyFun_padTable : PolyFun padTable := by
  have hstep : PolyFun (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2)) :=
    (polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)
  refine (PolyFun.iterateSetup (q := fun n => n) (p := padBound)
    polyFun_padTabSetUp hstep polyFun_tabRead ?_ polyBound_id
    size_padTabState_le polyBound_padBound).of_eq (fun a => rfl)
  intro a
  by_cases hg : PadOk a.1.1.length a.1.2.length a.2.length
  · have hset : padTabSetUp a = (a.1.1.length, (a.1.2, [[]])) := if_pos hg
    rw [hset]
    exact (length_le_size _).trans ((size_fst_le' a.1).trans (size_fst_le' a))
  · have hset : padTabSetUp a = (0, (a.1.2, [])) := if_neg hg
    rw [hset]
    exact Nat.zero_le _

/-! ## The index set `𝔐_k`, padded -/

/-- The set-up of the loop building `𝔐_k` on `(X, pad)`. -/
def padMonSetUp (a : PIn × List ℕ) : ℕ × (List ℕ × List (List ℕ)) :=
  if PadOk a.1.1.1.length a.1.1.2.length a.2.length then
    (a.1.1.1.length, (List.range a.1.1.1.length, [[]]))
  else (0, ([], []))

/-- **`𝔐_k` on the padded input.** -/
def padMon (a : PIn × List ℕ) : List (List ℕ) :=
  (tabStep^[(padMonSetUp a).1] (padMonSetUp a).2).2

theorem padMon_of_guard {a : PIn × List ℕ}
    (hg : PadOk a.1.1.1.length a.1.1.2.length a.2.length) :
    padMon a = monIdx a.1.1.1.length := by
  have hset : padMonSetUp a = (a.1.1.1.length, (List.range a.1.1.1.length, [[]])) := if_pos hg
  rw [padMon, hset]
  show (tabStep^[a.1.1.1.length]
    ((List.range a.1.1.1.length, [[]]) : List ℕ × List (List ℕ))).2 = _
  rw [tabStep_iterate]
  rfl

theorem size_padMonState_le (a : PIn × List ℕ) (j : ℕ) (hj : j ≤ (padMonSetUp a).1) :
    Enc.size (tabStep^[j] (padMonSetUp a).2) ≤ padBound (Enc.size a) := by
  set N := Enc.size a with hN
  have hkN : a.1.1.1.length ≤ N :=
    (length_le_size _).trans ((size_fst_le' a.1.1).trans ((size_fst_le' a.1).trans
      (size_fst_le' a)))
  by_cases hg : PadOk a.1.1.1.length a.1.1.2.length a.2.length
  · set k := a.1.1.1.length with hk
    have hset : padMonSetUp a = (k, (List.range k, [[]])) := if_pos hg
    have hj' : j ≤ k := by rw [hset] at hj; exact hj
    rw [hset]
    show Enc.size (tabStep^[j] ((List.range k, [[]]) : List ℕ × List (List ℕ))) ≤ _
    rw [tabStep_iterate]
    have hent : ∀ x ∈ List.range k, Enc.size x ≤ N + 2 := fun x hx =>
      size_idx_le (le_trans (le_of_lt (List.mem_range.1 hx)) hkN)
    have hc : (List.range k).length ^ j ≤ N + 1 := by
      rw [List.length_range]
      exact le_trans (pow_le_of_padOk' hg hj') (by
        have : a.2.length ≤ N := (length_le_size _).trans (size_snd_le' a)
        omega)
    have hl := size_tuplesOf_le_pad hent (le_trans hj' hkN) hc
    have hr : Enc.size (List.range k) ≤ 1 + N * (2 * (N + 2) + 1) := by
      have h := size_list_le_of_entries (List.range k) (N + 2) hent
      rw [List.length_range] at h
      have h2 : k * (2 * (N + 2) + 1) ≤ N * (2 * (N + 2) + 1) := Nat.mul_le_mul_right _ hkN
      omega
    have hp := size_pair_le' ((List.range k, tuplesOf (List.range k) j) :
      List ℕ × List (List ℕ))
    simp only at hp
    unfold padBound
    omega
  · have hset : padMonSetUp a = (0, ([], [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    rw [hset]
    show Enc.size (([], []) : List ℕ × List (List ℕ)) ≤ _
    have hp := size_pair_le' (([], []) : List ℕ × List (List ℕ))
    have h1 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    have h2 : Enc.size ([] : List ℕ) = 1 := rfl
    simp only at hp
    unfold padBound
    omega

theorem polyFun_padMonSetUp : PolyFun padMonSetUp := by
  have hk : PolyFun (fun a : PIn × List ℕ => a.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hn : PolyFun (fun a : PIn × List ℕ => a.1.1.2.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_length
  have hP : PolyFun (fun a : PIn × List ℕ => a.2.length) := polyFun_snd.comp polyFun_length
  have hks : ∀ a : PIn × List ℕ, a.1.1.1.length ≤ Enc.size a := fun a =>
    (length_le_size _).trans ((size_fst_le' a.1.1).trans ((size_fst_le' a.1).trans
      (size_fst_le' a)))
  have hrange : PolyFun (fun a : PIn × List ℕ => List.range a.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength
  have hyes : PolyFun (fun a : PIn × List ℕ =>
      ((a.1.1.1.length, (List.range a.1.1.1.length, [[]])) : ℕ × (List ℕ × List (List ℕ)))) :=
    hk.pair (hrange.pair (polyFun_const [[]]))
  have hno : PolyFun (fun _ : PIn × List ℕ =>
      ((0, ([], [])) : ℕ × (List ℕ × List (List ℕ)))) := polyFun_const _
  refine (PolyFun.ite (polyFun_padOk hk hn hP hks) hyes hno).of_eq (fun a => ?_)
  by_cases h : PadOk a.1.1.1.length a.1.1.2.length a.2.length <;> simp [padMonSetUp, h]

theorem polyFun_padMon : PolyFun padMon := by
  have hstep : PolyFun (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2)) :=
    (polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)
  refine (PolyFun.iterateSetup (q := fun n => n) (p := padBound)
    polyFun_padMonSetUp hstep polyFun_snd ?_ polyBound_id
    size_padMonState_le polyBound_padBound).of_eq (fun a => rfl)
  intro a
  by_cases hg : PadOk a.1.1.1.length a.1.1.2.length a.2.length
  · have hset : padMonSetUp a = (a.1.1.1.length, (List.range a.1.1.1.length, [[]])) :=
      if_pos hg
    rw [hset]
    exact (length_le_size _).trans ((size_fst_le' a.1.1).trans ((size_fst_le' a.1).trans
      (size_fst_le' a)))
  · have hset : padMonSetUp a = (0, ([], [])) := if_neg hg
    rw [hset]
    exact Nat.zero_le _

/-! ## Line 01 on the padded input -/

/-- **Line 01 (`F3 ∘ F2 ∘ F1` of §5.2) on the padded input.** -/
def padPipeline321 (a : PIn × List ℕ) : RawWL :=
  rawPipelineI (pairIdxOf a.1, padMon a) (padTable (a.1.1, a.2), a.1.2)

theorem polyFun_padPipeline321 : PolyFun padPipeline321 := by
  have hin : PolyFun (fun a : PIn × List ℕ =>
      (((pairIdxOf a.1, padMon a), (padTable (a.1.1, a.2), a.1.2)) : IdxP × RawF1In)) :=
    ((polyFun_fst.comp polyFun_pairIdxOf).pair polyFun_padMon).pair
      ((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_padTable).pair
        (polyFun_fst.comp polyFun_snd))
  exact (hin.comp polyFun_rawPipelineI).of_eq (fun a => rfl)

theorem fst_padPipeline321 (a : PIn × List ℕ) : (padPipeline321 a).1 = a.1.1.2 := by
  rw [padPipeline321, rawPipelineI, fst_rawWLStable, rawF2I_fst, rawF1_fst, fst_padTable]

/-- Under both guards the padded pipeline is the guarded pipeline. -/
theorem padPipeline321_eq {c₀ : ℕ} {a : PIn} {pad : List ℕ}
    (hp : PadOk a.1.1.length a.1.2.length pad.length)
    (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length) :
    padPipeline321 (a, pad) = guardedPipeline321 c₀ a := by
  rw [guardedPipeline321_of_guard hg, padPipeline321, rawPipeline, idxOf, pairIdxOf_eq,
    padMon_of_guard (a := (a, pad)) hp, padTable_of_guard (a := (a.1, pad)) hp]

/-! ## Lines 02–08 on the padded input -/

/-- The number of rounds of line 02 on `(z, pad)`: the arity, when the guard holds. -/
def padScanRounds (w : DIn × List ℕ) : ℕ :=
  if PadOk w.1.1.1.1.length w.1.1.2.1.length w.2.length then w.1.1.1.1.length else 0

/-- The set-up of the loop of line 02 on `(z, pad)`. -/
def padScanSetUp (w : DIn × List ℕ) : ℕ × SState := (padScanRounds w, ((w.1, [[]]), none))

/-- **Lines 02–08 on the padded input.** -/
def padScan (w : DIn × List ℕ) : Option (List ℕ) :=
  (scanStep^[(padScanSetUp w).1] (padScanSetUp w).2).2

theorem padScan_eq (w : DIn × List ℕ) : padScan w = ansUpTo w.1 (padScanRounds w) := by
  rw [padScan, padScanSetUp, scanStep_iterate]

theorem size_padScanState_le (w : DIn × List ℕ) (j : ℕ) (hj : j ≤ (padScanSetUp w).1) :
    Enc.size (scanStep^[j] (padScanSetUp w).2) ≤ padBound (Enc.size w) := by
  classical
  set N := Enc.size w with hN
  set z := w.1 with hz
  set dom := z.1.2.1 with hdom
  have hzN : Enc.size z ≤ N := size_fst_le' w
  have hdomN : Enc.size dom ≤ N :=
    ((size_fst_le' z.1.2).trans ((size_snd_le' z.1).trans (size_fst_le' z))).trans hzN
  have hkN : z.1.1.1.length ≤ N := (length_le_size _).trans ((size_fst_le' z.1.1).trans
    ((size_fst_le' z.1).trans ((size_fst_le' z).trans hzN)))
  have hPN : w.2.length ≤ N := (length_le_size _).trans (size_snd_le' w)
  have hent : ∀ x ∈ dom, Enc.size x ≤ N + 2 := fun x hx =>
    le_trans (size_mem_le hx) (by omega)
  -- the rounds run so far, and the number of strings of that length
  have hjk : j ≤ N ∧ dom.length ^ j ≤ N + 1 := by
    by_cases hg : PadOk z.1.1.1.length dom.length w.2.length
    · have hj' : j ≤ z.1.1.1.length := by
        have : padScanRounds w = z.1.1.1.length := if_pos hg
        simpa [padScanSetUp, this] using hj
      exact ⟨hj'.trans hkN, (pow_le_of_padOk hg hj').trans (by omega)⟩
    · have : padScanRounds w = 0 := if_neg hg
      have hj0 : j = 0 := by simpa [padScanSetUp, this] using hj
      subst hj0
      simp
  obtain ⟨hjN, hcount⟩ := hjk
  rw [padScanSetUp, scanStep_iterate]
  change Enc.size (((z, tuplesOf dom j), ansUpTo z j) : SState) ≤ _
  have hl := size_tuplesOf_le_pad hent hjN hcount
  have hans : Enc.size (ansUpTo z j) ≤ 1 + N * (2 * (N + 2) + 1) + 2 := by
    cases hA : ansUpTo z j with
    | none => rw [size_none]; omega
    | some xs =>
        obtain ⟨l, hl, hmem⟩ := ansUpTo_mem hA
        have := size_tuple_le_pad hent (le_trans (le_of_lt hl) hjN) hmem
        rw [size_some_eq]
        omega
  have hp1 := size_pair_le' ((z, tuplesOf dom j) : DIn × List (List ℕ))
  have hp2 := size_pair_le' (((z, tuplesOf dom j), ansUpTo z j) : SState)
  simp only at hp1 hp2
  unfold padBound
  omega

theorem polyFun_padScanSetUp : PolyFun padScanSetUp := by
  have hk : PolyFun (fun w : DIn × List ℕ => w.1.1.1.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hn : PolyFun (fun w : DIn × List ℕ => w.1.1.2.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  have hP : PolyFun (fun w : DIn × List ℕ => w.2.length) := polyFun_snd.comp polyFun_length
  have hks : ∀ w : DIn × List ℕ, w.1.1.1.1.length ≤ Enc.size w := fun w =>
    (length_le_size _).trans ((size_fst_le' w.1.1.1).trans ((size_fst_le' w.1.1).trans
      ((size_fst_le' w.1).trans (size_fst_le' w))))
  have hr : PolyFun padScanRounds :=
    (PolyFun.ite (polyFun_padOk hk hn hP hks) hk (polyFun_const 0)).of_eq (fun w => by
      by_cases h : PadOk w.1.1.1.1.length w.1.1.2.1.length w.2.length <;>
        simp [padScanRounds, h])
  exact (hr.pair ((polyFun_fst.pair (polyFun_const [[]])).pair (polyFun_const none))).of_eq
    (fun w => rfl)

/-- **Lines 02–08 on the padded input are a `RAM.PolyFun`.** -/
theorem polyFun_padScan : PolyFun padScan := by
  have hstep : PolyFun (fun x : ℕ × SState => (x.1 - 1, scanStep x.2)) :=
    (polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_scanStep)
  refine (PolyFun.iterateSetup (q := fun n => n) (p := padBound)
    polyFun_padScanSetUp hstep polyFun_snd ?_ polyBound_id
    size_padScanState_le polyBound_padBound).of_eq (fun w => rfl)
  intro w
  show padScanRounds w ≤ Enc.size w
  have hle : w.1.1.1.1.length ≤ Enc.size w :=
    (length_le_size _).trans ((size_fst_le' w.1.1.1).trans ((size_fst_le' w.1.1).trans
      ((size_fst_le' w.1).trans (size_fst_le' w))))
  unfold padScanRounds
  split <;> omega

/-! ## The whole procedure on the padded input -/

/-- The input of the tests of lines 04–08 at a string, with the padded table of line 01. -/
def padDesignAt (w : GIn × List ℕ) (xs : List ℕ) : DIn :=
  (((w.1.1.1.1, xs), padPipeline321 (w.1.1, w.2)), w.1.2)

/-- **Procedure "Design Lemma", lines 01–08, on the padded input.** -/
def padDesignProcedure (w : GIn × List ℕ) : Option (List ℕ) := padScan (padDesignAt w [], w.2)

/-- The objects of lines 05 and 08 (Theorem 8.1.5), on the padded input. -/
def padDesignOutcome (w : GIn × List ℕ) : Option (List ℕ × (List ℕ × ℕ)) :=
  (padDesignProcedure w).elim none (fun xs => some (designOutRaw (padDesignAt w xs)))

/-- The outcome of Theorem 8.1.2 in the form Sec. 9 reads it (`Algo.designReadExit`), on the
padded input. -/
def padDesignRead (w : GIn × List ℕ) : Option RawDesignReadOut :=
  (padDesignProcedure w).elim none (fun xs => some (designReadExit (padDesignAt w xs)))

theorem polyFun_padDesignAt0 : PolyFun (fun w : GIn × List ℕ => padDesignAt w []) :=
  ((((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
    (polyFun_const ([] : List ℕ))).pair
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_padPipeline321)).pair
    (polyFun_fst.comp polyFun_snd))

theorem polyFun_padDesignProcedure : PolyFun padDesignProcedure :=
  ((polyFun_padDesignAt0.pair polyFun_snd).comp polyFun_padScan).of_eq (fun _ => rfl)

theorem polyFun_padDesign_elim {γ : Type} [Enc γ] {F : DIn → γ} (hF : PolyFun F) :
    PolyFun (fun w : GIn × List ℕ =>
      (padDesignProcedure w).elim none (fun xs => some (F (padDesignAt w xs)))) := by
  have hpair : PolyFun (fun w : GIn × List ℕ =>
      ((padDesignProcedure w, padDesignAt w []) : Option (List ℕ) × DIn)) :=
    polyFun_padDesignProcedure.pair polyFun_padDesignAt0
  have hh : PolyFun (fun q : List ℕ × DIn => (some (F (withStr (q.2, q.1))) : Option γ)) :=
    ((polyFun_snd.pair polyFun_fst).comp polyFun_withStr |>.comp hF |>.comp polyFun_some)
  refine (hpair.comp (PolyFun.optionElim (polyFun_const none) hh)).of_eq (fun w => ?_)
  cases padDesignProcedure w <;> rfl

theorem polyFun_padDesignOutcome : PolyFun padDesignOutcome :=
  polyFun_padDesign_elim polyFun_designOutRaw

theorem polyFun_padDesignRead : PolyFun padDesignRead :=
  polyFun_padDesign_elim polyFun_designReadExit

/-! ## Agreement with the guarded procedure -/

section Agree

variable {c₀ : ℕ} {g : GIn} {pad : List ℕ}

theorem padDesignAt_eq (hp : PadOk g.1.1.1.length g.1.1.2.length pad.length)
    (hg : g.1.1.1.length ≤ guardBound c₀ g.1.1.2.length) (xs : List ℕ) :
    padDesignAt (g, pad) xs = designAt c₀ g xs := by
  rw [padDesignAt, designAt, padPipeline321_eq hp hg]

theorem padDesignProcedure_eq (hp : PadOk g.1.1.1.length g.1.1.2.length pad.length)
    (hg : g.1.1.1.length ≤ guardBound c₀ g.1.1.2.length) :
    padDesignProcedure (g, pad) = designProcedure c₀ g := by
  have hz : padDesignAt (g, pad) [] = (((g.1.1.1, []), guardedPipeline321 c₀ g.1), g.2) :=
    padDesignAt_eq hp hg []
  have hdom : (guardedPipeline321 c₀ g.1).1.length = g.1.1.2.length := by
    rw [fst_guardedPipeline321]
  rw [padDesignProcedure, padScan_eq, designProcedure, rawDesignScan_eq]
  simp only [hz]
  congr 1
  have h1 : padScanRounds ((((g.1.1.1, []), guardedPipeline321 c₀ g.1), g.2), pad)
      = g.1.1.1.length := by
    unfold padScanRounds
    simp only [hdom]
    exact if_pos hp
  have h2 : scanRounds c₀ (((g.1.1.1, []), guardedPipeline321 c₀ g.1), g.2)
      = g.1.1.1.length := by
    apply scanRounds_of_guard
    simp only [hdom]
    exact hg
  rw [h1, h2]

theorem padDesignOutcome_eq (hp : PadOk g.1.1.1.length g.1.1.2.length pad.length)
    (hg : g.1.1.1.length ≤ guardBound c₀ g.1.1.2.length) :
    padDesignOutcome (g, pad) = designOutcome c₀ g := by
  rw [padDesignOutcome, designOutcome, padDesignProcedure_eq hp hg]
  generalize designProcedure c₀ g = o
  cases o with
  | none => simp only [Option.elim_none]
  | some xs => simp only [Option.elim_some, padDesignAt_eq hp hg]

theorem padDesignRead_eq (hp : PadOk g.1.1.1.length g.1.1.2.length pad.length)
    (hg : g.1.1.1.length ≤ guardBound c₀ g.1.1.2.length) :
    padDesignRead (g, pad) =
      (designProcedure c₀ g).elim none (fun xs => some (designReadExit (designAt c₀ g xs))) := by
  rw [padDesignRead, padDesignProcedure_eq hp hg]
  generalize designProcedure c₀ g = o
  cases o with
  | none => simp only [Option.elim_none]
  | some xs => simp only [Option.elim_some, padDesignAt_eq hp hg]

end Agree

/-- For `k ≤ n` the guard of `Workspace/Algo/WLGuarded.lean` holds at the exponent `c₀ = k`. -/
theorem le_guardBound_self {k n : ℕ} (h : k ≤ n) : k ≤ guardBound k n := by
  unfold guardBound
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · omega
    · have : k = 1 := by omega
      subst this; simp
  · have h1 : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ ≤ (Nat.log 2 n + 1) ^ k := Nat.pow_le_pow_left (by omega) k

/-! ## The unpadded routine -/

/-- The padded input: `n^k` zeros next to the input `X = (Ω, R)`. -/
def designPad (g : GIn) : GIn × List ℕ := (g, List.replicate (g.1.1.2.length ^ g.1.1.1.length) 0)

/-- **Procedure "Design Lemma" with the outcome of Theorem 8.1.5**, for every arity. -/
def designOutcomeAll (g : GIn) : Option (List ℕ × (List ℕ × ℕ)) := padDesignOutcome (designPad g)

/-- **Procedure "Design Lemma" with the outcome of Theorem 8.1.2** (in the form of Sec. 9), for
every arity. -/
def designReadAll (g : GIn) : Option RawDesignReadOut := padDesignRead (designPad g)

theorem designPad_padOk {g : GIn} (h : g.1.1.1.length ≤ g.1.1.2.length) :
    PadOk g.1.1.1.length g.1.1.2.length (designPad g).2.length := by
  refine ⟨h, ?_⟩
  simp [designPad]

theorem designOutcomeAll_eq {g : GIn} (h : g.1.1.1.length ≤ g.1.1.2.length) :
    designOutcomeAll g = designOutcome g.1.1.1.length g :=
  padDesignOutcome_eq (designPad_padOk h) (le_guardBound_self h)

theorem designReadAll_eq {g : GIn} (h : g.1.1.1.length ≤ g.1.1.2.length) :
    designReadAll g = (designProcedure g.1.1.1.length g).elim none
      (fun xs => some (designReadExit (designAt g.1.1.1.length g xs))) :=
  padDesignRead_eq (designPad_padOk h) (le_guardBound_self h)

/-! ## The machine: pad, then run the padded routine -/

/-- `s + N + 1 ≤ 2 (s + 1) (n + 1)^k` for `N = n^k`. -/
theorem add_pow_le (s n k : ℕ) : s + n ^ k + 1 ≤ 2 * ((s + 1) * (n + 1) ^ k) := by
  have h1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (by omega) k
  have h3 : s ≤ s * (n + 1) ^ k := Nat.le_mul_of_pos_right s h1
  have h4 : (s + 1) * (n + 1) ^ k = s * (n + 1) ^ k + (n + 1) ^ k := by ring
  omega

/-- **Every polynomial routine of the padded input runs in time `poly(size) · n^{O(k)}` on the
input.**  The program computes `n^k` (`RAM.PolyFun.pow`, the exponent `k` being the length of a
list of the input), writes `n^k` zeros next to the input (`Algo.exists_padProg`), and runs the
routine. -/
theorem exists_designPadProg {β : Type} [Enc β] (f : GIn × List ℕ → β) (hf : PolyFun f) :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ g : GIn,
      RunsOn 16 P g (f (designPad g))
        (C * (Enc.size g + 1) ^ d * (g.1.1.2.length + 1) ^ (d * g.1.1.1.length)) := by
  have hN : PolyFun (fun g : GIn => g.1.1.2.length ^ g.1.1.1.length) :=
    PolyFun.pow (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_length)
      (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length) (q := id)
      (fun g => (length_le_size _).trans ((size_fst_le' g.1.1).trans ((size_fst_le' g.1).trans
        (size_fst_le' g)))) polyBound_id
  have h1 : PolyFun (fun g : GIn =>
      ((g.1.1.2.length ^ g.1.1.1.length, (g, ([] : List ℕ))) : ℕ × (GIn × List ℕ))) :=
    hN.pair (polyFun_id.pair (polyFun_const []))
  obtain ⟨P1, c1, d1, hP1, -⟩ := polyFun_witness h1
  obtain ⟨Ppad, ca, da, hPadwf, hPad⟩ := exists_padProg GIn
  have h2 : PolyFun (fun x : ℕ × (GIn × List ℕ) => f x.2) := polyFun_snd.comp hf
  obtain ⟨P2, c2, d2, hP2, -⟩ := polyFun_witness h2
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = pw c1 d1 t + pw ca da t + pw c2 d2 (20 * t + 10) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => pw c1 d1 t + pw ca da t + pw c2 d2 (20 * t + 10) from funext hGd]
    exact ((polyBound_pw c1 d1).add (polyBound_pw ca da)).add ((polyBound_pw c2 d2).comp
      (((polyBound_const 20).mul polyBound_id).add (polyBound_const 10)))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨RAM.seq P1 (RAM.seq Ppad P2), c * 2 ^ d, d,
    wf_seq (CleanComputeAt.wf' hP1) (wf_seq hPadwf (CleanComputeAt.wf' hP2)), fun g => ?_⟩
  set n := g.1.1.2.length with hn
  set k := g.1.1.1.length with hk
  set N := n ^ k with hNdef
  have r1 : RunsOn 16 P1 g ((N, (g, ([] : List ℕ))) : ℕ × (GIn × List ℕ))
      (c1 * (Enc.size g + 1) ^ d1) := hP1.runsOn g
  have r2 := hPad g N
  have r3 : RunsOn 16 P2 ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ))
      (f (g, List.replicate N 0))
      (c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)) + 1) ^ d2) :=
    hP2.runsOn ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ))
  have r := r1.seq (r2.seq r3)
  refine r.mono ?_
  obtain ⟨t, ht⟩ : ∃ t, t = Enc.size g + N := ⟨_, rfl⟩
  have hs0 : Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)) ≤ 20 * t + 10 := by
    have e1 := size_pair_le' ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ))
    have e2 := size_pair_le' ((g, List.replicate N 0) : GIn × List ℕ)
    have e3 := size_replicate_zero_le N
    have e4 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; simp
    simp only at e1 e2
    omega
  have t1 : pw c1 d1 (Enc.size g) ≤ pw c1 d1 t := pw_mono c1 d1 (by omega)
  have t2 : pw ca da (Enc.size g + N) ≤ pw ca da t := pw_mono ca da (by omega)
  have t3 : pw c2 d2 (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)))
      ≤ pw c2 d2 (20 * t + 10) := pw_mono c2 d2 hs0
  have t5 := hcd t
  rw [hGd] at t5
  -- `c (t + 1)^d ≤ c 2^d (s + 1)^d (n + 1)^{d k}`
  have t6 : c * (t + 1) ^ d ≤ c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k) := by
    have hle : t + 1 ≤ 2 * ((Enc.size g + 1) * (n + 1) ^ k) := by
      rw [ht]; exact add_pow_le _ _ _
    have hp := Nat.pow_le_pow_left hle d
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm k d] at hp
    calc c * (t + 1) ^ d ≤ c * (2 ^ d * ((Enc.size g + 1) ^ d * (n + 1) ^ (d * k))) :=
          Nat.mul_le_mul_left c hp
      _ = c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k) := by ring
  have e1 : pw c1 d1 (Enc.size g) = c1 * (Enc.size g + 1) ^ d1 := rfl
  have e3 : pw c2 d2 (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)))
      = c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)) + 1) ^ d2 := rfl
  show c1 * (Enc.size g + 1) ^ d1 + (pw ca da (Enc.size g + N)
      + c2 * (Enc.size ((0, (g, List.replicate N 0)) : ℕ × (GIn × List ℕ)) + 1) ^ d2)
    ≤ c * 2 ^ d * (Enc.size g + 1) ^ d * (n + 1) ^ (d * k)
  omega

/-! ## Theorems 8.1.5 and 8.1.2 on the RAM -/

theorem length_eq_of_nodup_mem {dom : List ℕ} {n : ℕ} (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) : dom.length = n := by
  have h := List.toFinset_card_of_nodup hnd
  have he : dom.toFinset = Finset.range n := by
    ext c; simp [hmem]
  rw [he, Finset.card_range] at h
  exact h.symm

/-- Line 01 produces a coherent configuration (the guarded form of
`Algo.ambientPipeline321_isCoherent`). -/
theorem guardedPipeline321_isCoherent {n k c : ℕ} {ks dom : List ℕ} {rels : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ i, i ∈ dom ↔ i < n) (hk : ks.length = k)
    (hg : ks.length ≤ guardBound c dom.length) :
    (decWL n k (guardedPipeline321 c ((ks, dom), rels))).IsCoherent := by
  subst k
  apply KAryPartStruct.isCoherent_congr (fun u v =>
    (guardedPipeline321_spec (n := n) (c₀ := c) (a := ((ks, dom), rels)) hnd hmem hg u v).symm)
  exact KAryPartStruct.F3_isCoherent _ (KAryPartStruct.F2_isConfiguration _)

/-- Under the hypotheses of Theorem 8.1.5 the procedure returns (Theorem 8.2.1). -/
theorem designProcedure_isSome {n k a b : ℕ} {α : ℝ} {ks dom : List ℕ} {rels : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ c, c ∈ dom ↔ c < n) (hk : ks.length = k) (hb : 0 < b)
    (hab : α = (a : ℝ) / (b : ℝ)) (hα : 1 / 2 ≤ α) (hα1 : α < 1) (hk2 : 2 ≤ k)
    (hkn : 2 * k ≤ n) (hdef : (1 : ℝ) - α ≤ (defect (decRel n k rels).Aut : ℝ)) :
    ∃ xs, designProcedure k (((ks, dom), rels), (a, b)) = some xs := by
  classical
  have hlen := length_eq_of_nodup_mem hnd hmem
  have hg : ks.length ≤ guardBound k dom.length := by
    rw [hk, hlen]; exact le_guardBound_self (by omega)
  obtain ⟨l, hl, x, hx⟩ := KAryRelStruct.theorem_8_1_5 hα hα1 (decRel n k rels)
    hk2 (by simpa only [Fintype.card_fin] using hkn) hdef
  cases hh : designProcedure k (((ks, dom), rels), (a, b)) with
  | some xs => exact ⟨xs, rfl⟩
  | none =>
      have hp := (designProcedure_none_iff (n := n) (rels := rels) hnd hmem hk hb hab hg).1 hh
      have hex : ∃ l, KAryPartStruct.ReturnsAt α (decRel n k rels).F1.F2.F3 l :=
        ⟨l, by omega, x, hx⟩
      rw [KAryPartStruct.procedure, dif_pos hex] at hp
      exact absurd hp (by simp)

/-- The string the procedure returns is one at which the test of lines 04–08 fires on the
table of line 01. -/
theorem returnsB_designAt {c₀ : ℕ} {g : GIn} {xs : List ℕ}
    (hs : designProcedure c₀ g = some xs) : returnsB (designAt c₀ g xs) = true := by
  rw [designProcedure, rawDesignScan_eq] at hs
  obtain ⟨l, -, hsc⟩ := ansUpTo_isSome hs
  have hm := List.mem_of_mem_head? hsc
  exact (List.mem_filter.1 hm).2

/-- **Theorem 8.1.5 (Design lemma, rephrased), §8.1, on the RAM.**  *"Let `1/2 ≤ α < 1` be a
threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational structure with `n = |Ω|`
vertices, `2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`.  Then in time `n^{O(k)}` we can find a
value `ℓ ≤ k − 1` and a string `x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ` distinct vertices such that by
individualizing each `x_j` we obtain either (i) a canonical coloring of `Ω` with no dominant
color, or (ii) a canonical (classical) coherent configuration `X*` on vertex set `Ω` such that
the subconfiguration induced on the dominant vertex-color class of `X*` is not a clique.
Canonicity in the above statements is relative to `x⃗`."*

One program runs on every input `X = (Ω, R)` with threshold `α = a/b` in time
`C · (size + 1)^d · (n + 1)^{d k}` — the paper's `n^{O(k)}` times a polynomial in the size of
the input (see the module docstring for why that factor is needed).  Under the hypotheses of the
theorem it returns the objects of lines 05 and 08 at a string `x⃗` of length `ℓ < k` at which the
test of lines 04–08 fires in `F3(F2(F1(X)))` (`KAryPartStruct.Returns`: (i) or (ii)); no shorter
string fires; the returned vertex coloring is that of `X_x⃗`, the returned set is its dominant
class, and the returned number is the rank of `(X_x⃗)^{(2)}` on that class.  All three are
functions of the refined table and of `x⃗`, which is the canonicity relative to `x⃗`
(`Algo.designOutRaw`, `Algo.designAt`). -/
theorem theorem_8_1_5_ram :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ g : GIn,
      RunsOn 16 P g (designOutcomeAll g)
        (C * (Enc.size g + 1) ^ d * (g.1.1.2.length + 1) ^ (d * g.1.1.1.length)) ∧
      ∀ (n k a b : ℕ) (α : ℝ) (ks dom : List ℕ) (rels : RawRelStruct),
        g = (((ks, dom), rels), (a, b)) → dom.Nodup → (∀ c, c ∈ dom ↔ c < n) →
        ks.length = k → 0 < b → α = (a : ℝ) / (b : ℝ) → 1 / 2 ≤ α → α < 1 →
        2 ≤ k → 2 * k ≤ n → (1 : ℝ) - α ≤ (defect (decRel n k rels).Aut : ℝ) →
        ∃ w, designOutcomeAll g = some w ∧
        ∃ (xs : List ℕ) (l : ℕ) (hl : l < k) (x : Str (Fin n) l),
          tupleOf x = xs ∧ w = designOutRaw (designAt k g xs) ∧
          Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le x ∧
          (∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
            ¬ Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3
                (by omega : l' ≤ k) y) ∧
          (∀ u : Fin n, restrVColorAt (designAt k g xs, (u : ℕ))
            = ((decWL n k (guardedPipeline321 k ((ks, dom), rels))).restrTo hl.le x).vcolor u) ∧
          (∀ u : Fin n, (u : ℕ) ∈ w.2.1 ↔ u ∈ Babai.KAryPartStruct.dominantClass α
            ((decWL n k (guardedPipeline321 k ((ks, dom), rels))).restrTo hl.le x)) ∧
          (∀ _ : l + 2 ≤ k, w.2.2 =
            ((((decWL n k (guardedPipeline321 k ((ks, dom), rels))).restrTo hl.le x).skel2
                (by omega)).induced
              (Babai.KAryPartStruct.dominantClass α
                ((decWL n k (guardedPipeline321 k ((ks, dom), rels))).restrTo hl.le x))).rank) := by
  obtain ⟨P, C, d, hwf, hrun⟩ := exists_designPadProg padDesignOutcome polyFun_padDesignOutcome
  refine ⟨P, C, d, hwf, fun g => ⟨hrun g, ?_⟩⟩
  intro n k a b α ks dom rels hgdef hnd hmem hk hb hab hα hα1 hk2 hkn hdef
  subst hgdef
  have hlen := length_eq_of_nodup_mem hnd hmem
  have hkn' : ks.length ≤ dom.length := by omega
  have hg : ks.length ≤ guardBound k dom.length := by
    rw [← hk]; exact le_guardBound_self hkn'
  obtain ⟨xs, hxs⟩ := designProcedure_isSome (rels := rels) hnd hmem hk hb hab hα hα1 hk2 hkn hdef
  have he : designOutcomeAll (((ks, dom), rels), (a, b))
      = designOutcome k (((ks, dom), rels), (a, b)) := by
    rw [designOutcomeAll_eq hkn', hk]
  refine ⟨_, he.trans (designOutcome_of_some hxs), ?_⟩
  obtain ⟨xs', l, hl, x, hx, hw, hrest⟩ :=
    designOutcome_spec (n := n) (rels := rels) hnd hmem hk hb hab hg (designOutcome_of_some hxs)
  exact ⟨xs', l, hl, x, hx, hw, hrest⟩

/-- **Theorem 8.1.2 (Design lemma), §8.1, on the RAM**, with the outcome in the form Sec. 9
reads it (the corrected paper Theorem 8.1.2 as used in §9: the coloring of outcome (c)
is not carried).  *"… Then in time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a string
`x⃗ …` such that by individualizing each `x_j` we obtain either (a) a canonical coloring of `Ω`
with no dominant color, or (b) a canonical coloring of `Ω` and a nontrivial canonical
equipartition of the dominant color class, or (c) a canonical coloring of `Ω` and a canonically
embedded uniprimitive coherent configuration (UPCC) whose vertex set is the dominant color
class."*

One program, in time `C · (size + 1)^d · (n + 1)^{d k}`, returns under the hypotheses of the
theorem either an `α`-partition of `Ω` (outcomes (a) and (b), `Algo.designReadExit`), or a
UPCC on a dominant set of vertices (outcome (c)), computed at the string of lines 02–08. -/
theorem theorem_8_1_2_ram :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ g : GIn,
      RunsOn 16 P g (designReadAll g)
        (C * (Enc.size g + 1) ^ d * (g.1.1.2.length + 1) ^ (d * g.1.1.1.length)) ∧
      ∀ (n k a b : ℕ) (α : ℝ) (ks dom : List ℕ) (rels : RawRelStruct),
        g = (((ks, dom), rels), (a, b)) → dom.Nodup → (∀ c, c ∈ dom ↔ c < n) →
        ks.length = k → 0 < b → α = (a : ℝ) / (b : ℝ) → 1 / 2 ≤ α → α < 1 →
        2 ≤ k → 2 * k ≤ n → (1 : ℝ) - α ≤ (defect (decRel n k rels).Aut : ℝ) →
        ∃ o, designReadAll g = some o ∧
          (∃ (l : ℕ) (_ : l < k) (x : Str (Fin n) l),
            Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 (by omega) x ∧
            o = designReadExit (designAt k g (tupleOf x))) ∧
          (o.1 = none → ∃ q, o.2.2 = some q) ∧
          (∀ P, o.1 = some P → (decColPartition n P).IsAlphaPartition α) ∧
          (∀ q, o.2.2 = some q →
            IsUPCCColoring (designReadNamedColor n o.2.1 q) ∧ IsDominant α (winSet n o.2.1) ∧
            ∃ Z : PartitionStructure (Fin o.2.1.length), Z.IsCoherent ∧ Z.IsUniprimitive ∧
              ∀ u v : Fin o.2.1.length, binColor (q, (u, v)) = Z.natColor u v) := by
  obtain ⟨P, C, d, hwf, hrun⟩ := exists_designPadProg padDesignRead polyFun_padDesignRead
  refine ⟨P, C, d, hwf, fun g => ⟨hrun g, ?_⟩⟩
  intro n k a b α ks dom rels hgdef hnd hmem hk hb hab hα hα1 hk2 hkn hdef
  subst hgdef
  have hlen := length_eq_of_nodup_mem hnd hmem
  have hkn' : ks.length ≤ dom.length := by omega
  have hg : ks.length ≤ guardBound k dom.length := by
    rw [← hk]; exact le_guardBound_self hkn'
  obtain ⟨xs, hxs⟩ := designProcedure_isSome (rels := rels) hnd hmem hk hb hab hα hα1 hk2 hkn hdef
  have he : designReadAll (((ks, dom), rels), (a, b))
      = some (designReadExit (designAt k (((ks, dom), rels), (a, b)) xs)) := by
    rw [designReadAll_eq hkn', hk, hxs]; rfl
  obtain ⟨l, hl, x, hx, hret, -⟩ :=
    designProcedure_some (n := n) (rels := rels) hnd hmem hk hb hab hg hxs
  have hr : returnsB (designAt k (((ks, dom), rels), (a, b)) xs) = true := returnsB_designAt hxs
  have hw : RawWL.WF n k (guardedPipeline321 k ((ks, dom), rels)) :=
    wf_line01 (rels := rels) hnd hmem hk hg
  have hcoh := guardedPipeline321_isCoherent (rels := rels) hnd hmem hk hg
  have hz : designAt k (((ks, dom), rels), (a, b)) xs
      = (((ks, tupleOf x), guardedPipeline321 k ((ks, dom), rels)), (a, b)) := by
    rw [designAt, hx]
  rw [hz] at he hr
  have hn4 : 4 ≤ n := by omega
  refine ⟨_, he, ⟨l, hl, x, hret, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    obtain ⟨L, q, hq⟩ := designReadExit_of_none h1
    exact ⟨q, by rw [hq]⟩
  · intro Q hQ
    exact designReadExit_partition_valid hw hk hl.le x hb hab hα hn4 hcoh hr hQ
  · intro q hq
    exact ⟨designReadExit_named_upcc hw hk hl.le x hb hab hα hcoh hq,
      designReadExit_upcc_dominant hw hk hl.le x hb hab hα hcoh hq,
      designReadExit_position_upcc hw hk hl.le x hb hab hα hcoh hq⟩

end Algo

namespace Algo

open RAM RAM.Targets

/-- The step bound of `Algo.theorem_8_1_5_ram` on an input of size at most `(n + 1)^{c k}`. -/
theorem designBound_of_size_le {C d c S n k : ℕ} (hS : S ≤ (n + 1) ^ (c * k)) :
    C * (S + 1) ^ d * (n + 1) ^ (d * k) ≤ C * 2 ^ d * (n + 1) ^ ((c * d + d) * k) := by
  have h1 : 1 ≤ (n + 1) ^ (c * k) := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h2 : S + 1 ≤ 2 * (n + 1) ^ (c * k) := by omega
  have h3 : (S + 1) ^ d ≤ 2 ^ d * (n + 1) ^ (c * k * d) := by
    calc (S + 1) ^ d ≤ (2 * (n + 1) ^ (c * k)) ^ d := Nat.pow_le_pow_left h2 d
      _ = 2 ^ d * (n + 1) ^ (c * k * d) := by rw [mul_pow, ← pow_mul]
  calc C * (S + 1) ^ d * (n + 1) ^ (d * k)
      ≤ C * (2 ^ d * (n + 1) ^ (c * k * d)) * (n + 1) ^ (d * k) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = C * 2 ^ d * (n + 1) ^ ((c * d + d) * k) := by
        rw [show (c * d + d) * k = c * k * d + d * k by ring, pow_add]; ring

/-- **Theorems 8.1.2 and 8.1.5, §8.1: the time `n^{O(k)}` on inputs of size `n^{O(k)}`.**  The
paper gives the relational structure explicitly, as a list of relations each listed by its
tuples (comment after Prop. 2.3.6), and that convention does not bound the number of relations,
so no bound in `n` and `k` alone can hold on every input (the corrected paper the running
time of Theorems 8.1.2 and 8.1.5).  On inputs of size at most `(n + 1)^{c k}`, the size of every
structure the paper feeds to the Design Lemma, the programs of `Algo.theorem_8_1_5_ram` and
`Algo.theorem_8_1_2_ram` run in time `C' (n + 1)^{d' k}`, for constants `C'`, `d'` depending on
`c` only.  Here `n = |Ω|` is the length of the domain list and `k` the length of the arity
list. -/
theorem theorem_8_1_5_ram_of_size (c : ℕ) :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ g : GIn,
      Enc.size g ≤ (g.1.1.2.length + 1) ^ (c * g.1.1.1.length) →
      RunsOn 16 P g (designOutcomeAll g) (C * (g.1.1.2.length + 1) ^ (d * g.1.1.1.length)) := by
  obtain ⟨P, C, d, hwf, h⟩ := theorem_8_1_5_ram
  exact ⟨P, C * 2 ^ d, c * d + d, hwf, fun g hs =>
    (h g).1.mono (designBound_of_size_le hs)⟩

/-- `Algo.theorem_8_1_5_ram_of_size` for the outcome of Theorem 8.1.2
(`Algo.theorem_8_1_2_ram`). -/
theorem theorem_8_1_2_ram_of_size (c : ℕ) :
    ∃ (P : Program) (C d : ℕ), Wf P ∧ ∀ g : GIn,
      Enc.size g ≤ (g.1.1.2.length + 1) ^ (c * g.1.1.1.length) →
      RunsOn 16 P g (designReadAll g) (C * (g.1.1.2.length + 1) ^ (d * g.1.1.1.length)) := by
  obtain ⟨P, C, d, hwf, h⟩ := theorem_8_1_2_ram
  exact ⟨P, C * 2 ^ d, c * d + d, hwf, fun g hs =>
    (h g).1.mono (designBound_of_size_le hs)⟩

end Algo
