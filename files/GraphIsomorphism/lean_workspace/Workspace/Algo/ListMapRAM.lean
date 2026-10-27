/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: running one routine on every entry of a list, on the RAM.
-/
import Workspace.Algo.OracleFold

/-!
# Running a routine on every entry of a list

Procedure AggregateCertificates (§13.2) runs Procedure LocalCertificates "for both inputs
`x`, `y` and all test sets `T`", and the comparison routine "for all pairs". On the RAM this
is a loop over a list of prepared inputs, with one routine run on each. This file gives the
cost of such a loop: `Algo.MapFold.exists_mapProg`. If a program `P` runs on each entry `a`
of `l` to `f a` within `τ a` steps, then `F P` runs from `l` to `l.map f` within

  `100 · ∑_{a ∈ l} τ(a) + (|l| + 2) · poly(size l + size (l.map f))`

steps. The loop is the fold of `Algo.Round.exists_foldProg`, for a round whose children are
the entries of the list, each wrapped as a one-entry list. The round is used only for its
fold: its recursion fields are vacuous (`WF` is `False`).
-/

namespace Algo
open RAM

namespace MapFold

variable {α β : Type*} [Inhabited α]

/-- The `j`-th entry of the list, as a one-entry list, while `j` is in range. -/
def child (p : List α × ℕ × List β) : Option (List α) :=
  if decide (p.2.1 < p.1.length) then some [p.1.getD p.2.1 default] else none

variable (α β) in
/-- The fold over the entries of a list. Only `child`, `init`, `combine` and `finish` are
used; the recursion fields are vacuous. -/
def round : Round (List α) (List β) (List β) where
  WF _ := False
  ground l := l.length
  measure l := l.length
  width l := l.length
  child := child
  init _ := []
  combine p := p.2.2.1 ++ p.2.2.2
  finish p := p.2
  bot := []
  child_eq_none I j s h := by
    have : ¬ j < I.length := by omega
    simp [child, this]
  child_wf _ _ _ _ h := h.elim
  child_measure _ _ _ _ h := h.elim
  child_ground _ _ _ _ h := h.elim

theorem child_of_lt {l : List α} {j : ℕ} (s : List β) (hj : j < l.length) :
    (round α β).child (l, j, s) = some [l[j]] := by
  simp [round, child, hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem child_of_le {l : List α} {j : ℕ} (s : List β) (hj : l.length ≤ j) :
    (round α β).child (l, j, s) = none := by
  have : ¬ j < l.length := by omega
  simp [round, child, this]

/-- **The fold computes the map.** -/
theorem loopAux_eq (f : α → β) (l : List α) :
    ∀ (w j : ℕ) (s : List β), l.length ≤ j + w →
      (round α β).loopAux (fun J => J.map f) w l j s = s ++ (l.drop j).map f := by
  intro w
  induction w with
  | zero =>
    intro j s h
    simp [round, List.drop_eq_nil_of_le (show l.length ≤ j by omega)]
  | succ w ih =>
    intro j s h
    by_cases hj : j < l.length
    · rw [(round α β).loopAux_succ_some (child_of_lt s hj), ih (j + 1) _ (by omega)]
      show s ++ [l[j]].map f ++ _ = _
      rw [List.drop_eq_getElem_cons hj]
      simp only [List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    · rw [(round α β).loopAux_succ_none (child_of_le s (by omega))]
      simp [round, List.drop_eq_nil_of_le (show l.length ≤ j by omega)]

/-- **The calls of the fold are the entries**, each as a one-entry list. -/
theorem loopCalls_eq (f : α → β) (l : List α) :
    ∀ (w j : ℕ) (s : List β), l.length ≤ j + w →
      (round α β).loopCalls (fun J => J.map f) w l j s = (l.drop j).map (fun a => [a]) := by
  intro w
  induction w with
  | zero =>
    intro j s h
    simp [List.drop_eq_nil_of_le (show l.length ≤ j by omega)]
  | succ w ih =>
    intro j s h
    by_cases hj : j < l.length
    · rw [(round α β).loopCalls_succ_some (child_of_lt s hj), ih (j + 1) _ (by omega)]
      rw [List.drop_eq_getElem_cons hj]
      rfl
    · rw [(round α β).loopCalls_succ_none (child_of_le s (by omega))]
      simp [List.drop_eq_nil_of_le (show l.length ≤ j by omega)]

/-- The states of the fold: after `k` steps, the first `k` answers. -/
theorem foldStep_iterate_eq (f : α → β) (l : List α) :
    ∀ (k j : ℕ) (s : List β), j + k ≤ l.length →
      ((round α β).foldStep (fun J => J.map f))^[k] ((l, j, s), false)
        = ((l, j + k, s ++ ((l.drop j).take k).map f), false) := by
  intro k
  induction k with
  | zero => intro j s _; simp
  | succ k ih =>
    intro j s h
    have hj : j < l.length := by omega
    rw [Function.iterate_succ_apply]
    have h1 : (round α β).foldStep (fun J => J.map f) ((l, j, s), false)
        = ((l, j + 1, s ++ [f l[j]]), false) := by
      simp only [Round.foldStep, Round.foldAsk, Bool.false_eq_true, if_false]
      rw [child_of_lt s hj]
      rfl
    rw [h1, ih (j + 1) _ (by omega), List.drop_eq_getElem_cons hj]
    simp only [List.take_succ_cons, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    congr 3
    omega

variable [Enc α] [Enc β]

theorem polyFun_child : PolyFun (child : List α × ℕ × List β → Option (List α)) := by
  have hlt : PolyFun (fun p : List α × ℕ × List β => decide (p.2.1 < p.1.length)) :=
    ((((polyFun_snd.comp polyFun_fst).add (polyFun_const 1)).le
      (polyFun_fst.comp polyFun_length)).of_eq (fun p => by simp [Nat.succ_le_iff]))
  have hget : PolyFun (fun p : List α × ℕ × List β => p.1.getD p.2.1 default) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair
      (polyFun_const default)).comp polyFun_getD).of_eq (fun _ => rfl)
  exact (PolyFun.ite hlt (hget.comp polyFun_singleton |>.comp polyFun_some)
    polyFun_none).of_eq (fun _ => rfl)

theorem polyFun_combine :
    PolyFun (round α β).combine :=
  (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp polyFun_append |>.of_eq
    (fun _ => rfl)

omit [Inhabited α] in
/-- A natural number below the length of a list has size at most that of the list, plus
two. -/
theorem size_nat_le_of_le_length {k : ℕ} {l : List α} (hk : k ≤ l.length) :
    Enc.size k ≤ Enc.size l + 2 := by
  have h1 : Enc.size k = Nat.size k + 2 := Small.size_nat k
  have h2 := size_le_self k
  have h3 := length_le_size l
  omega

omit [Inhabited α] in
theorem size_singleton_le (a : α) : Enc.size [a] ≤ 2 * Enc.size a + 2 := by
  have h1 := size_cons_le a []
  have h2 := size_pair_le' ((a, []) : α × List α)
  have h3 : Enc.size ([] : List α) = 1 := size_nil
  simp only at h2
  omega

/-- `pw` at an affine argument. -/
theorem pw_affine (c d X : ℕ) : pw c d (12 * X + 30) ≤ pw (c * 31 ^ d) d X := by
  unfold pw
  have h : (12 * X + 30 + 1) ^ d ≤ (31 * (X + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
  rw [mul_pow] at h
  calc c * (12 * X + 30 + 1) ^ d ≤ c * (31 ^ d * (X + 1) ^ d) := Nat.mul_le_mul_left _ h
    _ = c * 31 ^ d * (X + 1) ^ d := by ring

theorem sum_map_le_add_mul {γ : Type*} (l : List γ) (g h : γ → ℕ) (E : ℕ)
    (hle : ∀ a ∈ l, g a ≤ h a + E) :
    (l.map g).sum ≤ (l.map h).sum + l.length * E := by
  have := List.sum_le_sum (l := l) (f := g) (g := fun a => h a + E) hle
  simpa [List.sum_map_add, List.map_const', List.sum_replicate] using this

set_option maxHeartbeats 1000000 in
/-- **Running a routine on every entry of a list.** One program transformer `F` and one
polynomial `pw c d`: if `P` runs on each entry `a` of `l` to `f a` within `τ a` steps, then
`F P` runs from `l` to `l.map f` within
`100 · ∑_{a ∈ l} τ(a) + (|l| + 2) · pw c d (size l + size (l.map f))` steps. -/
theorem exists_mapProg [Inhabited β] :
    ∃ (F : Program → Program) (c d : ℕ), ∀ P : Program, Wf P → Wf (F P) ∧
      ∀ (f : α → β) (τ : α → ℕ) (l : List α), (∀ a ∈ l, RunsOn 16 P a (f a) (τ a)) →
        RunsOn 16 (F P) l (l.map f)
          (100 * (l.map τ).sum
            + (l.length + 2) * pw c d (Enc.size l + Enc.size (l.map f))) := by
  obtain ⟨F0, c0, d0, hF0⟩ := (round α β).exists_foldProg polyFun_child polyFun_combine
    (polyFun_nil : PolyFun (fun _ : List α => ([] : List β))) polyFun_snd
    (polyFun_length : PolyFun (fun l : List α => l.length))
  obtain ⟨Phd, ch, dh, hhd, -⟩ := polyFun_witness
    ((((polyFun_id.pair (polyFun_const 0)).pair (polyFun_const default)).comp
      polyFun_getD).of_eq (fun _ => rfl) : PolyFun (fun J : List α => J.getD 0 default))
  obtain ⟨Psg, cs, ds, hsg, -⟩ := polyFun_witness (polyFun_singleton : PolyFun (fun b : β => [b]))
  let Q' : Program → Program := fun P => RAM.seq Phd (RAM.seq P Psg)
  refine ⟨fun P => F0 (Q' P), c0 * 31 ^ d0 + 100 * (ch * 31 ^ dh) + 100 * (cs * 31 ^ ds),
    d0 + dh + ds, ?_⟩
  intro P hP
  have hQ'wf : Wf (Q' P) := wf_seq (hhd.runsOn []).wf (wf_seq hP (hsg.runsOn default).wf)
  obtain ⟨hwf, hrun⟩ := hF0 (Q' P) hQ'wf
  refine ⟨hwf [], ?_⟩
  intro f τ l hl
  obtain ⟨X, hX⟩ : ∃ X, X = Enc.size l + Enc.size (l.map f) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 12 * X + 30 := ⟨_, rfl⟩
  let τ' : List α → ℕ := fun J => ch * (Enc.size J + 1) ^ dh + τ (J.getD 0 default)
    + cs * (Enc.size (f (J.getD 0 default)) + 1) ^ ds
  have hcalls : (round α β).loopCalls (fun J => J.map f) l.length l 0 ((round α β).init l)
      = l.map (fun a => [a]) := by
    rw [loopCalls_eq f l l.length 0 _ (by omega), List.drop_zero]
  have hval : (round α β).loopAux (fun J => J.map f) l.length l 0 ((round α β).init l)
      = l.map f := by
    rw [loopAux_eq f l l.length 0 _ (by omega), List.drop_zero]
    rfl
  have hsizeA : ∀ a ∈ l, Enc.size [a] ≤ B := by
    intro a ha
    have h1 := size_singleton_le a
    have h2 := size_mem_le ha
    omega
  have hsizeB : ∀ a ∈ l, Enc.size [f a] ≤ B := by
    intro a ha
    have h1 := size_singleton_le (f a)
    have h2 := size_mem_le (List.mem_map_of_mem ha : f a ∈ l.map f)
    omega
  have hmain := hrun (fun J => J.map f) τ' l B (by
    intro J hJ
    rw [hcalls] at hJ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hJ
    refine ⟨?_, hsizeA a ha, by simpa using hsizeB a ha⟩
    have r1 := hhd.runsOn [a]
    have r2 := (hl a ha).seq (hsg.runsOn (f a))
    have r3 := r1.seq r2
    simp only [List.getD_cons_zero] at r3
    refine r3.mono (le_of_eq ?_)
    simp only [τ', List.getD_cons_zero]
    omega) (by
    intro k hk
    have hst := foldStep_iterate_eq f l k 0 [] (by omega)
    have hinit : (round α β).init l = [] := rfl
    rw [hinit, hst]
    have h1 := Round.size_foldSt_le (ι := List α) (ω := List β) l (0 + k) ([] ++ ((l.drop 0).take k).map f) false
    have h2 : ([] ++ ((l.drop 0).take k).map f) = (l.map f).take k := by
      simp [List.map_take]
    rw [h2] at h1 ⊢
    have h3 := size_take_le k (l.map f)
    have h4 := size_nat_le_of_le_length (show 0 + k ≤ l.length by omega)
    omega)
  rw [hval, hcalls] at hmain
  refine hmain.mono ?_
  -- the arithmetic
  have hE : ∀ a ∈ l, τ' [a] ≤ τ a + (pw ch dh B + pw cs ds B) := by
    intro a ha
    have e1 : ch * (Enc.size [a] + 1) ^ dh ≤ pw ch dh B := pw_mono ch dh (hsizeA a ha)
    have e2 : Enc.size (f a) ≤ B := by
      have := size_mem_le (List.mem_map_of_mem ha : f a ∈ l.map f); omega
    have e3 : cs * (Enc.size (f a) + 1) ^ ds ≤ pw cs ds B := pw_mono cs ds e2
    show ch * (Enc.size [a] + 1) ^ dh + τ ([a].getD 0 default)
      + cs * (Enc.size (f ([a].getD 0 default)) + 1) ^ ds ≤ _
    simp only [List.getD_cons_zero]
    omega
  have hsum : ((l.map (fun a => [a])).map τ').sum
      ≤ (l.map τ).sum + l.length * (pw ch dh B + pw cs ds B) := by
    rw [List.map_map]
    exact sum_map_le_add_mul l _ τ _ hE
  have k0 : pw c0 d0 B ≤ pw (c0 * 31 ^ d0) d0 X := hB ▸ pw_affine c0 d0 X
  have k1 : pw ch dh B ≤ pw (ch * 31 ^ dh) dh X := hB ▸ pw_affine ch dh X
  have k2 : pw cs ds B ≤ pw (cs * 31 ^ ds) ds X := hB ▸ pw_affine cs ds X
  have k3 : pw (c0 * 31 ^ d0) d0 X + 100 * pw (ch * 31 ^ dh) dh X
      + 100 * pw (cs * 31 ^ ds) ds X
      ≤ pw (c0 * 31 ^ d0 + 100 * (ch * 31 ^ dh) + 100 * (cs * 31 ^ ds)) (d0 + dh + ds) X := by
    unfold pw
    have q0 : (X + 1) ^ d0 ≤ (X + 1) ^ (d0 + dh + ds) := Nat.pow_le_pow_right (by omega) (by omega)
    have q1 : (X + 1) ^ dh ≤ (X + 1) ^ (d0 + dh + ds) := Nat.pow_le_pow_right (by omega) (by omega)
    have q2 : (X + 1) ^ ds ≤ (X + 1) ^ (d0 + dh + ds) := Nat.pow_le_pow_right (by omega) (by omega)
    have := Nat.mul_le_mul_left (c0 * 31 ^ d0) q0
    have := Nat.mul_le_mul_left (100 * (ch * 31 ^ dh)) q1
    have := Nat.mul_le_mul_left (100 * (cs * 31 ^ ds)) q2
    nlinarith
  rw [← hX]
  set W := pw (c0 * 31 ^ d0 + 100 * (ch * 31 ^ dh) + 100 * (cs * 31 ^ ds)) (d0 + dh + ds) X
  have k4 : 100 * (l.length * (pw ch dh B + pw cs ds B)) + (l.length + 2) * pw c0 d0 B
      ≤ (l.length + 2) * W := by
    have : 100 * (pw ch dh B + pw cs ds B) + pw c0 d0 B ≤ W := by omega
    nlinarith
  omega

end MapFold

end Algo
