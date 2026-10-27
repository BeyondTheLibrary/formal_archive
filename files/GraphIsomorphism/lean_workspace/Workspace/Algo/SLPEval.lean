import Workspace.Algo.Stabilizer

/-!
# Straight-line programs on raw permutations (Definition 11.1.10, Observation 11.1.11)

Definition 11.1.10:

> Given a group `G` by a list `S` of generators, a straight-line program of length `ℓ` in `G`
> is a sequence of length `ℓ` of elements of `G` such that each element in the sequence is
> either one of the generators or is a product of two elements earlier in the sequence or is
> the inverse of an element earlier in the sequence.  We say that the straight-line program
> computes a set `T` of elements if the elements of `T` appear in the sequence and are marked
> as belonging to `T`.  A subgroup is computed if a set of generators of the subgroup is
> computed.  A coset is computed if the corresponding subgroup and a coset representative are
> computed.

A straight-line program given as *data* is the list of its instructions: instruction `i` says
how element `i` of the sequence is formed, and carries the mark.  The raw form used here:

* an instruction is `(op, a, b, f)`: `op = 0` is "the generator number `a`", `op = 1` is "the
  product of the elements number `a` and `b`" and `op ≥ 2` is "the inverse of element number
  `a`"; `f ≠ 0` marks the element as belonging to the computed set;
* a program computing a coset is the list of instructions together with the index `σ` of the
  coset representative.

This file gives the semantics on raw permutations (`Algo.slpVals`), the answer that
Observation 11.1.11 extracts from it (`Algo.obsCore`), and the list facts the RAM evaluator of
`Workspace/Algo/SLPEvalRAM.lean` needs.  The products and inverses follow `Algo.rawMul` and
`Algo.rawInv` (Lean's convention, `Workspace/Algo/DESIGN.md`).
-/

namespace Algo

open RAM

/-! ## The raw program and its values -/

/-- One instruction `(op, a, b, f)` of a raw straight-line program (Definition 11.1.10). -/
abbrev RawSLPInstr := ℕ × ℕ × ℕ × ℕ

/-- A raw straight-line program computing a coset: the instructions and the index of the coset
representative (Definition 11.1.10, "a coset representative"). -/
abbrev RawSLP := List RawSLPInstr × ℕ

/-- The element formed by one instruction from the generators `S` and the elements `vals`
formed so far (Definition 11.1.10: a generator, a product of two earlier elements, or the
inverse of an earlier element). -/
def slpStep (S : RawGens) (vals : List RawPerm) (ins : RawSLPInstr) : RawPerm :=
  if ins.1 = 0 then S.getD ins.2.1 []
  else if ins.1 = 1 then rawMul (vals.getD ins.2.1 [], vals.getD ins.2.2.1 [])
  else rawInv (vals.getD ins.2.1 [])

/-- One step of the evaluation: append the element the instruction forms. -/
def slpAcc (S : RawGens) (vals : List RawPerm) (ins : RawSLPInstr) : List RawPerm :=
  vals ++ [slpStep S vals ins]

/-- **The sequence of a straight-line program**: element `i` is formed by instruction `i`. -/
def slpVals (S : RawGens) (prog : List RawSLPInstr) : List RawPerm :=
  prog.foldl (slpAcc S) []

/-- The marked elements, in the order of the sequence (Definition 11.1.10, "marked as
belonging to `T`"). -/
def slpMarked (S : RawGens) (prog : List RawSLPInstr) : List RawPerm :=
  (prog.zip (slpVals S prog)).filterMap (fun p => if p.1.2.2.2 = 0 then none else some p.2)

/-- The well-formedness of a raw program for the generators `S` of degree `n`: the generators
are permutations of `[0, n)`, a generator reference is in range, and every other reference
is to an earlier element (Definition 11.1.10). -/
def SLPValid (n : ℕ) (S : RawGens) (prog : List RawSLPInstr) : Prop :=
  RawGens.WF n S ∧ ∀ i (hi : i < prog.length),
    (prog[i].1 = 0 → prog[i].2.1 < S.length) ∧ (prog[i].1 ≠ 0 → prog[i].2.1 < i) ∧
      (prog[i].1 = 1 → prog[i].2.2.1 < i)

theorem foldl_slpAcc_length (S : RawGens) (l : List RawSLPInstr) :
    ∀ init : List RawPerm, (l.foldl (slpAcc S) init).length = init.length + l.length := by
  induction l with
  | nil => intro init; simp
  | cons x l ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp [slpAcc]
      omega

theorem foldl_slpAcc_take (S : RawGens) (l : List RawSLPInstr) :
    ∀ init : List RawPerm, (l.foldl (slpAcc S) init).take init.length = init := by
  induction l with
  | nil => intro init; simp
  | cons x l ih =>
      intro init
      rw [List.foldl_cons]
      have h := ih (slpAcc S init x)
      have hlen : (slpAcc S init x).length = init.length + 1 := by simp [slpAcc]
      rw [hlen] at h
      have : (List.foldl (slpAcc S) (slpAcc S init x) l).take init.length
          = ((List.foldl (slpAcc S) (slpAcc S init x) l).take (init.length + 1)).take
              init.length := by
        rw [List.take_take]; congr 1; omega
      rw [this, h]
      simp [slpAcc]

@[simp] theorem length_slpVals (S : RawGens) (prog : List RawSLPInstr) :
    (slpVals S prog).length = prog.length := by
  rw [slpVals, foldl_slpAcc_length]; simp

/-- The values of a prefix of the program are a prefix of the values. -/
theorem slpVals_take (S : RawGens) (prog : List RawSLPInstr) (i : ℕ) :
    slpVals S (prog.take i) = (slpVals S prog).take i := by
  rcases Nat.lt_or_ge prog.length i with h | h
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega)]
  · have hsplit : slpVals S prog
        = (prog.drop i).foldl (slpAcc S) (slpVals S (prog.take i)) := by
      conv_lhs => rw [← List.take_append_drop i prog]
      rw [slpVals, List.foldl_append]
      rfl
    have hlen : (slpVals S (prog.take i)).length = i := by simp; omega
    rw [hsplit]
    have := foldl_slpAcc_take S (prog.drop i) (slpVals S (prog.take i))
    rw [hlen] at this
    exact this.symm

/-- **Element `i` is formed by instruction `i` from the earlier elements.** -/
theorem getElem_slpVals (S : RawGens) (prog : List RawSLPInstr) (i : ℕ)
    (hi : i < (slpVals S prog).length) :
    (slpVals S prog)[i] = slpStep S ((slpVals S prog).take i) (prog[i]'(by simpa using hi)) := by
  have hi' : i < prog.length := by simpa using hi
  have h1 : slpVals S (prog.take (i + 1))
      = slpVals S (prog.take i) ++ [slpStep S (slpVals S (prog.take i)) prog[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some, slpVals,
      List.foldl_append]
    rfl
  rw [slpVals_take, slpVals_take] at h1
  have h2 : ((slpVals S prog).take (i + 1))[i]'(by simp; omega) = (slpVals S prog)[i] := by
    simp
  rw [← h2]
  simp only [h1]
  simp

/-- Under validity every element of the sequence is a permutation of `[0, n)`. -/
theorem wf_slpVals {n : ℕ} {S : RawGens} {prog : List RawSLPInstr} (hv : SLPValid n S prog) :
    ∀ i (hi : i < (slpVals S prog).length), RawPerm.WF n ((slpVals S prog)[i]) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hi' : i < prog.length := by simpa using hi
    obtain ⟨h0, h1, h2⟩ := hv.2 i hi'
    rw [getElem_slpVals]
    have hget : ∀ a (ha : a < i), ((slpVals S prog).take i).getD a [] = (slpVals S prog)[a]'(by
        simp; omega) := by
      intro a ha
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    unfold slpStep
    split_ifs with hop hop1
    · have ha := h0 hop
      rw [List.getD_eq_getElem _ _ ha]
      exact hv.1 _ (List.getElem_mem _)
    · rw [hget _ (h1 hop), hget _ (h2 hop1)]
      exact wf_rawMul (ih _ (h1 hop) _) (ih _ (h2 hop1) _)
    · rw [hget _ (h1 hop)]
      exact wf_rawInv (ih _ (h1 hop) _)

/-- The marked elements among the first `i`. -/
theorem slpMarked_take_succ (S : RawGens) (prog : List RawSLPInstr) (i : ℕ)
    (hi : i < prog.length) :
    ((prog.zip (slpVals S prog)).take (i + 1)).filterMap
        (fun p => if p.1.2.2.2 = 0 then none else some p.2)
      = ((prog.zip (slpVals S prog)).take i).filterMap
          (fun p => if p.1.2.2.2 = 0 then none else some p.2) ++
        (if (prog[i]).2.2.2 = 0 then [] else [(slpVals S prog)[i]'(by simpa using hi)]) := by
  have hz : i < (prog.zip (slpVals S prog)).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some, List.filterMap_append]
  congr 1
  simp only [List.getElem_zip]
  split_ifs <;> simp_all

/-! ## Observation 11.1.11, the answer -/

/-- The header of the evaluator's input: the degree `n`, the generators `S` of `G` and the
generators of the kernel of the `G`-action on the window. -/
abbrev ObsHdr := ℕ × (RawGens × RawGens)

/-- **The answer of Observation 11.1.11** from the header and the program: `none` when there
is no program (the coset is empty), and otherwise the marked elements of the sequence
together with the kernel generators, and the representative (element `σ` of the sequence).

> If `Iso_{G^Δ}(x^Δ, y^Δ)` is not empty, in the end we obtain a subset `S ⊆ G` and an element
> `σ ∈ G` [...].  Adding to `S` a set of generators of the kernel of the `G`-action on `Δ` we
> obtain a set of generators of `Aut^Δ_G(x)`; and `Iso^Δ_G(x,y) = Aut^Δ_G(x)σ`. -/
def obsCore (z : ObsHdr × Option RawSLP) : RawCoset :=
  match z.2 with
  | none => none
  | some p => some (slpMarked z.1.2.1 p.1 ++ z.1.2.2, (slpVals z.1.2.1 p.1).getD p.2 [])

/-- The header computed from the group `G = ⟨S⟩` on the domain `dom` and the window `Δ`: the
kernel of the action on `Δ` is the pointwise stabilizer of `Δ` (`Algo.rawPointStab`). -/
def obsHdr (g : (List ℕ × RawGens) × List ℕ) : ObsHdr :=
  (g.1.1.length, (g.1.2, rawPointStab g))

/-- **Observation 11.1.11 as a routine**: the group, the window and (when the coset on the
window is not empty) a straight-line program computing it. -/
def obsWindow (x : ((List ℕ × RawGens) × List ℕ) × Option RawSLP) : RawCoset :=
  obsCore (obsHdr x.1, x.2)

/-! ## The word layout of permutations -/

/-- The words of the encoding of a list of numbers: each number `x` is the block `[1, x]`. -/
def encNats (l : List ℕ) : List ℕ := l.flatMap (fun x => [1, x])

theorem encode_listNat (l : List ℕ) : Enc.encode l = encNats l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      show frame [a] ++ encList Enc.encode l = _
      rw [show encList Enc.encode l = Enc.encode l from rfl, ih]
      simp [encNats, frame]

@[simp] theorem encNats_nil : encNats [] = [] := rfl

theorem encNats_cons (a : ℕ) (l : List ℕ) : encNats (a :: l) = 1 :: a :: encNats l := by
  simp [encNats]

theorem encNats_append (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

@[simp] theorem length_encNats (l : List ℕ) : (encNats l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encNats_cons]; simp [ih]; omega

theorem getD_encNats_odd (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    (encNats l).getD (2 * k + 1) 0 = l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
      rw [encNats_cons]
      cases k with
      | zero => simp
      | succ k =>
          have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
          rw [this]
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact ih (by simpa using hk)

theorem getD_encNats_even (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    (encNats l).getD (2 * k) 0 = 1 := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
      rw [encNats_cons]
      cases k with
      | zero => simp
      | succ k =>
          have : 2 * (k + 1) = 2 * k + 2 := by omega
          rw [this]
          simp only [List.getD_cons_succ]
          exact ih (by simpa using hk)

theorem encNats_set (l : List ℕ) {k : ℕ} (hk : k < l.length) (v : ℕ) :
    (encNats l).set (2 * k + 1) v = encNats (l.set k v) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
      rw [encNats_cons]
      cases k with
      | zero => simp [encNats_cons]
      | succ k =>
          have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
          rw [this]
          simp only [List.set_cons_succ, encNats_cons]
          rw [ih (by simpa using hk)]

theorem encNats_replicate (u : ℕ) : encNats (List.replicate u 0) =
    (List.replicate u [1, 0]).flatten := by
  induction u with
  | zero => rfl
  | succ u ih => rw [List.replicate_succ, encNats_cons, List.replicate_succ, ih]; simp

theorem encNats_replicate_succ (u : ℕ) :
    encNats (List.replicate (u + 1) 0) = encNats (List.replicate u 0) ++ [1, 0] := by
  rw [List.replicate_succ', encNats_append]; rfl

/-! ## Inversion by scattering

The evaluator inverts a permutation `A` by writing `u` at position `A[u]` of a zeroed array, for
`u = 0, 1, ...`. -/

/-- The array after the first `u` writes. -/
def scat (n : ℕ) (A : List ℕ) (u : ℕ) : List ℕ :=
  (List.range u).foldl (fun c k => c.set (A.getD k 0) k) (List.replicate n 0)

theorem scat_zero (n : ℕ) (A : List ℕ) : scat n A 0 = List.replicate n 0 := rfl

theorem scat_succ (n : ℕ) (A : List ℕ) (u : ℕ) :
    scat n A (u + 1) = (scat n A u).set (A.getD u 0) u := by
  rw [scat, List.range_succ, List.foldl_append]; rfl

@[simp] theorem length_scat (n : ℕ) (A : List ℕ) (u : ℕ) : (scat n A u).length = n := by
  induction u with
  | zero => simp [scat_zero]
  | succ u ih => rw [scat_succ, List.length_set, ih]

theorem getElem_scat {n : ℕ} {A : List ℕ} (h : RawPerm.WF n A) :
    ∀ u (hu : u ≤ n) k (hk : k < u), (scat n A u)[A[k]'(by rw [h.length]; omega)]'(by
      rw [length_scat]; exact h.getElem_lt _) = k := by
  intro u
  induction u with
  | zero => intro _ k hk; omega
  | succ u ih =>
      intro hu k hk
      have hAu : A.getD u 0 = A[u]'(by rw [h.length]; omega) :=
        List.getD_eq_getElem _ _ _
      simp only [scat_succ, hAu]
      rcases Nat.lt_or_ge k u with hku | hku
      · have hne : A[u]'(by rw [h.length]; omega) ≠ A[k]'(by rw [h.length]; omega) := by
          intro heq
          have := (List.Nodup.getElem_inj_iff h.nodup).1 heq
          omega
        rw [List.getElem_set_ne hne]
        exact ih (by omega) k hku
      · have hk' : k = u := by omega
        subst hk'
        simp

/-- A well-formed raw permutation takes every value of the domain. -/
theorem mem_of_wf {n : ℕ} {A : List ℕ} (h : RawPerm.WF n A) {j : ℕ} (hj : j < n) : j ∈ A := by
  classical
  have hsub : A.toFinset ⊆ Finset.range n := by
    intro x hx
    simpa using h.lt (List.mem_toFinset.1 hx)
  have hcard : (Finset.range n).card ≤ A.toFinset.card := by
    rw [List.toFinset_card_of_nodup h.nodup, h.length]; simp
  have := Finset.eq_of_subset_of_card_le hsub hcard
  have hj' : j ∈ Finset.range n := by simpa using hj
  rw [← this] at hj'
  exact List.mem_toFinset.1 hj'

/-- **Scattering computes the inverse.** -/
theorem scat_eq_rawInv {n : ℕ} {A : List ℕ} (h : RawPerm.WF n A) : scat n A n = rawInv A := by
  apply List.ext_getElem
  · simp [h.length]
  · intro j hj _
    have hjn : j < n := by simpa using hj
    obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem (mem_of_wf h hjn)
    have hkn : k < n := by rw [← h.length]; exact hk
    have h1 := getElem_scat h n (le_refl _) k hkn
    have hlook : List.lookup j (A.zipIdx 0) = some k := by
      have := lookup_zipIdx_getElem A h.nodup 0 k j hk hkj
      rwa [Nat.add_zero] at this
    have h2 : (rawInv A)[j]'(by simp [h.length]; omega) = k := by
      simp [rawInv, rawInvLookup, hlook]
    subst hkj
    rw [h1, h2]

/-! ## Words of framed blocks of equal length -/

/-- In the encoding of a list whose entries all have `c` words, entry `i` occupies the words
`(c + 1) i, ..., (c + 1) i + c`. -/
theorem encList_drop_take {α : Type*} (f : α → List ℕ) (c : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = c) → ∀ i (hi : i < l.length),
      ((encList f l).drop ((c + 1) * i)).take (c + 1) = frame (f l[i]) := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons a l ih =>
      intro hc i hi
      have ha : (f a).length = c := hc a (by simp)
      cases i with
      | zero =>
          simp only [encList, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
          rw [List.take_append_of_le_length (by simp [frame, ha])]
          rw [List.take_of_length_le (by simp [frame, ha])]
      | succ i =>
          simp only [encList, List.getElem_cons_succ]
          have hlen : (frame (f a)).length = c + 1 := by simp [frame, ha]
          have : (c + 1) * (i + 1) = (frame (f a)).length + (c + 1) * i := by
            rw [hlen]; ring
          rw [this, ← List.drop_drop, List.drop_left]
          exact ih (fun x hx => hc x (by simp [hx])) i (by simpa using hi)

end Algo
