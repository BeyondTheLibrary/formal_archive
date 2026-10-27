import Workspace.Algo.SLPEval
import Workspace.Machine.LayoutExact

/-!
# The word layout of the evaluator's input (Observation 11.1.11)

The RAM evaluator of `Workspace/Algo/SLPEvalRAM.lean` reads its input
`((n, (S, Ker)), prog?)` in place.  This file records where each piece lies in the list
`|E| :: E` (`E` the encoding), which is the list the workspace convention starts from
(`RAM.Layout.initMemAt_eq_memAt`), and the facts about segments of lists the evaluator's
invariants use.
-/

namespace Algo
namespace SLPRAM

open RAM

/-! ## Segments -/

/-- The segment of `c` words of `L` from index `p`. -/
def seg (L : List ℕ) (p c : ℕ) : List ℕ := (L.drop p).take c

theorem getD_seg_eq {L : List ℕ} {p c k : ℕ} (hk : k < c) :
    (seg L p c).getD k 0 = L.getD (p + k) 0 := by
  rw [seg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hk, List.getElem?_drop]

theorem getD_of_seg {L X : List ℕ} {p c k : ℕ} (h : seg L p c = X) (hk : k < c) :
    L.getD (p + k) 0 = X.getD k 0 := by
  rw [← getD_seg_eq hk, h]

theorem seg_seg {L X : List ℕ} {p c p' c' : ℕ} (h : seg L p c = X) (hc : p' + c' ≤ c) :
    seg L (p + p') c' = seg X p' c' := by
  rw [← h, seg, seg, seg, List.drop_take, List.take_take, ← List.drop_drop]
  congr 1
  omega

theorem seg_append_left (A B : List ℕ) {p c : ℕ} (h : p + c ≤ A.length) :
    seg (A ++ B) p c = seg A p c := by
  rw [seg, seg, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

theorem seg_append_right (A B : List ℕ) (p c : ℕ) :
    seg (A ++ B) (A.length + p) c = seg B p c := by
  rw [seg, seg, ← List.drop_drop, List.drop_left]

theorem seg_whole (A B : List ℕ) : seg (A ++ B) A.length B.length = B := by
  rw [← Nat.add_zero A.length, seg_append_right, seg, List.drop_zero, List.take_length]

theorem seg_self (A : List ℕ) : seg A 0 A.length = A := by
  rw [seg, List.drop_zero, List.take_length]

theorem seg_set_of_lt {L : List ℕ} {p c t : ℕ} (x : ℕ) (h : t < p ∨ p + c ≤ t) :
    seg (L.set t x) p c = seg L p c := by
  apply List.ext_getElem?
  intro k
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with hk
  · rw [List.getElem?_set_ne (by omega)]
  · rfl

/-- The encoding of the `c`-word entry `i` of a list of blocks. -/
theorem seg_encList {α : Type*} (f : α → List ℕ) (c : ℕ) (l : List α)
    (hc : ∀ x ∈ l, (f x).length = c) (i : ℕ) (hi : i < l.length) :
    seg (encList f l) ((c + 1) * i) (c + 1) = frame (f l[i]) :=
  encList_drop_take f c l hc i hi

theorem length_encList_const {α : Type*} (f : α → List ℕ) (c : ℕ) (l : List α)
    (hc : ∀ x ∈ l, (f x).length = c) : (encList f l).length = (c + 1) * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [encList, List.length_append, frame, List.length_cons,
        hc a (by simp), ih (fun x hx => hc x (by simp [hx]))]
      ring

/-! ## Permutations in the workspace -/

/-- **A permutation `v` stored at index `p`** of the list: the words `p, ..., p + 2|v| - 1` are
the blocks `[1, v[u]]`. -/
def SlotAt (L : List ℕ) (p : ℕ) (v : List ℕ) : Prop :=
  p + 2 * v.length ≤ L.length ∧ seg L p (2 * v.length) = encNats v

theorem SlotAt.getD {L : List ℕ} {p : ℕ} {v : List ℕ} (h : SlotAt L p v) {x : ℕ}
    (hx : x < v.length) : L.getD (p + (2 * x + 1)) 0 = v[x] := by
  rw [getD_of_seg h.2 (by omega), getD_encNats_odd _ hx]

theorem SlotAt.append {L : List ℕ} {p : ℕ} {v : List ℕ} (h : SlotAt L p v) (M : List ℕ) :
    SlotAt (L ++ M) p v :=
  ⟨by simp; have := h.1; omega, by rw [seg_append_left _ _ h.1]; exact h.2⟩

theorem SlotAt.set {L : List ℕ} {p : ℕ} {v : List ℕ} (h : SlotAt L p v) {t : ℕ} (x : ℕ)
    (ht : t < p ∨ p + 2 * v.length ≤ t) : SlotAt (L.set t x) p v :=
  ⟨by simp; exact h.1, by rw [seg_set_of_lt x ht]; exact h.2⟩

theorem slotAt_append_self (L : List ℕ) (v : List ℕ) : SlotAt (L ++ encNats v) L.length v :=
  ⟨by simp, by
    have := seg_whole L (encNats v)
    rw [length_encNats] at this
    exact this⟩

/-- A write into the middle block of a three-block list. -/
theorem set_append3 (A B C : List ℕ) {j : ℕ} (hj : j < B.length) (x : ℕ) :
    (A ++ B ++ C).set (A.length + j) x = A ++ B.set j x ++ C := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_left _ _ hj, List.append_assoc]

theorem set_append2 (A B : List ℕ) {j : ℕ} (_hj : j < B.length) (x : ℕ) :
    (A ++ B).set (A.length + j) x = A ++ B.set j x := by
  rw [List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left]

theorem getD_set_ne (l : List ℕ) {i k : ℕ} (h : k ≠ i) (x : ℕ) :
    (l.set i x).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem getD_set_eq (l : List ℕ) {i : ℕ} (h : i < l.length) (x : ℕ) :
    (l.set i x).getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

theorem SlotAt.getD' {L : List ℕ} {p : ℕ} {v : List ℕ} (h : SlotAt L p v) {x : ℕ}
    (hx : x < v.length) : L.getD (p + (2 * x + 1)) 0 = v.getD x 0 := by
  rw [h.getD hx, List.getD_eq_getElem _ _ hx]

theorem getD_prefix {L M : List ℕ} {k : ℕ} (h : k < L.length) :
    (L ++ M).getD k 0 = L.getD k 0 := List.getD_append _ _ _ _ h

theorem take_succ_getD (l : List ℕ) {u : ℕ} (hu : u < l.length) :
    l.take (u + 1) = l.take u ++ [l.getD u 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hu, List.getD_eq_getElem _ _ hu]; rfl

theorem encNats_singleton (x : ℕ) : encNats [x] = [1, x] := rfl

theorem rawMul_getD (A B : List ℕ) {u : ℕ} (hu : u < B.length) (hx : B.getD u 0 < A.length) :
    (rawMul (A, B)).getD u 0 = A.getD (B.getD u 0) 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu)]
  simp only [rawMul, List.getElem_map, rawApply]
  rw [List.getD_eq_getElem _ _ hu] at hx ⊢
  rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hx]

/-! ## The input -/

/-- The words of the input as the workspace convention lays them out: the length, then the
encoding. -/
def inWords (z : ObsHdr × Option RawSLP) : List ℕ :=
  (Enc.encode z).length :: Enc.encode z

section Input

variable (n : ℕ) (S K : RawGens) (prog : List RawSLPInstr) (σ : ℕ)

/-- The words of the input with a program. -/
theorem encode_some :
    Enc.encode (((n, (S, K)), some (prog, σ)) : ObsHdr × Option RawSLP) =
      [(Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
        (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
        Enc.encode S ++ [(Enc.encode K).length] ++ Enc.encode K ++
        [(Enc.encode prog).length + 4, 1, (Enc.encode prog).length] ++ Enc.encode prog ++
        [1, σ] := by
  show frame (frame [n] ++ frame (frame (Enc.encode S) ++ frame (Enc.encode K))) ++
    frame (1 :: (frame (Enc.encode prog) ++ frame [σ])) = _
  simp [frame]
  omega

/-- The words of the input without a program. -/
theorem encode_none :
    Enc.encode (((n, (S, K)), none) : ObsHdr × Option RawSLP) =
      [(Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
        (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
        Enc.encode S ++ [(Enc.encode K).length] ++ Enc.encode K ++ [1, 0] := by
  show frame (frame [n] ++ frame (frame (Enc.encode S) ++ frame (Enc.encode K))) ++
    frame [0] = _
  simp [frame]
  omega

/-- The common head of the input words: everything up to the kernel generators. -/
def headW (E : ℕ) : List ℕ :=
  [E, (Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
    (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
    Enc.encode S ++ [(Enc.encode K).length] ++ Enc.encode K

theorem length_headW (E : ℕ) :
    (headW n S K E).length = 7 + (Enc.encode S).length + (Enc.encode K).length := by
  simp [headW]; omega

theorem inWords_some :
    inWords ((n, (S, K)), some (prog, σ)) =
      headW n S K (Enc.encode (((n, (S, K)), some (prog, σ)) : ObsHdr × Option RawSLP)).length
        ++ ([(Enc.encode prog).length + 4, 1, (Enc.encode prog).length] ++ Enc.encode prog ++
          [1, σ]) := by
  rw [inWords]
  conv_lhs => rw [encode_some]
  simp only [headW, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
    and_true]
  rw [encode_some]; simp

theorem inWords_none :
    inWords ((n, (S, K)), none) =
      headW n S K (Enc.encode (((n, (S, K)), none) : ObsHdr × Option RawSLP)).length ++ [1, 0] := by
  rw [inWords]
  conv_lhs => rw [encode_none]
  simp only [headW, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
    and_true]
  rw [encode_none]; simp

variable {n S K} in
theorem headW_getD_zero (E : ℕ) (T : List ℕ) : (headW n S K E ++ T).getD 0 0 = E := by
  simp [headW]

theorem headW_getD_n (E : ℕ) (T : List ℕ) : (headW n S K E ++ T).getD 3 0 = n := by
  simp [headW]

theorem headW_getD_LS (E : ℕ) (T : List ℕ) :
    (headW n S K E ++ T).getD 5 0 = (Enc.encode S).length := by
  simp [headW]

theorem headW_getD_LK (E : ℕ) (T : List ℕ) :
    (headW n S K E ++ T).getD (6 + (Enc.encode S).length) 0 = (Enc.encode K).length := by
  have : 6 + (Enc.encode S).length = ([E, (Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
      (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
      Enc.encode S).length := by simp; omega
  rw [this]
  simp [headW]

theorem headW_seg_S (E : ℕ) (T : List ℕ) :
    seg (headW n S K E ++ T) 6 (Enc.encode S).length = Enc.encode S := by
  have h : headW n S K E ++ T = [E, (Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
      (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
      (Enc.encode S ++ ([(Enc.encode K).length] ++ Enc.encode K ++ T)) := by
    simp [headW]
  rw [h, show (6 : ℕ) = [E, (Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
      (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length].length + 0 from rfl,
    seg_append_right, seg, List.drop_zero, List.take_left]

theorem headW_seg_K (E : ℕ) (T : List ℕ) :
    seg (headW n S K E ++ T) (7 + (Enc.encode S).length) (Enc.encode K).length =
      Enc.encode K := by
  have h : headW n S K E ++ T = ([E, (Enc.encode S).length + (Enc.encode K).length + 5, 1, n,
      (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
      Enc.encode S ++ [(Enc.encode K).length]) ++ (Enc.encode K ++ T) := by
    simp [headW]
  have hl : 7 + (Enc.encode S).length = ([E, (Enc.encode S).length + (Enc.encode K).length + 5,
      1, n, (Enc.encode S).length + (Enc.encode K).length + 2, (Enc.encode S).length] ++
      Enc.encode S ++ [(Enc.encode K).length]).length + 0 := by simp; omega
  rw [h, hl, seg_append_right, seg, List.drop_zero, List.take_left]

theorem headW_getD_tail (E : ℕ) (T : List ℕ) (k : ℕ) :
    (headW n S K E ++ T).getD (7 + (Enc.encode S).length + (Enc.encode K).length + k) 0 =
      T.getD k 0 := by
  rw [← length_headW n S K E, List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem progW_getD (T : List ℕ) (k : ℕ) :
    ([(Enc.encode prog).length + 4, 1, (Enc.encode prog).length] ++ Enc.encode prog ++
        [1, σ] ++ T).getD (3 + (Enc.encode prog).length + k) 0 = ([1, σ] ++ T).getD k 0 := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc [_, _, _]]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  congr 1
  simp; omega

theorem progW_seg :
    seg ([(Enc.encode prog).length + 4, 1, (Enc.encode prog).length] ++ Enc.encode prog ++
        [1, σ]) 3 (Enc.encode prog).length = Enc.encode prog := by
  rw [List.append_assoc, show (3 : ℕ) = [(Enc.encode prog).length + 4, 1,
      (Enc.encode prog).length].length + 0 from rfl, seg_append_right, seg, List.drop_zero,
    List.take_left]

/-! ## Generators and instructions inside the input -/

theorem length_encode_perm (p : RawPerm) : (Enc.encode p).length = 2 * p.length := by
  rw [encode_listNat, length_encNats]

theorem length_encode_gens {S : RawGens} (hS : RawGens.WF n S) :
    (Enc.encode S).length = (2 * n + 1) * S.length :=
  length_encList_const Enc.encode (2 * n) S (fun x hx => by
    rw [length_encode_perm, (hS x hx).length])

theorem seg_encode_gens {S : RawGens} (hS : RawGens.WF n S) (j : ℕ) (hj : j < S.length) :
    seg (Enc.encode S) ((2 * n + 1) * j + 1) (2 * n) = encNats S[j] := by
  have h := seg_encList Enc.encode (2 * n) S (fun x hx => by
    rw [length_encode_perm, (hS x hx).length]) j hj
  have h2 := seg_seg (p' := 1) (c' := 2 * n) h (by omega)
  change seg (encList Enc.encode S) _ _ = _
  rw [h2, frame, show ((Enc.encode S[j]).length :: Enc.encode S[j])
      = [(Enc.encode S[j]).length] ++ Enc.encode S[j] from rfl,
    show (1 : ℕ) = [(Enc.encode S[j]).length].length + 0 from rfl,
    seg_append_right, seg, List.drop_zero,
    encode_listNat, List.take_of_length_le (by simp [(hS _ (List.getElem_mem hj)).length])]

theorem length_encode_prog (prog : List RawSLPInstr) :
    (Enc.encode prog).length = 11 * prog.length :=
  length_encList_const Enc.encode 10 prog (fun _ _ => rfl)

theorem seg_encode_prog (prog : List RawSLPInstr) (i : ℕ) (hi : i < prog.length) :
    seg (Enc.encode prog) (11 * i) 11 =
      [10, 1, prog[i].1, 7, 1, prog[i].2.1, 4, 1, prog[i].2.2.1, 1, prog[i].2.2.2] :=
  seg_encList Enc.encode 10 prog (fun _ _ => rfl) i hi

end Input

end SLPRAM
end Algo
