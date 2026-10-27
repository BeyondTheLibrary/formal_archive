import Mathlib.Data.List.GetD
import Workspace.Machine.RAM
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card

/-!
# Encoding data for the RAM

A RAM computation starts from a memory and ends in a memory, so the objects the paper's
algorithms take and return have to be laid out in registers.  We fix the following convention,
once and for all.

* **Input and output convention.**  A list `l : List ℕ` occupies registers `0, 1, ..., l.length`:
  register `0` holds the length `l.length` and register `i + 1` holds the `i`-th entry
  (`RAM.initMem`, `RAM.OutputAt`).
* **Initial memory.**  Every register outside the input region holds `0` (`RAM.initMem` again).
  This is the usual convention (Cook-Reckhow: the machine starts with all registers zero except
  for the input).  It is a real choice, and the reason for it is discussed in
  `Workspace/Machine/DESIGN.md`: the *top-level* semantics starts from a zeroed memory, but the
  compositional specifications of `Workspace/Machine/Combinators.lean` never assume anything
  about registers outside the input region, so that a program may be started in the middle of
  another program's dirty memory.  Reading the output only inspects registers `0 .. length`, so
  a program is free to leave garbage anywhere else.
* **Size.**  The size of a list of naturals is its total bit length,
  `listSize l = 1 + ∑ x ∈ l, (Nat.size x + 1)`: one bit per entry as a separator, `Nat.size x`
  bits for the entry itself, and one for the length field.  The size of an encodable object is
  the size of its encoding (`Enc.size`).

Structured data is encoded by *self-delimiting* concatenation: `frame xs = xs.length :: xs`
prefixes a block by its length, so that a concatenation of frames can be parsed uniquely
(`frame_append_inj`).  Injectivity of every encoding below is proved; decoding is never needed,
because a program's specification refers to the encoding of the intended output.
-/

namespace RAM

/-! ## The memory convention -/

/-- The initial memory holding the list `l`: register `0` is the length, registers `1 .. n` the
entries, every other register is `0`. -/
def initMem (l : List ℕ) : Mem := fun a => if a = 0 then l.length else l.getD (a - 1) 0

/-- The initial configuration on input `l`: program counter `0`, memory `initMem l`. -/
def Config.init (l : List ℕ) : Config := ⟨0, initMem l⟩

/-- The memory `m` holds the list `l` in the output convention. -/
def OutputAt (m : Mem) (l : List ℕ) : Prop :=
  m 0 = l.length ∧ ∀ i, i < l.length → m (i + 1) = l.getD i 0

theorem outputAt_initMem (l : List ℕ) : OutputAt (initMem l) l := by
  refine ⟨by simp [initMem], fun i hi => ?_⟩
  simp [initMem]

/-- The output convention determines the list: two lists displayed by the same memory are
equal. -/
theorem OutputAt.unique {m : Mem} {l l' : List ℕ} (h : OutputAt m l) (h' : OutputAt m l') :
    l = l' := by
  have hlen : l.length = l'.length := by rw [← h.1, h'.1]
  apply List.ext_getElem hlen
  intro i hi hi'
  have := h.2 i hi
  have h2 := h'.2 i hi'
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [List.getD_eq_getElem _ _ hi'] at h2
  rw [← this, ← h2]

/-- Every register of an initial memory is bounded by the length and the entries of the input;
this is the hypothesis of the bit-growth lemma `RAM.mem_le_run`. -/
theorem initMem_le (l : List ℕ) (B : ℕ) (hlen : l.length ≤ B) (hmem : ∀ x ∈ l, x ≤ B) :
    ∀ a, initMem l a ≤ B := by
  intro a
  unfold initMem
  split
  · exact hlen
  · rcases lt_or_ge (a - 1) l.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hmem _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact Nat.zero_le _

/-! ## Sizes -/

/-- The total bit length of a list of naturals, our measure of input size. -/
def listSize (l : List ℕ) : ℕ := 1 + (l.map (fun x => Nat.size x + 1)).sum

@[simp] theorem listSize_nil : listSize [] = 1 := by simp [listSize]

theorem listSize_cons (x : ℕ) (l : List ℕ) :
    listSize (x :: l) = listSize l + (Nat.size x + 1) := by
  simp [listSize]; omega

/-- A list is shorter than its bit length. -/
theorem length_lt_listSize (l : List ℕ) : l.length < listSize l := by
  induction l with
  | nil => simp
  | cons x l ih => rw [listSize_cons]; simp; omega

/-- If all entries of `l` are at most `B`, its bit length is at most
`1 + l.length * (Nat.size B + 1)`. -/
theorem listSize_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) :
    listSize l ≤ 1 + l.length * (Nat.size B + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx : Nat.size x ≤ Nat.size B := Nat.size_le_size (h x (by simp))
      have := ih (fun y hy => h y (by simp [hy]))
      rw [listSize_cons]
      simp only [List.length_cons]
      have : (l.length + 1) * (Nat.size B + 1) = l.length * (Nat.size B + 1) + (Nat.size B + 1) :=
        by ring
      omega

theorem listSize_append (l l' : List ℕ) : listSize (l ++ l') = listSize l + listSize l' - 1 := by
  induction l with
  | nil => simp [listSize]
  | cons x l ih =>
      have := length_lt_listSize l'
      rw [List.cons_append, listSize_cons, listSize_cons, ih]
      have : 1 ≤ listSize l' := by omega
      omega

/-! ## Encodings -/

/-- `frame xs` prefixes the block `xs` by its length, making concatenations of blocks uniquely
parsable (`frame_append_inj`). -/
def frame (xs : List ℕ) : List ℕ := xs.length :: xs

theorem frame_append_inj {xs ys r s : List ℕ} (h : frame xs ++ r = frame ys ++ s) :
    xs = ys ∧ r = s := by
  simp only [frame, List.cons_append, List.cons.injEq] at h
  exact List.append_inj h.2 h.1

theorem listSize_frame (xs : List ℕ) :
    listSize (frame xs) = listSize xs + (Nat.size xs.length + 1) := by
  rw [frame, listSize_cons]

/-- Data with a RAM encoding: an injective map to lists of naturals. -/
class Enc (α : Type*) where
  /-- The encoding of an element as a list of register values. -/
  encode : α → List ℕ
  /-- Encodings determine the element. -/
  encode_injective : Function.Injective encode

export Enc (encode)

/-- The size of an encodable object: the total bit length of its encoding. -/
def Enc.size {α : Type*} [Enc α] (a : α) : ℕ := listSize (Enc.encode a)

instance : Enc ℕ where
  encode n := [n]
  encode_injective := by intro a b h; simpa using h

instance : Enc Bool where
  encode b := [if b then 1 else 0]
  encode_injective := by
    intro a b h
    simp only [List.cons.injEq] at h
    cases a <;> cases b <;> simp_all

instance (n : ℕ) : Enc (Fin n) where
  encode i := [i.val]
  encode_injective := by
    intro a b h
    simp only [List.cons.injEq] at h
    exact Fin.ext h.1

instance {α β : Type*} [Enc α] [Enc β] : Enc (α × β) where
  encode p := frame (encode p.1) ++ frame (encode p.2)
  encode_injective := by
    intro p q h
    obtain ⟨h1, h2⟩ := frame_append_inj h
    obtain ⟨h3, -⟩ := frame_append_inj (xs := encode p.2) (ys := encode q.2) (r := []) (s := [])
      (by simpa using h2)
    exact Prod.ext (Enc.encode_injective h1) (Enc.encode_injective h3)

instance {α : Type*} [Enc α] : Enc (Option α) where
  encode
    | none => [0]
    | some a => 1 :: encode a
  encode_injective := by
    intro a b h
    cases a <;> cases b <;> simp_all
    exact Enc.encode_injective h

/-- The encoding of a list: the concatenation of the framed encodings of its entries. -/
def encList {α : Type*} (f : α → List ℕ) : List α → List ℕ
  | [] => []
  | a :: l => frame (f a) ++ encList f l

theorem encList_injective {α : Type*} {f : α → List ℕ} (hf : Function.Injective f) :
    Function.Injective (encList f) := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons b l' => simp [encList, frame] at h
  | cons a l ih =>
      intro l' h
      cases l' with
      | nil => simp [encList, frame] at h
      | cons b l' =>
          simp only [encList] at h
          obtain ⟨h1, h2⟩ := frame_append_inj h
          rw [hf h1, ih h2]

instance {α : Type*} [Enc α] : Enc (List α) where
  encode := encList encode
  encode_injective := encList_injective Enc.encode_injective

/-- A function on `Fin n` is encoded as the array of its values. -/
instance {n : ℕ} {α : Type*} [Enc α] : Enc (Fin n → α) where
  encode f := encList encode (List.ofFn f)
  encode_injective := by
    intro f g h
    have := encList_injective (f := (Enc.encode : α → List ℕ)) Enc.encode_injective h
    exact List.ofFn_injective this

/-- A permutation of `Fin n` is encoded as the array of its images: the `i`-th entry is
`σ i`. -/
instance {n : ℕ} : Enc (Equiv.Perm (Fin n)) where
  encode σ := encode (fun i => σ i : Fin n → Fin n)
  encode_injective := by
    intro σ τ h
    have := Enc.encode_injective (α := Fin n → Fin n) h
    exact Equiv.ext (fun i => congrFun this i)

/-! ## Size bounds

The bounds the later sections need: an array of `n` values below `m` has encoding size between
`n` and `O(n log m)`. -/

theorem listSize_encList_le {α : Type*} [Enc α] (l : List α) (S : ℕ)
    (h : ∀ a ∈ l, Enc.size a ≤ S) :
    listSize (encList encode l) ≤ 1 + l.length * (S + Nat.size S + 1) := by
  induction l with
  | nil => simp [encList]
  | cons a l ih =>
      have ha : Enc.size a ≤ S := h a (by simp)
      have hrest := ih (fun b hb => h b (by simp [hb]))
      rw [encList, listSize_append, listSize_frame]
      have hlen : Nat.size (encode a).length ≤ Nat.size S := by
        apply Nat.size_le_size
        have := length_lt_listSize (encode a)
        have : (encode a).length < Enc.size a := this
        omega
      have hsz : listSize (encode a) = Enc.size a := rfl
      have hexp : (l.length + 1) * (S + Nat.size S + 1)
          = l.length * (S + Nat.size S + 1) + (S + Nat.size S + 1) := by ring
      simp only [List.length_cons]
      have h1 : 1 ≤ listSize (encList encode l) := by
        have := length_lt_listSize (encList encode l); omega
      omega

/-- An array of `n` entries has encoding size larger than `n`. -/
theorem lt_size_pi {n : ℕ} {α : Type*} [Enc α] (f : Fin n → α) :
    n < Enc.size f := by
  have key : ∀ l : List α, l.length ≤ (encList Enc.encode l).length := by
    intro l
    induction l with
    | nil => simp [encList]
    | cons a l ih => simp only [encList, List.length_append, List.length_cons, frame]; omega
  have h := key (List.ofFn f)
  rw [List.length_ofFn] at h
  have h2 := length_lt_listSize (encList Enc.encode (List.ofFn f))
  have hsz : Enc.size f = listSize (encList Enc.encode (List.ofFn f)) := rfl
  omega

/-- `Nat.size m ≤ m`: a number needs at most that many bits. -/
theorem size_le_self (m : ℕ) : Nat.size m ≤ m := Nat.size_le.2 (Nat.lt_two_pow_self)

/-- A permutation of `Fin n` has encoding size at most `1 + n * (2 * Nat.size n + 5)`, that is,
`O(n log n)`. -/
theorem size_perm_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Enc.size σ ≤ 1 + n * (2 * Nat.size n + 5) := by
  have hentry : ∀ a ∈ List.ofFn (fun i => σ i : Fin n → Fin n), Enc.size a ≤ Nat.size n + 2 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    show Enc.size (σ i) ≤ Nat.size n + 2
    have hv : Enc.size (σ i) = 1 + (Nat.size (σ i : ℕ) + 1) := by
      simp [Enc.size, listSize, Enc.encode]
    have hlt : (σ i : ℕ) ≤ n := le_of_lt (σ i).isLt
    have := Nat.size_le_size hlt
    omega
  have hmain := listSize_encList_le (List.ofFn (fun i => σ i : Fin n → Fin n))
    (Nat.size n + 2) hentry
  rw [List.length_ofFn] at hmain
  have hsz : Enc.size σ = listSize (encList Enc.encode
      (List.ofFn (fun i => σ i : Fin n → Fin n))) := rfl
  have hss : Nat.size (Nat.size n + 2) ≤ Nat.size n + 2 := size_le_self _
  have hmul : n * (Nat.size n + 2 + Nat.size (Nat.size n + 2) + 1)
      ≤ n * (2 * Nat.size n + 5) := Nat.mul_le_mul_left _ (by omega)
  omega

end RAM
