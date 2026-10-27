/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the size of an
encoding as a routine with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFLists2
import Workspace.Algo.AggNodeSizeRoutine

/-!
# The size of an encoding, with explicit constants

`Algo.AggnSizeRoutine α` states that `Enc.size : α → ℕ` is a `RAM.PolyFun`, with instances for
`ℕ`, `Bool`, pairs, options and lists. `Explicit.PFSize α` is the same with explicit constants:
the instances are proved as the ones of `Algo.AggnSizeRoutine`, and their constants are closed
expressions in those of the components, which evaluate to numerals at a fixed type.
-/

namespace Explicit

open RAM Algo

/-- **The size of an encoding with explicit constants** (`Algo.AggnSizeRoutine`). -/
class PFSize (α : Type*) [Enc α] where
  k : ℕ
  d : ℕ
  s : ℕ
  e : ℕ
  pf : PF (Enc.size : α → ℕ) k d s e

instance : PFSize ℕ where
  k := 21
  d := 1
  s := 8
  e := 1
  pf := by
    have h := (pf_natSize.pair (PF.const (α := ℕ) (2 : ℕ))).comp pf_add
    exact h.of_eq (fun a => (Small.size_nat a).symm)

instance : PFSize Bool where
  k := 23
  d := 1
  s := 4
  e := 0
  pf := (PF.ite (PF.id (α := Bool)) (PF.const (α := Bool) (3 : ℕ))
    (PF.const (α := Bool) (2 : ℕ))).of_eq (fun a => by cases a <;> rfl)

/-- The constant `1`. -/
theorem pf_one {α : Type*} [Enc α] : PF (fun _ : α => (1 : ℕ)) 10 1 3 0 := PF.const 1

/-- The constant `2`. -/
theorem pf_two {α : Type*} [Enc α] : PF (fun _ : α => (2 : ℕ)) 11 1 4 0 := PF.const 2

/-- The size of a pair (as `Algo.aggnSize_pair_eq`, which is private). -/
theorem size_pair_eq' {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    Enc.size (a, b) = Enc.size a + Nat.size (rawLength a) +
      Enc.size b + Nat.size (rawLength b) + 1 := by
  change listSize (frame (Enc.encode a) ++ frame (Enc.encode b)) = _
  rw [listSize_append, listSize_frame, listSize_frame]
  change Enc.size a + (Nat.size (rawLength a) + 1) +
    (Enc.size b + (Nat.size (rawLength b) + 1)) - 1 = _
  omega

/-- `Enc.size a + Nat.size (rawLength a)`, the size of one framed block. -/
theorem pf_blockSize {α : Type*} [Enc α] {k d s e : ℕ} (h : PF (Enc.size : α → ℕ) k d s e) :
    PF (fun a : α => Enc.size a + Nat.size (rawLength a))
      (k + d + s + e + 40) (max d (max e 1)) (s + 12) (max e 1) := by
  have h := ((h.pair ((pf_rawLength (α := α)).comp pf_natSize)).comp pf_add)
  exact h.mono (by omega) (by omega) (by omega) (by omega)

/-- The size of a pair from the sizes of its components (`Algo.AggnSizeRoutine`, pairs). -/
theorem pf_pairSize {α β : Type*} [Enc α] [Enc β] {k d s e k' d' s' e' : ℕ}
    (ha : PF (Enc.size : α → ℕ) k d s e) (hb : PF (Enc.size : β → ℕ) k' d' s' e') :
    PF (Enc.size : α × β → ℕ) (k + k' + 3 * (d + d' + s + s' + e + e') + 300)
      (max (max d d') (max (max e e') 1)) (s + s' + 2 * (e + e') + 30) (max (max e e') 1) := by
  have hA := ((PF.fst (α := α) (β := β)).comp (pf_blockSize ha)).mono
    (k' := k + 2 * d + s + 2 * e + 50) (d' := max d (max e 1)) (s' := s + 12 + max e 1)
    (e' := max e 1) (by omega) (by omega) (by omega) (by omega)
  have hB := ((PF.snd (α := α) (β := β)).comp (pf_blockSize hb)).mono
    (k' := k' + 2 * d' + s' + 2 * e' + 50) (d' := max d' (max e' 1)) (s' := s' + 12 + max e' 1)
    (e' := max e' 1) (by omega) (by omega) (by omega) (by omega)
  have hAB := (hA.pair hB).mono (k' := k + k' + 2 * (d + d' + s + s' + e + e') + 120)
    (d' := max (max d d') (max (max e e') 1)) (s' := s + s' + 16 + max (max e e') 1)
    (e' := max (max e e') 1) (by omega) (by omega) (by omega) (by omega)
  have hS := (hAB.comp pf_add).mono (k' := k + k' + 2 * (d + d' + s + s' + e + e') + 160)
    (d' := max (max d d') (max (max e e') 1)) (s' := s + s' + 18 + 2 * max (max e e') 1)
    (e' := max (max e e') 1) (by omega) (by omega) (by omega) (by omega)
  have h2 := ((hS.pair (pf_one (α := α × β))).comp pf_add).mono
    (k' := k + k' + 3 * (d + d' + s + s' + e + e') + 300)
    (d' := max (max d d') (max (max e e') 1)) (s' := s + s' + 2 * (e + e') + 30)
    (e' := max (max e e') 1)
    (by omega) (by omega) (by omega) (by omega)
  refine h2.of_eq (g := (Enc.size : α × β → ℕ)) (fun ab => ?_)
  obtain ⟨a, b⟩ := ab
  show Enc.size a + Nat.size (rawLength a) + (Enc.size b + Nat.size (rawLength b)) + 1 = _
  rw [size_pair_eq']
  omega

instance {α β : Type*} [Enc α] [Enc β] [PFSize α] [PFSize β] : PFSize (α × β) where
  k := PFSize.k α + PFSize.k β + 3 * (PFSize.d α + PFSize.d β + PFSize.s α + PFSize.s β +
    PFSize.e α + PFSize.e β) + 300
  d := max (max (PFSize.d α) (PFSize.d β)) (max (max (PFSize.e α) (PFSize.e β)) 1)
  s := PFSize.s α + PFSize.s β + 2 * (PFSize.e α + PFSize.e β) + 30
  e := max (max (PFSize.e α) (PFSize.e β)) 1
  pf := pf_pairSize PFSize.pf PFSize.pf

/-- A `PFSize` instance whose constants are read off the type of the proof. -/
def PFSize.ofPF {α : Type*} [Enc α] {k d s e : ℕ} (h : PF (Enc.size : α → ℕ) k d s e) :
    PFSize α := ⟨k, d, s, e, h⟩

instance {α : Type*} [Enc α] [PFSize α] : PFSize (Option α) := PFSize.ofPF <| by
  have hs := (((PF.fst (α := α) (β := Option α)).comp (PFSize.pf (α := α))).pair
    (pf_two (α := α × Option α))).comp pf_add
  exact ((PF.id.pair PF.id).comp (PF.optionElim (pf_two (α := Option α)) hs)).of_eq
    (fun a => by
      cases a <;> simp only [id_eq, Option.elim_none, Option.elim_some, size_none,
        size_some_eq])

/-- One round of the size of a list (as `Algo.aggnSizeListStep`, which is private). -/
def sizeListStep {α : Type*} [Enc α] (p : ℕ × α) : ℕ :=
  p.1 + (Enc.size p.2 + Nat.size (rawLength p.2))

theorem sizeList_fold {α : Type*} [Enc α] :
    ∀ (l : List α) (x : ℕ), l.foldl (fun x a => sizeListStep (x, a)) x =
      x + (Enc.size l - 1) := by
  intro l
  induction l with
  | nil => intro x; simp [size_nil]
  | cons a rest ih =>
    intro x
    rw [List.foldl_cons, ih, size_cons_eq, listSize_frame]
    have h := one_le_size rest
    change x + (Enc.size a + Nat.size (rawLength a)) + (Enc.size rest - 1) =
      x + (Enc.size a + (Nat.size (rawLength a) + 1) + Enc.size rest - 1 - 1)
    omega

theorem natSize_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.2
  have ha : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have hb : b < 2 ^ Nat.size b := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

instance {α : Type*} [Enc α] [PFSize α] : PFSize (List α) := PFSize.ofPF <| by
  have hstep := (PF.fst (α := ℕ) (β := α)).pair
    ((PF.snd (α := ℕ) (β := α)).comp (pf_blockSize (PFSize.pf (α := α)))) |>.comp pf_add
  have hfold := PF.foldl (ka := 2) (da := 1) (f := @sizeListStep α _) hstep (fun x l j => by
    rw [sizeList_fold]
    have hl : Enc.size (l.take j) ≤ Enc.size ((x, l) : ℕ × List α) :=
      (size_take_le j l).trans (size_snd_le' (x, l))
    have hx : Enc.size x ≤ Enc.size ((x, l) : ℕ × List α) := size_fst_le' (x, l)
    have h1 := natSize_add_le x (Enc.size (l.take j) - 1)
    have h2 := size_le_self (Enc.size (l.take j) - 1)
    have h3 : Enc.size (x + (Enc.size (l.take j) - 1)) =
      Nat.size (x + (Enc.size (l.take j) - 1)) + 2 := Small.size_nat _
    have h4 : Enc.size x = Nat.size x + 2 := Small.size_nat _
    show _ ≤ 2 ^ 2 * (Enc.size ((x, l) : ℕ × List α) + 1) ^ 1
    rw [pow_one]
    omega)
  exact (((pf_one (α := List α)).pair PF.id).comp hfold).of_eq (fun l => by
    dsimp only
    rw [sizeList_fold]
    have := one_le_size l
    omega)

end Explicit
