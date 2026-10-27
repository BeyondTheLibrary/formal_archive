import Workspace.Algo.AggNodeCheckedPhaseRAM

/-! # Computing the size of the certificate state

A size cap must be an actual RAM test. For the natural numbers, lists,
options, and products used by this carrier, the encoding size can be
computed by following the encoding's framing rules.
-/
namespace Algo
open RAM RAM.Targets

class AggnSizeRoutine (α : Type*) [Enc α] : Prop where
  polyFun_size : PolyFun (Enc.size : α → ℕ)

instance : AggnSizeRoutine ℕ := ⟨by
  exact (polyFun_natSize.add (polyFun_const 2)).of_eq (fun a => (Small.size_nat a).symm)⟩

instance : AggnSizeRoutine Bool := ⟨by
  exact (PolyFun.ite polyFun_id (polyFun_const 3) (polyFun_const 2)).of_eq
    (fun a => by cases a <;> rfl)⟩

private theorem aggnSize_pair_eq {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    Enc.size (a, b) = Enc.size a + Nat.size (rawLength a) +
      Enc.size b + Nat.size (rawLength b) + 1 := by
  change listSize (frame (Enc.encode a) ++ frame (Enc.encode b)) = _
  rw [listSize_append, listSize_frame, listSize_frame]
  change Enc.size a + (Nat.size (rawLength a) + 1) +
    (Enc.size b + (Nat.size (rawLength b) + 1)) - 1 = _
  omega

instance {α β : Type*} [Enc α] [Enc β] [AggnSizeRoutine α] [AggnSizeRoutine β] :
    AggnSizeRoutine (α × β) := ⟨by
  have hα := (AggnSizeRoutine.polyFun_size (α := α)).add (polyFun_rawLength.comp polyFun_natSize)
  have hβ := (AggnSizeRoutine.polyFun_size (α := β)).add (polyFun_rawLength.comp polyFun_natSize)
  exact (((polyFun_fst.comp hα).add (polyFun_snd.comp hβ)).add
    (polyFun_const 1)).of_eq (fun ⟨a, b⟩ => by dsimp only; rw [aggnSize_pair_eq]; omega)⟩

instance {α : Type*} [Enc α] [AggnSizeRoutine α] : AggnSizeRoutine (Option α) := ⟨by
  have hs : PolyFun (fun z : α × Option α => Enc.size z.1 + 2) :=
    (polyFun_fst.comp AggnSizeRoutine.polyFun_size).add (polyFun_const 2)
  exact ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const 2) hs)).of_eq
      (fun a => by cases a <;> simp only [id_eq, Option.elim_none, Option.elim_some, size_none, size_some_eq])⟩

private def aggnSizeListStep {α : Type*} [Enc α] (p : ℕ × α) : ℕ :=
  p.1 + (Enc.size p.2 + Nat.size (rawLength p.2))

private theorem aggnSizeList_fold {α : Type*} [Enc α] :
    ∀ (l : List α) (x : ℕ), l.foldl (fun x a => aggnSizeListStep (x, a)) x =
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

instance {α : Type*} [Enc α] [AggnSizeRoutine α] : AggnSizeRoutine (List α) := ⟨by
  have he : PolyFun (fun a : α => Enc.size a + Nat.size (rawLength a)) :=
    AggnSizeRoutine.polyFun_size.add (polyFun_rawLength.comp polyFun_natSize)
  have hstep : PolyFun (@aggnSizeListStep α _) := polyFun_fst.add (polyFun_snd.comp he)
  obtain ⟨S, hS, hmono, hs⟩ := polyFun_add.size.exists_polyBound
  have hfold := PolyFun.foldl hstep (hS.comp
    (((polyBound_const 4).mul polyBound_id).add (polyBound_const 4))) (fun x l j => by
      rw [aggnSizeList_fold]
      have hl := (size_take_le j l).trans (size_snd_le' (x, l))
      have hx : Enc.size x ≤ Enc.size (x, l) := size_fst_le' (x, l)
      have hu : Enc.size (Enc.size (l.take j) - 1) ≤ Enc.size (x, l) + 2 := by
        rw [Small.size_nat]
        have := size_le_self (Enc.size (l.take j) - 1)
        omega
      have hp := Combine.size_pair_le x (Enc.size (l.take j) - 1)
      exact (hs (x, Enc.size (l.take j) - 1)).trans (hmono _ _ (by omega)))
  exact (((polyFun_const 1).pair polyFun_id).comp hfold).of_eq (fun l => by
    dsimp only
    rw [aggnSizeList_fold]
    simp only [id_eq]
    have := one_le_size l
    omega)⟩

/-- The complete raw certificate state has a polynomial size test. -/
theorem aggnPolyFun_stateSize : PolyFun (Enc.size : AggnPhaseState → ℕ) :=
  AggnSizeRoutine.polyFun_size

/-- The parent context also has an exact polynomial size test. -/
theorem aggnPolyFun_contextSize : PolyFun (Enc.size : AggnPhaseCtx → ℕ) :=
  AggnSizeRoutine.polyFun_size

/-- A standard quasipolynomial cap has a polynomially computable binary encoding. -/
theorem aggnPolyFun_sizeCap (d : ℕ) : PolyFun (fun n : ℕ => 2 ^ ((Nat.log 2 n + 2) ^ d)) := by
  have he := polyFun_powConst (polyFun_log2.add (polyFun_const 2)) d
  apply (polyFun_const 2).pow he (q := fun m => (m + 1) ^ d)
  · intro n
    apply Nat.pow_le_pow_left
    have := Round.log_succ_le_size n
    omega
  · exact ⟨1, d, fun _ => by simp⟩

end Algo
