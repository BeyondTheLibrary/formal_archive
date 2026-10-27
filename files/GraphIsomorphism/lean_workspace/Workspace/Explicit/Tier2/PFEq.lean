/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: membership and
equality of lists with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFLookup

/-!
# Membership and equality of lists, with explicit constants

The `Explicit.PF` forms of `RAM.polyFun_listMem` and `RAM.polyFun_listEq` (as `Explicit.PFB`,
for any entry type with an equality test), and of `RAM.polyFun_natListMem`,
`RAM.polyFun_listNatEq` and `RAM.polyFun_listListNatEq` with numeral constants.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `RAM.polyFun_listMem`. -/
def PF.listMemB [DecidableEq α] {k d s e : ℕ}
    (heq : PF (fun q : α × α => decide (q.1 = q.2)) k d s e) :
    PFB (fun p : α × List α => decide (p.1 ∈ p.2)) := PFB.of <| by
  have hcond := PF.ite ((PF.fst (α := Bool × α) (β := α)).comp PF.fst)
    (PF.const (α := (Bool × α) × α) true)
    ((((PF.fst (α := Bool × α) (β := α)).comp PF.snd).pair PF.snd).comp heq)
  have hf := (hcond.pair ((PF.fst (α := Bool × α) (β := α)).comp PF.snd)).of_eq
    (g := fun q : (Bool × α) × α => ((q.1.1 || decide (q.1.2 = q.2) : Bool), q.1.2))
    (fun q => by cases h : q.1.1 <;> simp [h])
  have hmain := PF.foldl (ka := 3) (da := 1) hf (fun x r j => by
    obtain ⟨b, y⟩ := x
    rw [memFold_eq]
    have h1 : Enc.size ((((b || decide (y ∈ r.take j) : Bool)), y) : Bool × α)
        ≤ 2 * Enc.size ((b || decide (y ∈ r.take j) : Bool)) + 2 * Enc.size y :=
      Combine.size_pair_le _ _
    have h2 : Enc.size ((b || decide (y ∈ r.take j) : Bool)) ≤ 3 := Combine.size_bool_le _
    have h3 : Enc.size y ≤ Enc.size ((b, y) : Bool × α) := Combine.size_snd_le b y
    have h4 : Enc.size ((b, y) : Bool × α)
        ≤ Enc.size ((((b, y) : Bool × α), r) : (Bool × α) × List α) :=
      Combine.size_fst_le _ r
    show Enc.size ((((b || decide (y ∈ r.take j) : Bool)), y) : Bool × α) ≤
      2 ^ 3 * (Enc.size ((((b, y) : Bool × α), r) : (Bool × α) × List α) + 1) ^ 1
    rw [pow_one]
    omega)
  have hin := ((PF.const (α := α × List α) false).pair PF.fst).pair PF.snd
  exact ((hin.comp hmain).comp PF.fst).of_eq (fun p => by
    obtain ⟨x, l⟩ := p
    show (List.foldl (fun s a => ((s.1 || decide (s.2 = a) : Bool), s.2))
      ((false, x)) l).1 = _
    rw [memFold_eq]
    simp)

/-- `RAM.polyFun_eqStep`. -/
def PF.eqStepB [DecidableEq α] {k d s e : ℕ}
    (heq : PF (fun q : α × α => decide (q.1 = q.2)) k d s e) :
    PFB (eqStep : (Bool × List α) × α → Bool × List α) := PFB.of <| by
  have hg := PF.const (α := Bool × α) ((false, ([] : List α)) : Bool × List α)
  have hbit := PF.ite ((PF.snd (α := α × List α) (β := Bool × α)).comp
      (PF.fst (α := Bool) (β := α)))
    ((((PF.snd (α := α × List α) (β := Bool × α)).comp PF.snd).pair
      ((PF.fst (α := α × List α) (β := Bool × α)).comp PF.fst)).comp heq)
    (PF.const (α := (α × List α) × (Bool × α)) false)
  have hh := (hbit.pair ((PF.fst (α := α × List α) (β := Bool × α)).comp PF.snd)).of_eq
    (g := fun q : (α × List α) × (Bool × α) =>
      (((q.2.1 && decide (q.2.2 = q.1.1) : Bool), q.1.2) : Bool × List α))
    (fun q => by cases h : q.2.1 <;> simp [h])
  have hin := ((PF.fst (α := Bool × List α) (β := α)).comp PF.snd).pair
    (((PF.fst (α := Bool × List α) (β := α)).comp PF.fst).pair PF.snd)
  exact (hin.comp (PF.listCases hg hh)).of_eq
    (g := (eqStep : (Bool × List α) × α → Bool × List α)) (fun s => by
      obtain ⟨⟨b, m⟩, a⟩ := s
      cases m <;> rfl)

/-- `RAM.polyFun_listEq`. -/
def PF.listEqB [DecidableEq α] {k d s e : ℕ}
    (heq : PF (fun q : α × α => decide (q.1 = q.2)) k d s e) :
    PFB (fun p : List α × List α => decide (p.1 = p.2)) := PFB.of <| by
  have hfold := PF.foldl (ka := 3) (da := 1) (PF.eqStepB heq).pf (fun x r j => by
    have := eqStep_size_bound x r j
    rw [pow_one]
    omega)
  have hin := ((PF.const (α := List α × List α) true).pair PF.snd).pair PF.fst
  have hand := (PF.ite (PF.fst (α := Bool) (β := List α))
    ((PF.snd (α := Bool) (β := List α)).comp pf_isEmpty)
    (PF.const (α := Bool × List α) false)).of_eq
      (g := fun z : Bool × List α => (z.1 && z.2.isEmpty : Bool))
      (fun z => by cases h : z.1 <;> simp [h])
  exact ((hin.comp hfold).comp hand).of_eq (fun p => by
    have h := eqStep_result p.1 p.2 true
    simpa using h)

/-- `RAM.polyFun_natListMem`. -/
theorem pf_natListMem : PF (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2)) 366 2 16 1 := by
  have h := (PF.listMemB pf_natEq).pf
  exact h

/-- `RAM.polyFun_listNatEq`. -/
theorem pf_listNatEq : PF (fun p : List ℕ × List ℕ => decide (p.1 = p.2)) 414 2 3 0 := by
  have h := (PF.listEqB pf_natEq).pf
  exact h

end Explicit
