import Workspace.Algo.AggNodeCompareReadOff

/-! # Looking up the computed comparison cosets

A lookup returns an option of a coset: the outer option records whether
the key is present, and the inner one records an empty isomorphism set.
Every key in the prescribed comparison phase is present.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem aggnPolyFun_boolEq : PolyFun (fun z : Bool × Bool => decide (z.1 = z.2)) :=
  (PolyFun.ite polyFun_fst polyFun_snd
    (PolyFun.ite polyFun_snd (polyFun_const false) (polyFun_const true))).of_eq
      (fun z => by rcases z with ⟨a, b⟩; cases a <;> cases b <;> rfl)

theorem aggnPolyFun_compareJobEq :
    PolyFun (fun z : AggnCompareJob × AggnCompareJob => decide (z.1 = z.2)) := by
  have hz : PolyFun (fun z : AggnCompareJob × AggnCompareJob => z) := polyFun_id
  have ha := pfst hz
  have hb := psnd hz
  have h1 := ((pfst ha).pair (pfst hb)).comp aggnPolyFun_boolEq
  have h2 := ((pfst (psnd ha)).pair (pfst (psnd hb))).comp polyFun_listNatEq
  have h3 := ((psnd (psnd ha)).pair (psnd (psnd hb))).comp polyFun_listNatEq
  exact (wftPolyFun_and h1 (wftPolyFun_and h2 h3)).of_eq (fun z => by
    rcases z with ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩
    by_cases h1 : a = d <;> by_cases h2 : b = e <;> by_cases h3 : c = f <;> simp [h1, h2, h3])

def aggnCompareLookup (z : RawAggCompareTable × AggnCompareJob) : Option RawCoset :=
  z.1.lookup z.2

theorem aggnPolyFun_compareLookup : PolyFun aggnCompareLookup :=
  polyFun_listLookup aggnPolyFun_compareJobEq

/-- A completed table always returns the recorded comparison at a prescribed key. -/
theorem aggnCompareLookup_spec {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} {tbl : RawAggCompareTable}
    (h : AggnCompareTableFor c ϕ tbl) {a : AggnCompareJob} (ha : a ∈ aggnCompareJobs c C) :
    ∃ q, aggnCompareLookup (tbl, a) = some q ∧ decCoset n q = aggnCompareValue ϕ a := by
  obtain ⟨q, hq, hdec⟩ := h.complete ha
  cases hl : aggnCompareLookup (tbl, a) with
  | none =>
    have he := List.lookup_eq_none_iff.mp hl (a, q) hq
    simp at he
  | some r =>
    obtain ⟨l₁, l₂, he, _⟩ := List.lookup_eq_some_iff.mp hl
    refine ⟨r, rfl, h.2 (a, r) ?_⟩
    dsimp only at he
    rw [he]
    exact List.mem_append_right _ List.mem_cons_self

/-- The lookup test for an empty comparison is exactly the mathematical one. -/
theorem aggnCompareLookup_empty_iff {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} {tbl : RawAggCompareTable}
    (h : AggnCompareTableFor c ϕ tbl) {a : AggnCompareJob} (ha : a ∈ aggnCompareJobs c C) :
    aggnCompareLookup (tbl, a) = some none ↔ aggnCompareValue ϕ a = ∅ := by
  obtain ⟨q, hq, hdec⟩ := aggnCompareLookup_spec h ha
  rw [hq, Option.some.injEq, ← hdec]
  exact (decCoset_eq_empty_iff n q).symm

end Algo
