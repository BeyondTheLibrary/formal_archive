import Workspace.Algo.SplitBipPointColors

/-! The dictionary records a vertex as its set of original point names.
This is the interface needed to restore colors of singleton vertices,
including singleton blocks that lie outside the current first part. -/
namespace Algo
open Babai RAM

structure SbipVertexDictionary {α : Type*} (V : Set (Set α)) (point : α → ℕ)
    (d : List (List ℕ)) (e : ↥V ≃ Fin d.length) : Prop where
  row_nodup : ∀ A, (d[(e A).val]).Nodup
  row_mem : ∀ A a, a ∈ d[(e A).val] ↔ ∃ x ∈ A.val, point x = a

section
variable {α : Type*} {V : Set (Set α)} {point : α → ℕ}
    {d : List (List ℕ)} {e : ↥V ≃ Fin d.length}
    (h : SbipVertexDictionary V point d e) (hinj : Function.Injective point)
include h hinj

theorem sbipVertexDictionary_singleton (A : ↥V) (x : α) :
    d[(e A).val] = [point x] ↔ A.val = {x} := by
  constructor
  · intro hr
    ext y
    constructor
    · intro hy
      have hm := (h.row_mem A (point y)).2 ⟨y,hy,rfl⟩
      rw [hr,List.mem_singleton] at hm
      exact hinj hm
    · intro hy
      obtain ⟨z,hz,hzx⟩ := (h.row_mem A (point x)).1
        (hr ▸ List.mem_singleton_self (point x))
      have hz' := hinj hzx
      simpa only [Set.mem_singleton_iff] using (hy ▸ hz' ▸ hz)
  · intro hA
    have hm (a : ℕ) : a ∈ d[(e A).val] ↔ a = point x := by
      rw [h.row_mem,hA]
      simp [eq_comm]
    have hx := (hm (point x)).2 rfl
    by_contra he
    rcases ((h.row_nodup A).ne_singleton_iff (point x)).1 he with hn | ⟨a,ha,han⟩
    · simpa [hn] using hx
    · exact han ((hm a).1 ha)

theorem sbipVertexDictionary_singleton_mem (x : α) : [point x] ∈ d ↔ {x} ∈ V := by
  constructor
  · intro hm
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hm
    let A := e.symm ⟨i,hi⟩
    have hr : d[(e A).val] = [point x] := by simpa [A] using he
    exact (sbipVertexDictionary_singleton h hinj A x).1 hr ▸ A.property
  · intro hx
    have hr := (sbipVertexDictionary_singleton h hinj ⟨{x},hx⟩ x).2 rfl
    exact hr ▸ List.getElem_mem (e ⟨{x},hx⟩).isLt

theorem sbipVertexDictionary_point (x : α) (hx : {x} ∈ V) :
    sbipDictPoint (d,e ⟨{x},hx⟩) = point x := by
  apply sbipDictPoint_singleton
  rw [sbipDictGet_get]
  exact (sbipVertexDictionary_singleton h hinj ⟨{x},hx⟩ x).2 rfl

open scoped Classical in
theorem sbipVertexDictionary_color (lab : RawLab) (pad : ℕ) (x : α) :
    sbipSingletonColor (((d,lab),pad),point x) =
      if hx : {x} ∈ V then labAt lab (e ⟨{x},hx⟩) else pad := by
  by_cases hx : {x} ∈ V
  · rw [dif_pos hx]
    apply sbipSingletonColor_hit d lab pad (point x) (e ⟨{x},hx⟩)
      ((sbipVertexDictionary_singleton h hinj ⟨{x},hx⟩ x).2 rfl)
    intro j hj
    have hA : e.symm j = ⟨{x},hx⟩ := Subtype.ext
      ((sbipVertexDictionary_singleton h hinj (e.symm j) x).1 (by simpa using hj))
    have he : j = e ⟨{x},hx⟩ := by simpa using congrArg e hA
    rw [he]
  · rw [dif_neg hx]
    apply sbipSingletonColor_miss
    exact fun hh => hx ((sbipVertexDictionary_singleton_mem h hinj x).1 hh)

end
end Algo
