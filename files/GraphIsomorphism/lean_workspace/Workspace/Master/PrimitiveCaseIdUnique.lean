import Workspace.Master.Hypergraph

/-! # The labelling of the primitive case is unique

Sec. 15, line 4: in the primitive case the window is the set of standard blocks, and the
label of a point `u` is its own set `T(u)` (Theorem 10.5.1 (c) and (e)). So the labelling
`Ω → Γ^{(t)}` is a function of the giant representation `ϕ` alone. The Master round picks a
`Babai.PrimitiveCaseId` by choice. This file shows that there is nothing to pick: any two
are equal. A machine that computes the labelling from `T(u)` therefore works with the same
labelling as `Babai.primitiveCaseId`.
-/

namespace Babai

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ} {t : ℕ}

omit [Fintype Ω] [DecidableEq Ω] in
/-- Two labellings of the primitive case agree: both send `u` to `T(u)`, by the field
`label_eq`. -/
theorem PrimitiveCaseId.label_unique (a b : PrimitiveCaseId ϕ t) : a.label = b.label := by
  ext u : 1
  apply Subtype.ext
  apply Finset.coe_injective
  rw [a.label_eq u, b.label_eq u]

/-- Sec. 15, line 4: **the identification of the primitive case is unique.** The labelling
is determined by `label_eq`, and the other fields are propositions. -/
instance PrimitiveCaseId.instSubsingleton : Subsingleton (PrimitiveCaseId ϕ t) :=
  ⟨fun a b => by
    have h := PrimitiveCaseId.label_unique a b
    cases a
    cases b
    cases h
    rfl⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- A labelling that sends every point to its set `T(u)` is the labelling of any
identification of the primitive case. This is the form a machine uses: it computes `T(u)`
and needs to know that the Master round reads the window through the same labelling. -/
theorem PrimitiveCaseId.label_apply_eq (a : PrimitiveCaseId ϕ t) (u : Ω) (s : binom Γ t)
    (hs : ((s : Finset Γ) : Set Γ) = TpointOf ϕ u) : a.label u = s := by
  apply Subtype.ext
  apply Finset.coe_injective
  rw [a.label_eq u, hs]

end Babai
