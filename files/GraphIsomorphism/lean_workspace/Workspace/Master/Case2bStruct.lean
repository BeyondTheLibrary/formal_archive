/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2, case (2b): a constituent of the orbital configuration read as a binary
relational structure on a subset of `Γ`.
-/
import Workspace.Master.Case2bFamily
import Workspace.Master.FamilyVersions

/-!
# A digraph on a subset of `Γ` as a binary relational structure

Line 6 of Sec. 15 speaks of a *"canonically embedded `k`-ary relational structure on `Γ`
with relative symmetry defect `≥ 1/2`"*, and case (2b) of Theorem 13.2.1 produces a
**digraph** — one off-diagonal constituent `X_i` of an orbital configuration on
`C' = C ∖ S`.  The two are the same thing at `k = 2`, and this file says so:

| piece | name |
|---|---|
| a set of pairs read as a binary relational structure on a subset | `Babai.binStruct` |
| the same read as a digraph | `Babai.binDigraph` |
| transport along a bijection of the carriers | `Babai.binStruct_map` |
| the two automorphism groups are the same | `Babai.aut_binStruct` |
| hence the same symmetry defect | `Babai.structDefect_binStruct` |

`Babai.binStruct` keeps the automorphism group, so the symmetry defect of the digraph — the
`≥ 1/2` of Cor. 2.4.12 — *is* the relative symmetry defect Theorem 9.2.3 asks of its input.
-/

universe u v

namespace Babai

open Equiv

section BinStruct

variable {Γ : Type*}

/-- §13.2, case (2b): **a set of pairs of `Γ` read as a binary relational structure on a
subset `s ⊆ Γ`** — one relation, of arity `2`, holding the pairs of points of `s` that the
set contains. -/
def binStruct (s : Set Γ) (R : Set (Γ × Γ)) : RelStructure ↥s where
  numRel := 1
  arity := fun _ => 2
  rel := fun _ => {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R}

/-- The same data read as a digraph on `↥s`. -/
def binDigraph (s : Set Γ) (R : Set (Γ × Γ)) : Digraph ↥s :=
  ⟨{p : ↥s × ↥s | ((p.1 : Γ), (p.2 : Γ)) ∈ R}⟩

theorem binStruct_isKAry (s : Set Γ) (R : Set (Γ × Γ)) : (binStruct s R).IsKAry 2 :=
  fun _ => rfl

@[simp] theorem binStruct_numRel (s : Set Γ) (R : Set (Γ × Γ)) :
    (binStruct s R).numRel = 1 := rfl

/-- **The transport of `Babai.binStruct` along a bijection of the carriers.**  If the
bijection `e : ↥s ≃ ↥t` matches the pairs of `R` inside `s` with the pairs of `R'` inside
`t`, then it is an isomorphism of the two binary structures. -/
theorem binStruct_map {s t : Set Γ} (e : ↥s ≃ ↥t) (R R' : Set (Γ × Γ))
    (h : ∀ u v : ↥s, (((e u : ↥t) : Γ), ((e v : ↥t) : Γ)) ∈ R' ↔ ((u : Γ), (v : Γ)) ∈ R) :
    (binStruct s R).map (e : ↥s → ↥t) = binStruct t R' := by
  have hrel : mapRel (e : ↥s → ↥t)
        {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R}
      = {w : Fin 2 → ↥t | (((w 0 : ↥t) : Γ), ((w 1 : ↥t) : Γ)) ∈ R'} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h (v 0) (v 1)).2 hv
    · intro hw
      refine ⟨fun i => e.symm (w i), ?_, ?_⟩
      · have := (h (e.symm (w 0)) (e.symm (w 1))).1
        simp only [Equiv.apply_symm_apply] at this
        exact this hw
      · funext i
        show e (e.symm (w i)) = w i
        rw [Equiv.apply_symm_apply]
  show RelStructure.mk 1 (fun _ => 2)
      (fun _ => mapRel (e : ↥s → ↥t)
        {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R})
    = RelStructure.mk 1 (fun _ => 2)
      (fun _ => {w : Fin 2 → ↥t | (((w 0 : ↥t) : Γ), ((w 1 : ↥t) : Γ)) ∈ R'})
  simp only [RelStructure.mk.injEq, heq_eq_eq, true_and]
  funext i
  exact hrel

/-- The converse of `Babai.binStruct_map` at `t = s`: an isomorphism of the binary
structure with itself matches the pairs of `R` the way the digraph asks. -/
theorem binStruct_map_self {s : Set Γ} (e : ↥s ≃ ↥s) (R : Set (Γ × Γ))
    (h : (binStruct s R).map (e : ↥s → ↥s) = binStruct s R) (u v : ↥s) :
    (((e u : ↥s) : Γ), ((e v : ↥s) : Γ)) ∈ R ↔ ((u : Γ), (v : Γ)) ∈ R := by
  have hrel : mapRel (e : ↥s → ↥s)
        {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R}
      = {w : Fin 2 → ↥s | (((w 0 : ↥s) : Γ), ((w 1 : ↥s) : Γ)) ∈ R} := by
    have h' : RelStructure.mk 1 (fun _ : Fin 1 => 2)
        (fun _ => mapRel (e : ↥s → ↥s)
          {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R})
      = RelStructure.mk 1 (fun _ : Fin 1 => 2)
        (fun _ => {w : Fin 2 → ↥s | (((w 0 : ↥s) : Γ), ((w 1 : ↥s) : Γ)) ∈ R}) := h
    simp only [RelStructure.mk.injEq, heq_eq_eq, true_and] at h'
    exact congrFun h' 0
  constructor
  · intro hmem
    have hw : (fun i : Fin 2 => if i = 0 then e u else e v)
        ∈ {w : Fin 2 → ↥s | (((w 0 : ↥s) : Γ), ((w 1 : ↥s) : Γ)) ∈ R} := by
      simpa using hmem
    rw [← hrel] at hw
    obtain ⟨v₀, hv₀, hev⟩ := hw
    have h0 : e (v₀ 0) = e u := by
      have := congrFun hev 0
      simpa using this
    have h1 : e (v₀ 1) = e v := by
      have := congrFun hev 1
      simpa using this
    have e0 : v₀ 0 = u := e.injective h0
    have e1 : v₀ 1 = v := e.injective h1
    rw [← e0, ← e1]
    exact hv₀
  · intro hmem
    have hv : (fun i : Fin 2 => if i = 0 then u else v)
        ∈ {w : Fin 2 → ↥s | (((w 0 : ↥s) : Γ), ((w 1 : ↥s) : Γ)) ∈ R} := by
      simpa using hmem
    have hmapped : mapRel (e : ↥s → ↥s)
        {v : Fin 2 → ↥s | (((v 0 : ↥s) : Γ), ((v 1 : ↥s) : Γ)) ∈ R}
        (fun i : Fin 2 => e (if i = 0 then u else v)) :=
      ⟨_, hv, rfl⟩
    rw [hrel] at hmapped
    simpa using hmapped

/-- **The automorphism group of `Babai.binStruct` is the automorphism group of the
digraph.**  This is what makes *"relative symmetry defect `≥ 1/2`"* of Cor. 2.4.12 the same
number as the relative symmetry defect Theorem 9.2.3 asks of a binary input. -/
theorem aut_binStruct (s : Set Γ) (R : Set (Γ × Γ)) :
    (binStruct s R).Aut = Digraph.Aut (binDigraph s R) := by
  ext τ
  constructor
  · intro hτ u v
    exact binStruct_map_self τ R hτ u v
  · intro hτ
    show (binStruct s R).map ((τ : Equiv.Perm ↥s) : ↥s → ↥s) = binStruct s R
    exact binStruct_map (τ : Equiv.Perm ↥s) R R fun u v => hτ u v

/-- The relative symmetry defect of `Babai.binStruct` is that of the digraph. -/
theorem structDefect_binStruct [Fintype Γ] [DecidableEq Γ] (s : Set Γ) [Fintype ↥s]
    [DecidableEq ↥s] (R : Set (Γ × Γ)) :
    structDefect (binStruct s R) = defect (Digraph.Aut (binDigraph s R)) := by
  show defect (binStruct s R).Aut = _
  rw [aut_binStruct]

end BinStruct

end Babai
