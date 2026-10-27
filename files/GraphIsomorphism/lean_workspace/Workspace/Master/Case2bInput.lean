/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 6a: a member of the case (2b) family as an admissible input of
Theorem 9.2.3.
-/
import Workspace.Master.Case2bDefect
import Workspace.Master.Line4cd

/-!
# A member of the case (2b) family as a point of `Babai.KAryInputs Γ 2 α`

`Babai.case2bFamily` is a set of pairs `(C ∖ S, R)`.  Theorem 9.2.3 takes a point of
`Babai.KAryInputs Γ 2 α`: a binary relational structure on a subset of `Γ` with at least
`4·2` vertices and relative symmetry defect above `1 − α`.  This file is the passage.

| piece | name |
|---|---|
| the relative symmetry defect of a member | `Babai.case2bDefect` |
| a member is admissible | `Babai.Case2bOk` |
| admissibility is invariant under a permutation of `Γ` | `Babai.case2bOk_move` |
| the member as a point, made total by a default | `Babai.case2bStr` |
| the point moves by `π` | `Babai.case2bStr_car`, `Babai.case2bStr_iso` |

The default is needed only because `Babai.exists_canonicalVersions_family_on` asks for a
total assignment of objects to members; it is never read at a member of the family.
-/

universe u v

namespace Babai

open MulAction Equiv

section Case2bInput

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- §13.2, case (2b): **the relative symmetry defect of the member `(C', R)`** — the defect
of the binary relational structure `Babai.binStruct`, read with the instances
`Babai.KAryInputs` reads it with. -/
noncomputable def case2bDefect (r : Set Γ × Set (Γ × Γ)) : ℚ :=
  @structDefect ↥r.1 _ _ (Fintype.ofFinite _) (Classical.decEq _) (binStruct r.1 r.2)

/-- §15, line 6a: **a member of the case (2b) family is an admissible input of
Theorem 9.2.3** at the threshold `α`: arity `2`, at least `4·2` vertices, relative symmetry
defect above `1 − α`. -/
def Case2bOk (α : ℝ) (r : Set Γ × Set (Γ × Γ)) : Prop :=
  2 ≤ 2 ∧ 4 * 2 ≤ r.1.ncard ∧ 1 - α < ((case2bDefect r : ℚ) : ℝ)

/-- The member as a point of `Babai.KAryInputs Γ 2 α`. -/
def case2bPt (α : ℝ) (r : Set Γ × Set (Γ × Γ)) (h : Case2bOk α r) :
    Pt (KAryInputs Γ 2 α) :=
  ⟨r.1, ⟨⟨binStruct r.1 r.2, binStruct_isKAry _ _⟩, h⟩⟩

@[simp] theorem case2bPt_car (α : ℝ) (r : Set Γ × Set (Γ × Γ)) (h : Case2bOk α r) :
    (case2bPt α r h).car = r.1 := rfl

/-! ### The defect is invariant under a permutation of `Γ` -/

/-- Moving the carrier and the relation by `π` does not change the relative symmetry
defect: `π` is an isomorphism of the two binary structures
(`Babai.binStruct_map`), and the defect is invariant under transport
(`Babai.RelStructure.structDefect_map_equiv`). -/
theorem case2bDefect_move (π : Equiv.Perm Γ) (r : Set Γ × Set (Γ × Γ)) :
    case2bDefect (moveCase2b π r) = case2bDefect r := by
  classical
  set s : Set Γ := r.1 with hs
  set R : Set (Γ × Γ) := r.2 with hR
  set e : ↥s ≃ ↥(π '' s) := Equiv.Set.image (π : Γ → Γ) s π.injective with he
  have heval : ∀ u : ↥s, ((e u : ↥(π '' s)) : Γ) = π (u : Γ) := fun _ => rfl
  have hmap : (binStruct s R).map (e : ↥s → ↥(π '' s))
      = binStruct (π '' s) ((Prod.map π π) '' R) := by
    refine binStruct_map e R ((Prod.map π π) '' R) fun u v => ?_
    rw [heval u, heval v]
    constructor
    · rintro ⟨p, hp, hpe⟩
      have h1 : π p.1 = π (u : Γ) := congrArg Prod.fst hpe
      have h2 : π p.2 = π (v : Γ) := congrArg Prod.snd hpe
      have : p = ((u : Γ), (v : Γ)) :=
        Prod.ext (π.injective h1) (π.injective h2)
      rwa [this] at hp
    · intro hmem
      exact ⟨((u : Γ), (v : Γ)), hmem, rfl⟩
  show @structDefect ↥(π '' s) _ _ (Fintype.ofFinite _) (Classical.decEq _)
      (binStruct (π '' s) ((Prod.map π π) '' R))
    = @structDefect ↥s _ _ (Fintype.ofFinite _) (Classical.decEq _) (binStruct s R)
  rw [← hmap]
  exact @RelStructure.structDefect_map_equiv ↥s ↥(π '' s) (Fintype.ofFinite _)
    (Classical.decEq _) (Fintype.ofFinite _) (Classical.decEq _) (binStruct s R) e

/-- Admissibility is invariant under a permutation of `Γ`. -/
theorem case2bOk_move (α : ℝ) (π : Equiv.Perm Γ) (r : Set Γ × Set (Γ × Γ)) :
    Case2bOk α (moveCase2b π r) ↔ Case2bOk α r := by
  have hcard : (moveCase2b π r).1.ncard = r.1.ncard := by
    show (π '' r.1).ncard = r.1.ncard
    exact Set.ncard_image_of_injective _ π.injective
  rw [Case2bOk, Case2bOk, hcard, case2bDefect_move]

/-! ### The assignment of objects to members -/

open scoped Classical in
/-- §15, line 6a: **the object of `Babai.KAryInputs Γ 2 α` a member of the family carries**,
made total by a default object that is never read at a member. -/
noncomputable def case2bStr (α : ℝ) (X₀ : Pt (KAryInputs Γ 2 α))
    (r : Set Γ × Set (Γ × Γ)) : Pt (KAryInputs Γ 2 α) :=
  if h : Case2bOk α r then case2bPt α r h else X₀

theorem case2bStr_of (α : ℝ) (X₀ : Pt (KAryInputs Γ 2 α)) {r : Set Γ × Set (Γ × Γ)}
    (h : Case2bOk α r) : case2bStr α X₀ r = case2bPt α r h := by
  classical
  rw [case2bStr, dif_pos h]

/-- The underlying set of the object moves by `π`. -/
theorem case2bStr_car (α : ℝ) (X₀ : Pt (KAryInputs Γ 2 α)) (π : Equiv.Perm Γ)
    {r : Set Γ × Set (Γ × Γ)} (h : Case2bOk α r) :
    (case2bStr α X₀ (moveCase2b π r)).car = π '' (case2bStr α X₀ r).car := by
  rw [case2bStr_of α X₀ h, case2bStr_of α X₀ ((case2bOk_move α π r).2 h)]
  rfl

/-- Replacing the two endpoints by equal objects does not change the statement that `π` is
a morphism between them. -/
theorem isoP_permHom_congr {C : Cat.{0, 0} Γ} {π : Equiv.Perm Γ} {A A' B B' : Pt C}
    (hA : A = A') (hB : B = B') (h : B.car = π '' A.car) (h' : B'.car = π '' A'.car)
    (hyp : permHom π A' B' h' ∈ C.IsoP A' B') : permHom π A B h ∈ C.IsoP A B := by
  subst hA
  subst hB
  exact hyp

/-- `π` is an isomorphism of the object of `r` with the object of `r` moved by `π`. -/
theorem case2bPt_iso (α : ℝ) (π : Equiv.Perm Γ) {r : Set Γ × Set (Γ × Γ)}
    (h : Case2bOk α r) (h' : Case2bOk α (moveCase2b π r))
    (hc : (case2bPt α (moveCase2b π r) h').car = π '' (case2bPt α r h).car) :
    permHom π (case2bPt α r h) (case2bPt α (moveCase2b π r) h') hc ∈
      (KAryInputs Γ 2 α).IsoP (case2bPt α r h) (case2bPt α (moveCase2b π r) h') := by
  show (binStruct r.1 r.2).map
      ((permHom π (case2bPt α r h) (case2bPt α (moveCase2b π r) h') hc :
        ↥r.1 ≃ ↥(π '' r.1)) : ↥r.1 → ↥(π '' r.1))
    = binStruct (π '' r.1) ((Prod.map π π) '' r.2)
  refine binStruct_map _ r.2 ((Prod.map π π) '' r.2) fun u v => ?_
  show (π ((u : Γ)), π ((v : Γ))) ∈ (Prod.map π π) '' r.2 ↔ ((u : Γ), (v : Γ)) ∈ r.2
  constructor
  · rintro ⟨p, hp, hpe⟩
    have h1 : π p.1 = π ((u : Γ)) := congrArg Prod.fst hpe
    have h2 : π p.2 = π ((v : Γ)) := congrArg Prod.snd hpe
    have hpq : p = (((u : Γ)), ((v : Γ))) := Prod.ext (π.injective h1) (π.injective h2)
    rwa [hpq] at hp
  · intro hmem
    exact ⟨(((u : Γ)), ((v : Γ))), hmem, rfl⟩

/-- `π` is an isomorphism of the object of `r` with the object of `r` moved by `π`, for the
total assignment `Babai.case2bStr`. -/
theorem case2bStr_iso (α : ℝ) (X₀ : Pt (KAryInputs Γ 2 α)) (π : Equiv.Perm Γ)
    {r : Set Γ × Set (Γ × Γ)} (h : Case2bOk α r) :
    permHom π (case2bStr α X₀ r) (case2bStr α X₀ (moveCase2b π r))
      (case2bStr_car α X₀ π h) ∈
      (KAryInputs Γ 2 α).IsoP (case2bStr α X₀ r) (case2bStr α X₀ (moveCase2b π r)) := by
  have h' : Case2bOk α (moveCase2b π r) := (case2bOk_move α π r).2 h
  refine isoP_permHom_congr (case2bStr_of α X₀ h) (case2bStr_of α X₀ h') _ ?_
    (case2bPt_iso α π h h' ?_)
  · rfl
  · rfl

end Case2bInput

end Babai
