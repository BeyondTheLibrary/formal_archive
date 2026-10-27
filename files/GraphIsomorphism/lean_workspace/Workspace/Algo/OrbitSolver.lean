/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§1.1, Corollary 1.1.3: the String Isomorphism routine of Theorem 1.1.1, called on raw
normalized instances.
-/
import Workspace.Algo.TopMasterClose
import Workspace.Algo.TopPrimitiveWindow
import Workspace.Machine.SIDecisionReduction

/-!
# The routine of Theorem 1.1.1 as a raw solver

Corollary 1.1.3 calls the String Isomorphism routine of Theorem 1.1.1 once per orbit, on the
instance restricted to that orbit. The restricted instance is a raw object; this file reads it
as a typed instance of `RAM.Targets.SIInput` and reads the typed answer back as a raw coset.

The routine is the one `Algo.siWorkspaceRoutine` provides: a program `P` with a
quasipolynomial time bound `T` and a polynomial size bound `S`, uniform in the domain size and
the alphabet. It solves a relation, not a function; since the program is deterministic, its
answer on each input is determined, and `Algo.normSolve` names it by choice.

## Main results

* `Algo.typedOfNorm`: a normalized raw instance on `m` points as a typed instance over the
  alphabet `Fin (2m)`, with the same encoding (`Algo.encode_typedOfNorm`);
* `Algo.normSolve`: the answer of the routine, as a raw coset;
* `Algo.normSolve_spec`: on every normalized instance, the routine runs to `normSolve` within
  `T` of the input size, the answer is a well-formed raw coset describing `Iso_G(x,y)`, and
  its size is at most `S` of the input size.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## Typed instances from normalized raw ones -/

/-- The letter at a position of a raw string with letters below `s`, as an element of
`Fin s`. -/
def strLetter {m s : ℕ} (l : RawStr) (hl : RawStr.WF m s l) (i : Fin m) : Fin s :=
  ⟨l.getD i 0, by
    have hi : (i : ℕ) < l.length := by rw [hl.1]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact hl.2 _ (List.getElem_mem hi)⟩

theorem encStr_strLetter {m s : ℕ} (l : RawStr) (hl : RawStr.WF m s l) :
    encStr (strLetter l hl) = l := by
  apply List.ext_getElem
  · simp [hl.1]
  · intro i h1 h2
    simp only [encStr, List.getElem_ofFn, strLetter]
    rw [List.getD_eq_getElem]

@[simp] theorem val_strLetter {m s : ℕ} (l : RawStr) (hl : RawStr.WF m s l) (i : Fin m) :
    (strLetter l hl i : ℕ) = decStrN m l i := rfl

/-- **A normalized raw instance as a typed instance** over the alphabet `Fin (2m)`. -/
noncomputable def typedOfNorm (m : ℕ) (r : RawSI) (h : NormSIWF m r) : SIInput m (2 * m) :=
  (r.1.map (decPerm m), strLetter r.2.1 h.2.2.1, strLetter r.2.2 h.2.2.2)

theorem rawOfSI_typedOfNorm (m : ℕ) (r : RawSI) (h : NormSIWF m r) :
    rawOfSI (typedOfNorm m r h) = r := by
  obtain ⟨g, x, y⟩ := r
  simp only [rawOfSI, typedOfNorm]
  rw [map_encPerm_decPerm h.1, encStr_strLetter, encStr_strLetter]

theorem encode_typedOfNorm (m : ℕ) (r : RawSI) (h : NormSIWF m r) :
    Enc.encode (typedOfNorm m r h) = Enc.encode r := by
  rw [encode_si_eq, rawOfSI_typedOfNorm]

/-- The isomorphisms of the typed instance are those of the decoded raw instance. -/
theorem isoSet_typedOfNorm (m : ℕ) (r : RawSI) (h : NormSIWF m r) :
    IsoSet (typedOfNorm m r h).1 (typedOfNorm m r h).2.1 (typedOfNorm m r h).2.2 =
      strIso (decGroup m r.1 : Set (Perm (Fin m))) (decStrN m r.2.1) (decStrN m r.2.2) := by
  rw [strIso_eq_sep]
  ext τ
  simp only [IsoSet, typedOfNorm, Set.mem_setOf_eq, Fin.ext_iff, val_strLetter]
  rfl

/-- **The typed answer read back.**  An admissible typed answer of Def. 11.1.2 describes, as a
raw coset, exactly the set `Iso_G(x,y)`. -/
theorem decCoset_rawAnswer {n s : ℕ} {a : SIInput n s}
    {b : Option (List (Perm (Fin n)) × Perm (Fin n))} (h : SIRel n s a b) :
    RawCoset.WF n (SIDecision.rawAnswer b) ∧
      decCoset n (SIDecision.rawAnswer b) = IsoSet a.1 a.2.1 a.2.2 := by
  obtain ⟨gens, x, y⟩ := a
  cases b with
  | none => exact ⟨trivial, h.symm⟩
  | some q =>
      obtain ⟨aut, σ⟩ := q
      obtain ⟨hσ, haut⟩ := h
      refine ⟨⟨fun g hg => ?_, wf_encPerm n σ⟩, ?_⟩
      · obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
        exact wf_encPerm n g'
      · change {τ | ∃ g ∈ decGroup n (aut.map (encPerm n)), τ = decPerm n (encPerm n σ) * g} = _
        rw [decGroup_map_encPerm, decPerm_encPerm]
        ext τ
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨g, hg, rfl⟩
          have hg' : g ∈ AutSet gens x := by rw [← haut]; exact hg
          exact ⟨(genGroup gens).mul_mem hσ.1 hg'.1,
            fun u => (hg'.2 u).trans (hσ.2 (g u))⟩
        · intro hτ
          refine ⟨σ⁻¹ * τ, ?_, by rw [mul_inv_cancel_left]⟩
          rw [← SetLike.mem_coe, haut]
          refine ⟨(genGroup gens).mul_mem ((genGroup gens).inv_mem hσ.1) hτ.1, fun u => ?_⟩
          rw [hτ.2 u, hσ.2 ((σ⁻¹ * τ) u)]
          simp [Perm.mul_apply]

/-! ## The routine as a raw solver -/

section Solver

variable {P : Program} {T S : ℕ → ℕ}

/-- The hypothesis that `P` is the routine of Theorem 1.1.1 in the workspace convention, with
time bound `T` and size bound `S`: the body of `RAM.SIWorkspaceRoutine`. -/
def IsSIRoutine (P : Program) (T S : ℕ → ℕ) : Prop :=
  ∀ n s : ℕ, CleanSolveAt 16 P
    (fun (a : SIInput n s) (b : Option (List (Perm (Fin n)) × Perm (Fin n))) =>
      SIRel n s a b ∧ Enc.size b ≤ S (Enc.size a)) T

open Classical in
/-- **The answer of the routine** on a raw instance, when the instance is normalized for the
length of its first string; `none` otherwise (no claim is made there). -/
noncomputable def normSolve (hP : IsSIRoutine P T S) (r : RawSI) : RawCoset :=
  if h : NormSIWF r.2.1.length r then
    SIDecision.rawAnswer (Classical.choose (hP r.2.1.length (2 * r.2.1.length)
      (typedOfNorm r.2.1.length r h)))
  else none

/-- **The specification of the raw solver.**  On a normalized instance on `m` points, the
routine halts cleanly holding `normSolve r` within `T` of the input size; the answer is a
well-formed raw coset describing `Iso_G(x,y)`, and its size is at most `S` of the input
size. -/
theorem normSolve_spec (hP : IsSIRoutine P T S) {m : ℕ} {r : RawSI} (h : NormSIWF m r) :
    RunsTo P (fun mem => mem = initMemAt 16 (Enc.encode r))
      (fun mem' => mem' = initMemAt 16 (Enc.encode (normSolve hP r))) (T (Enc.size r)) ∧
    RawCoset.WF m (normSolve hP r) ∧
    decCoset m (normSolve hP r) =
      strIso (decGroup m r.1 : Set (Perm (Fin m))) (decStrN m r.2.1) (decStrN m r.2.2) ∧
    Enc.size (normSolve hP r) ≤ S (Enc.size r) := by
  have hm : r.2.1.length = m := h.2.2.1.1
  subst hm
  set m := r.2.1.length with hmdef
  have hspec := Classical.choose_spec (hP m (2 * m) (typedOfNorm m r h))
  set b := Classical.choose (hP m (2 * m) (typedOfNorm m r h)) with hb
  have hsol : normSolve hP r = SIDecision.rawAnswer b := by
    rw [normSolve, dif_pos h]
  obtain ⟨⟨hrel, hsize⟩, hrun⟩ := hspec
  have henc := encode_typedOfNorm m r h
  have hsz : Enc.size (typedOfNorm m r h) = Enc.size r := size_eq_of_encode_eq henc
  have hbenc : Enc.encode (SIDecision.rawAnswer b) = Enc.encode b :=
    SIDecision.encode_rawAnswer b
  obtain ⟨hwf, hdec⟩ := decCoset_rawAnswer hrel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsol, hbenc, ← henc, ← hsz]
    exact hrun
  · rw [hsol]; exact hwf
  · rw [hsol, hdec, isoSet_typedOfNorm]
  · rw [hsol, size_eq_of_encode_eq hbenc, ← hsz]
    exact hsize

end Solver

end Algo
