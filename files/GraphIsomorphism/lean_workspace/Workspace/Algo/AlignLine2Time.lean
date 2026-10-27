/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§14.2, first sentence: Procedure Align, lines 1–2, run in polynomial time on the RAM.
-/
import Workspace.Algo.AlignG1
import Workspace.Algo.AlignJohnsonG1
import Workspace.Algo.AlignJohnsonLine2
import Workspace.Algo.TopLift
import Workspace.Machine.Bridge

/-!
# §14.2: Align, line 2, in polynomial time

> We are assuming that isomorphism of our canonical structures `X` is testable in polynomial
> time (which is certainly true for the types of structures considered), so Line 2 is
> executed in polynomial (in `m`) time.

and (§14.1)

> their `G^ϕ`-isomorphisms are easy to find (…trivial in linear time for colored
> equipartitions, and polynomial time for Johnson schemes.)

The routines are those the proof of `Algo.theorem_1_1_1` runs. This file only collects them
into one statement per structure type:

* line 1 and line 2 (i), `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))` or rejection:
  `Algo.alignColPartIso`, `Algo.alignJIso` (the flag says whether `G^ϕ` is `A(Γ)`);
* line 2 (ii), a lift `σ ∈ ϕ⁻¹(σ̄)`: `Algo.actPreimage`;
* line 2 (iv), `G₁ = ϕ⁻¹(Aut(X(x)))`: `Algo.alignG1`, `Algo.alignJG1`.

Each is `RAM.PolyTime`. The statements about what they compute are `Algo.alignColPartIso_some`,
`Algo.alignJIso_some`, `Algo.actPreimage_eq_some`, `Algo.decGroup_alignG1`,
`Algo.decGroup_alignJG1`; the part about line 1 and line 2 (i) is repeated here in terms of
`Iso_{G^ϕ}`.
-/

namespace Algo
open RAM Equiv

/-- The giant `G^ϕ ≤ S(Γ)` named by the flag of the routines: `A(Γ)` for `true`, `S(Γ)` for
`false`. -/
def alignGiant (m : ℕ) (g : Bool) : Set (Perm (Fin m)) :=
  if g then ((alternatingGroup (Fin m) : Subgroup (Perm (Fin m))) : Set (Perm (Fin m)))
  else Set.univ

/-- **§14.2, Align line 2 in polynomial time, colored partitions.** The routines of lines 1,
2 (i), 2 (ii) and 2 (iv) run in polynomial time, and the routine of lines 1–2 (i) returns
`σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`, or rejects exactly when that set is empty. -/
theorem align_line2_polyTime_colPart :
    PolyTime alignColPartIso ∧ PolyTime actPreimage ∧ PolyTime alignG1 ∧
      ∀ {m : ℕ} {P Q : RawColPart} (g : Bool), P.1.length = m → Q.1.length = m →
        (∀ s, alignColPartIso (g, (P, Q)) = some s →
          decPerm m s ∈ Babai.structIso (alignGiant m g) (decColStruct m P)
            (decColStruct m Q)) ∧
        (alignColPartIso (g, (P, Q)) = none →
          Babai.structIso (alignGiant m g) (decColStruct m P) (decColStruct m Q) = ∅) := by
  refine ⟨polyFun_alignColPartIso.polyTime, polyFun_actPreimage.polyTime,
    polyFun_alignG1.polyTime, fun g hP hQ => ⟨fun s hs => ?_, fun hs => ?_⟩⟩
  · obtain ⟨-, hiso, hsign⟩ := alignColPartIso_some hP hQ hs
    refine ⟨?_, (colPartIso_iff_smul _ _ _ _).1 hiso⟩
    cases g
    · exact Set.mem_univ _
    · exact (Equiv.Perm.mem_alternatingGroup).2 (hsign rfl)
  · cases g
    · exact alignColPartIso_none_structIso_univ hP hQ hs
    · exact alignColPartIso_none_structIso hP hQ hs

/-- **§14.2, Align line 2 in polynomial time, Johnson schemes.** The same four routines for a
Johnson scheme on `Γ`. -/
theorem align_line2_polyTime_johnson :
    PolyTime alignJIso ∧ PolyTime actPreimage ∧ PolyTime alignJG1 ∧
      ∀ {m : ℕ} {dom : List ℕ} {r r' : RawJohnson} (g : Bool), dom.length = m →
        RawJohnson.WF m (rawJDeg r) r.2.1 r → RawJohnson.WF m (rawJDeg r') r'.2.1 r' →
        (∀ s, alignJIso (g, (dom, (r, r'))) = some s →
          decPerm m s ∈ Babai.structIso (alignGiant m g) (decJohnson m r) (decJohnson m r')) ∧
        (alignJIso (g, (dom, (r, r'))) = none →
          Babai.structIso (alignGiant m g) (decJohnson m r) (decJohnson m r') = ∅) := by
  refine ⟨polyFun_alignJIso.polyTime, polyFun_actPreimage.polyTime,
    polyFun_alignJG1.polyTime, fun g hd h h' => ⟨fun s hs => ?_, fun hs => ?_⟩⟩
  · obtain ⟨-, hsmul, hsign⟩ := alignJIso_some hd h h' hs
    refine ⟨?_, hsmul⟩
    cases g
    · exact Set.mem_univ _
    · exact (Equiv.Perm.mem_alternatingGroup).2 (hsign rfl)
  · cases g
    · exact alignJIso_none_structIso_univ hd h h' hs
    · exact alignJIso_none_structIso hd h h' hs

end Algo

#print axioms Algo.align_line2_polyTime_colPart
#print axioms Algo.align_line2_polyTime_johnson
