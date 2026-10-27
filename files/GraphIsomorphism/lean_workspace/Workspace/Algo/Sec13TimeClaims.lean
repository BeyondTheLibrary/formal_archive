/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§13.1: the two polynomial-time claims of the section that are single routines on the RAM.
-/
import Workspace.Algo.LocalCertAff
import Workspace.Algo.LocalCertOut
import Workspace.Machine.Bridge

/-!
# §13.1: polynomial-time claims on the RAM

The proof of `Algo.theorem_1_1_1` runs these routines inside Procedure LocalCertificates.
This file states each paper claim once, as a RAM theorem.

* Notation 13.1.1: *"`G_A` can be computed in polynomial time as `G_A = ϕ⁻¹((G^ϕ)_A)`"*:
  `Algo.notation_13_1_1_polyTime`.
* Line 07 of Procedure LocalCertificates, the fullness test `H(W)^T ≥ A(T)` (Definition
  13.1.2), which is the check behind *"`K(T)` represents an easily (polynomial-time)
  verifiable proof of fullness of `T`"*: `Algo.fullnessTest_polyTime`.

The other running-time claims of §13 bound a whole procedure, for every `t`, and are stated
elsewhere as a call bound plus a RAM step bound for the rest: Thm. 13.1.3 in
`Algo.theorem_13_1_3_ram` (`Algo/LocalCertRAM.lean`), Prop. 13.1.11 in
`Algo.proposition_13_1_11_ram` (`Algo/LocalCertCompareRAM.lean`), and Thm. 13.2.1 in
`Algo.theorem_13_2_1_ram` (`Algo/Agg1321RAM.lean`; its two phases alone are
`Algo.theorem_13_2_1_phases_ram`, `Algo/AggregatePhasesRAM.lean`).
-/

namespace Algo
open RAM RAM.Targets Equiv

variable {n m : ℕ}

/-- **Notation 13.1.1, §13.1, the running time.** `G_A = ϕ⁻¹((G^ϕ)_A)` is computed in
polynomial time from generators of `G`, their images under the giant representation `ϕ`, and
the set `A`. -/
theorem notation_13_1_1_polyTime :
    PolyTime topStab ∧
      ∀ (p : RawAction × List ℕ) (ϕ : decGroup n p.1.1.2 →* Perm (Fin m)),
        RawAction.WF n m p.1 ϕ → Babai.IsGiantRep ϕ →
          decGroup n (topStab p) = Babai.bigGT ϕ (winSet m p.2) :=
  ⟨polyFun_topStab.polyTime, fun p ϕ hp hg => topStab_bigGT_of_wf p ϕ hp hg⟩

/-- **§13.1, line 07 (Definition 13.1.2), the running time.** Whether the group induced on the
test set, given by the images of generators, contains `A(T)` is decided in polynomial time. -/
theorem fullnessTest_polyTime :
    PolyTime rawIsFullT ∧
      ∀ {gens : List (Perm (Fin n))} {td : RawTAct}, RawGens.WF td.1.length td.2 →
        ∀ {ψ : genGroup gens →* Perm (Fin td.1.length)}, ImgsOf gens (lcImgs td) ψ →
          (rawIsFullT td = true ↔ alternatingGroup (Fin td.1.length) ≤ ψ.range) :=
  ⟨polyFun_rawIsFullT.polyTime, fun hwf _ hψ => rawIsFullT_eq_true_iff hwf hψ⟩

end Algo

#print axioms Algo.notation_13_1_1_polyTime
#print axioms Algo.fullnessTest_polyTime
