/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Cited algorithmic result of Section 11.2 (the structure of a Cameron group), on the RAM.
-/
import Workspace.Algo.Cameron

/-!
# Cited algorithmic result, Section 11.2: the structure of a Cameron group [BaLS]

This file contains **one** axiom.  It is the sentence that closes the proof of
Theorem 11.2.1 (version 2.5, p. 82, lines 5027–5029):

> This completes the proof of the mathematical part of Theorem 11.2.1.  The algorithmic
> part is well known: Cameron groups can be recognized and their structure mapped out in
> polynomial time (and even in NC [BaLS]).

[BaLS] is L. Babai, E. M. Luks, Á. Seress, *Permutation groups in NC*, Proc. 19th ACM STOC,
1987, pp. 409–420.  The paper gives no algorithm and no sharper statement; Sec. 2.2.3, the
toolkit of cited group algorithms, is marked "TO BE WRITTEN".  It is an axiom by a decision
of the user; see `CITED.md` (entry C16) and the entry on Cameron groups in the corrected paper.

It is the only axiom of this project about running time (Proposition 10.5.4 was one until
it was proved, `Workspace/Algo/StdBlocksProved.lean`).  It is stated against the machine
model (`Workspace/Machine/`) and the raw encodings (`Workspace/Algo/`).

## How the statement is read

* *"Cameron groups"*.  The input is a group `G ≤ S_n` given by a list of generators, with
  the domain witness `dom` of length `n`, as for every routine of `Workspace/Algo/`.  The
  axiom speaks only about inputs for which `G` **is** a Cameron group
  (`Babai.IsCameronGroup`, Def. 11.2.2), with any parameters.  It carries no other
  hypothesis: no bound on `n`, no primitivity, no bound on the order.
* *"their structure mapped out"*.  The structure of Def. 11.2.2 is the triple `s`, `t`, `k`
  and the identification of the domain with `(Fin k choose t)^s` through which
  `(A_k^{(t)})^s ≤ G ≤ S_k^{(t)} ≀ S_s`.  The routine returns exactly this, as a table with
  one row per point (`Algo.RawCameron`, decoded by `Algo.decCameron`).  The output is
  required to be a Cameron structure of `G`: the numeric clauses of Def. 11.2.2 are part of
  `Algo.RawCameron.WF`, the socle clause holds for the returned `k`, and the two containments
  hold through the returned bijection.  The socle factors are **not** returned as data.
* *"recognized"*.  The paper uses the routine only at step 6 of Procedure Reduce-to-Johnson,
  where Theorem 11.2.3 has already shown that the group is a Cameron group.  So the axiom
  says **nothing** about the output on a group that is not a Cameron group.  This half of
  the cited sentence is left out because it is not needed; leaving it out makes the axiom
  weaker.
* *"in polynomial time"*.  `RAM.PolyFun`, the class of every proved routine of
  `Workspace/Algo/`.  The axiom
  asserts only that such a routine **exists**; it names no routine and fixes no running
  time.  The NC claim is not used.

A function with this output exists by Def. 11.2.2 alone
(`Algo.cameronStructureSpec_exists`, `Workspace/Algo/CameronAxiom.lean`; its proof uses
only Lean's three axioms).  So the only content of the axiom is the running time.
-/

namespace Babai

open RAM

/-- §11.2, the algorithmic part of Theorem 11.2.1, cited from [BaLS].

Quoted from the paper (version 2.5, lines 5027–5029):

> The algorithmic part is well known: Cameron groups can be recognized and their structure
> mapped out in polynomial time (and even in NC [BaLS]).

There is a polynomial-time routine that takes generators of `G ≤ S_n`.  Whenever `G` is a
Cameron group, it returns parameters `s`, `t`, `k` and a bijection of the domain with
`(Fin k choose t)^s` such that `G` is a Cameron group with these parameters through this
bijection (Def. 11.2.2).  The module docstring says how each phrase of the paper is read. -/
axiom cameronStructure_polyTime :
    ∃ cameron : Algo.RawGens × List ℕ → Option Algo.RawCameron, PolyFun cameron ∧
      ∀ (n : ℕ) (gs : Algo.RawGens) (dom : List ℕ), dom.length = n → Algo.RawGens.WF n gs →
        (∃ s t k : ℕ, IsCameronGroup (Algo.decGroup n gs) s t k) →
        ∃ (c : Algo.RawCameron) (h : c.WF n), cameron (gs, dom) = some c ∧
          (∃ R : Fin c.s → Subgroup (Algo.decGroup n gs),
            IsSocleFactorization (Algo.decGroup n gs) R c.k) ∧
          basePower (JohnsonA c.k c.t) c.s ≤
            (Algo.decGroup n gs).map
              (Equiv.permCongrHom (Algo.decCameron c h)).toMonoidHom ∧
          (Algo.decGroup n gs).map
              (Equiv.permCongrHom (Algo.decCameron c h)).toMonoidHom ≤
            wreathProduct (JohnsonS c.k c.t) c.s

end Babai
