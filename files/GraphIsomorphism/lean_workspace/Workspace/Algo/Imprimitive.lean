/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 11.1.9 (Imprimitive Luks reduction) as one computable round.
-/
import Workspace.Algo.Blocks
import Workspace.Algo.Descent

/-!
# The Imprimitive Luks reduction (§11.1, Theorem 11.1.9) as one round

> Let `G ≤ S(Ω)` and let `Δ ⊆ Ω` be a `G`-invariant subset.  Let `{B₁,…,B_m}` be a
> `G`-invariant partition of `Δ`.  Let `ψ : G → Ḡ ≤ S_m` be the induced action of `G` on the
> set of blocks and let `N = ker(ψ)`.  Then finding `Iso^Δ_G(x,y)` reduces to `m|Ḡ|` instances
> of finding `Iso^{B_i}_{M_i}(x, y^{σ_i})`.
>
> *Proof.*  First descend to `N = ker ψ`.  Then consider each `B_i` to be the window in
> succession, reducing the group at each round, following the Chain Rule.  In the end, combine
> all the results into a single coset.

This file writes the two steps of that proof as **one** `Algo.Round`, on a phase-marked
instance

```
Algo.RawImpSI := RawWinSI × Option (RawBlocks × ℕ)
```

whose option is the block system together with `|G : N| = |Ḡ|`.  In the phase `some (ℬ, |Ḡ|)`
the round descends (Prop. 11.1.6 with `H = N`); its children carry the marker `none`, and in
the phase `none` the round is Luks's Chain Rule of `Workspace/Algo/Luks.lean`.  The measure
`2·|Δ| + (1 in the descend phase)` drops in both: a descent child keeps the window and loses
the marker, a chain child loses at least one point of the window.

## Two decisions, both recorded in `Workspace/Algo/DESIGN.md`

**The windows of the second phase are the orbits of `N`, not the blocks.**  The blocks are
`N`-invariant (`Babai.isInvariant_blockKernel`), so each of them is a union of orbits of `N`
and the Chain Rule over the orbits (Eq. (64)) refines the Chain Rule over the blocks.  This is
what `Algo.chainRound` already does, it is the recursion the paper analyses right after
Fact 11.1.8, and it is the finer of the two: processing a proper part of a block first only
makes the group smaller at the next window.  The identity the round computes is
`Babai.Theorem_11_1_9` with `Babai.wIso_window_sUnion` applied to the orbits instead of the
blocks; the descent half — the factor `|Ḡ|` and the subgroup `N` — is unchanged.

**One round rather than a `Round.seq` combinator.**  `Algo.LoopMatch` is tied to a particular
`Algo.Round`, so neither `Algo.loopMatch_chainRound` nor `Algo.loopMatch_descentRound`
transfers, and a sequencing combinator on `ι₁ ⊕ ι₂` would need a transfer lemma of the same
length as the two inductions redone here — plus a translation of the instance type, since the
two phases here share one instance and one decoding.  The two inductions are therefore redone
(`Algo.loopMatch_impDesc`, `Algo.loopMatch_impChain`); if a third composition of this shape
appears, the combinator becomes the better investment.

## Main definitions

* `Algo.RawImpSI`, `Algo.ImpWF` — the phase-marked instances and their well-formedness;
* `Algo.impKer`, `Algo.impRep` — `N` and the coset representatives (Prop. 2.2.6 (a) for the
  block action, `Workspace/Algo/Blocks.lean`);
* `Algo.impChild`, `Algo.impRound` — the round;
* `Algo.impRoundReduction` — the mathematical round it implements;
* `Algo.impCost` — its cost data.

## Main results

* `Algo.cover_impPerms` — the candidate set is the union of the `|Ḡ|` left cosets of `N`;
* `Algo.implements_impRound` — **the link**: the raw round walks that tree;
* `Algo.run_impRoundReduction` — the tree computes the answer of the instance, so
  `Algo.roundValue_eq` applies;
* `Algo.impCost` — every routine is a `RAM.PolyFun` and instances stay polynomially small.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The phase-marked instances -/

/-- A raw instance of the imprimitive round: an instance with a window (`Algo.RawWinSI`)
together with, in the descend phase, the block system `ℬ` and the index `|G : N| = |Ḡ|` as a
machine natural.  `none` marks the Chain Rule phase. -/
abbrev RawImpSI := RawWinSI × Option (RawBlocks × ℕ)

/-- The instance a raw instance describes.  Paper: Definition 11.1.2. -/
noncomputable def decImpSI (n : ℕ) (I : RawImpSI) : Babai.SIInstance (Fin n) ℕ :=
  decWinSI n I.1

/-- **Generators of `N = ker ψ`** (Theorem 11.1.9, through Prop. 2.2.6 (a)), shortened to at
most `n²` of them so that a child is a well-formed instance. -/
def impKer (W : RawWinSI) (bl : RawBlocks) : RawGens :=
  tidyGens (W.2.2.2.1, blockKerGens ((W.2.2.2.1, W.2.1), bl))

/-- The `j`-th representative of a child: the parent's representative times the `j`-th coset
representative of `N` in `G`, read off the stabilizer chain of the extended group, with the
index `j` in binary. -/
def impRep (W : RawWinSI) (bl : RawBlocks) (j : ℕ) : RawPerm :=
  rawMul (W.2.2.1, normPerm (W.2.2.2.1, blockCosetRep (((W.2.2.2.1, W.2.1), bl), j)))

/-- The representatives of the children, decoded: the `σ_j` of Eq. (62) for `H = N`. -/
noncomputable def impPerms (n : ℕ) (W : RawWinSI) (q : RawBlocks × ℕ) : List (Perm (Fin n)) :=
  (List.range q.2).map (fun j => decPerm n (impRep W q.1 j))

@[simp] theorem length_impPerms (n : ℕ) (W : RawWinSI) (q : RawBlocks × ℕ) :
    (impPerms n W q).length = q.2 := by simp [impPerms]

theorem getElem_impPerms (n : ℕ) (W : RawWinSI) (q : RawBlocks × ℕ) {j : ℕ}
    (hj : j < (impPerms n W q).length) :
    (impPerms n W q)[j] = decPerm n (impRep W q.1 j) := by
  simp only [impPerms, List.getElem_map, List.getElem_range]

/-- **Well-formed raw instances.**  Besides `Algo.WinWF`, the block system is a `G`-invariant
partition on raw data whose block action is a homomorphism (`Algo.BlockData`), and the stored
index is the number `|G : N|` of cosets the transversal produces. -/
def ImpWF (n : ℕ) (I : RawImpSI) : Prop :=
  WinWF n I.1 ∧
    ∀ bl idx, I.2 = some (bl, idx) →
      BlocksWF n bl ∧ BlockData n bl (descGens n I.1) ∧
        idx = blockCosetIndex n I.1.2.2.2.1 bl (descGens n I.1)

section Data

variable {I : RawImpSI} {bl : RawBlocks} {idx : ℕ}

/-- The generator list of the instance is the encoding of its decoding. -/
theorem imp_gens_eq (hI : ImpWF n I) : I.1.2.1 = (descGens n I.1).map (encPerm n) :=
  (map_encPerm_decPerm hI.1.2.2.2.2.1).symm

/-- **The subgroup descended to is `N = ker ψ`** (Theorem 11.1.9). -/
theorem decGroup_impKer (hI : ImpWF n I) (hs : I.2 = some (bl, idx))
    {ϕ : genGroup (descGens n I.1) →* Perm (Fin bl.length)}
    (hϕ : ImgsOf (descGens n I.1) (blockImgsOf n bl (descGens n I.1)) ϕ) :
    decGroup n (impKer I.1 bl) = actKer (descGens n I.1) ϕ := by
  obtain ⟨-, ⟨hwf, -⟩, -⟩ := hI.2 bl idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  rw [impKer, decGroup_tidyGens hx]
  show decGroup n (blockKerGens ((I.1.2.2.2.1, I.1.2.1), bl)) = _
  rw [imp_gens_eq hI]
  exact decGroup_blockKerGens hx hwf hϕ

/-- `N ≤ G`. -/
theorem impKer_le (hI : ImpWF n I) (hs : I.2 = some (bl, idx)) :
    decGroup n (impKer I.1 bl) ≤ decGroup n I.1.2.1 := by
  obtain ⟨-, ⟨-, ϕ, hϕ⟩, -⟩ := hI.2 bl idx hs
  rw [decGroup_impKer hI hs hϕ]
  intro a ha
  exact actKer_le ϕ ha

/-- The kernel generators are well formed and short. -/
theorem wf_impKer (hI : ImpWF n I) : RawGens.WF n (impKer I.1 bl) :=
  wf_tidyGens hI.1.1 _

theorem length_impKer_le (hI : ImpWF n I) : (impKer I.1 bl).length ≤ n * n :=
  length_tidyGens hI.1.1 _

/-- The `j`-th representative of a child is well formed. -/
theorem wf_impRep (hI : ImpWF n I) (j : ℕ) : RawPerm.WF n (impRep I.1 bl j) :=
  wf_rawMul hI.1.2.2.2.2.2.2.1 (wf_normPerm hI.1.1 _)

/-- The `j`-th representative, decoded. -/
theorem decPerm_impRep (hI : ImpWF n I) (j : ℕ) :
    decPerm n (impRep I.1 bl j)
      = decPerm n I.1.2.2.1 * decPerm n (blockCosetRep (((I.1.2.2.2.1, I.1.2.1), bl), j)) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hσ : RawPerm.WF n I.1.2.2.1 := hI.1.2.2.2.2.2.2.1
  rw [impRep, rawMul_of_wf hσ (wf_normPerm hx _), decPerm_encPerm, decPerm_normPerm hx]

/-- **The cover Eq. (62) needs**, for `H = N`: the candidate set of the instance is the union
of the `|Ḡ|` left cosets `σ_j·N`.  Paper: Theorem 11.1.9, the descent step, with
Proposition 2.2.6 (a). -/
theorem cover_impPerms (hI : ImpWF n I) (hs : I.2 = some (bl, idx)) :
    (decImpSI n I).K = ⋃ σ ∈ impPerms n I.1 (bl, idx),
      σ • (decGroup n (impKer I.1 bl) : Set (Perm (Fin n))) := by
  obtain ⟨hb, ⟨hwf, ϕ, hϕ⟩, hidx⟩ := hI.2 bl idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hK : (decImpSI n I).K
      = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
    rw [decImpSI, decWinSI, decCoset_some]
  have hH : (decGroup n (impKer I.1 bl) : Set (Perm (Fin n)))
      = (actKer (descGens n I.1) ϕ : Set (Perm (Fin n))) := by
    rw [decGroup_impKer hI hs hϕ]
  have hcov := cover_blockCosetRep (dom := I.1.2.2.2.1) (bl := bl)
    (gens := descGens n I.1) hx hwf hϕ
  have hlist : impPerms n I.1 (bl, idx)
      = (List.range idx).map (fun j => decPerm n I.1.2.2.1 *
          decPerm n (blockCosetRep (((I.1.2.2.2.1,
            (descGens n I.1).map (encPerm n)), bl), j))) := by
    rw [impPerms]
    refine List.map_congr_left (fun j _ => ?_)
    rw [decPerm_impRep hI j, ← imp_gens_eq hI]
  rw [hK, hH, hlist, show (decGroup n I.1.2.1 : Set (Perm (Fin n)))
      = (genGroup (descGens n I.1) : Set (Perm (Fin n))) from rfl, hcov, ← hidx,
    smul_biUnion_index]

end Data

/-! ## The computable round -/

/-- Lift a child of the Chain Rule round to a child of this round: the same instance, with the
phase marker `none`. -/
def liftWin (o : Option RawWinSI) : Option RawImpSI :=
  o.elim none (fun J => some ((J, none) : RawImpSI))

/-- The `j`-th child: in the descend phase the instance whose group is `N` and whose
representative is `σ_j` (Prop. 11.1.6 with `H = N`), in the Chain Rule phase the child of
`Algo.chainRound`. -/
def impChild (p : RawImpSI × ℕ × RawCoset) : Option RawImpSI :=
  p.1.2.elim (liftWin (winChild (p.1.1, p.2.1, p.2.2)))
    (fun q => if q.2 ≤ p.2.1 then none
      else some ((p.1.1.1, impKer p.1.1 q.1, impRep p.1.1 q.1 p.2.1,
        p.1.1.2.2.2.1, p.1.1.2.2.2.2), none))

/-- The fold step: the join of the answers in the descend phase (`Algo.rawCosetJoin`), the
answer of the child in the Chain Rule phase (`Algo.winCombine`). -/
def impCombine (p : RawImpSI × ℕ × RawCoset × RawCoset) : RawCoset :=
  p.1.2.elim p.2.2.2 (fun _ => rawCosetJoin (p.1.1.2.2.2.1, p.2.2.1, p.2.2.2))

/-- The empty partial answer: the candidate set itself in the Chain Rule phase, the empty
coset in the descend phase. -/
def impInit (I : RawImpSI) : RawCoset :=
  I.2.elim (some (I.1.2.1, I.1.2.2.1)) (fun _ => none)

/-- The answer of the instance, read off the final state. -/
def impFinish (solveW : RawWinSI → RawCoset) (p : RawImpSI × RawCoset) : RawCoset :=
  p.1.2.elim (if (winOrbits (p.1.1.2.1, p.1.1.1)).length ≤ 1 then solveW p.1.1 else p.2)
    (fun _ => p.2)

theorem impChild_desc_eq_some {p : RawImpSI × ℕ × RawCoset} {J : RawImpSI}
    {bl : RawBlocks} {idx : ℕ}
    (hq : p.1.2 = some (bl, idx)) (hc : impChild p = some J) :
    p.2.1 < idx ∧ J = ((p.1.1.1, impKer p.1.1 bl, impRep p.1.1 bl p.2.1,
      p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [impChild, hq] at hc
  simp only [Option.elim] at hc
  by_cases hj : idx ≤ p.2.1
  · rw [if_pos hj] at hc; exact absurd hc (by simp)
  · rw [if_neg hj] at hc
    exact ⟨by omega, (Option.some.inj hc).symm⟩

theorem impChild_desc_eq_some_of {p : RawImpSI × ℕ × RawCoset}
    {bl : RawBlocks} {idx : ℕ}
    (hq : p.1.2 = some (bl, idx)) (hj : p.2.1 < idx) :
    impChild p = some ((p.1.1.1, impKer p.1.1 bl, impRep p.1.1 bl p.2.1,
      p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [impChild, hq]
  simp only [Option.elim]
  rw [if_neg (by omega)]

theorem impChild_chain {p : RawImpSI × ℕ × RawCoset} (hq : p.1.2 = none) :
    impChild p = liftWin (winChild (p.1.1, p.2.1, p.2.2)) := by
  rw [impChild, hq]
  rfl

theorem impChild_chain_eq_some {p : RawImpSI × ℕ × RawCoset} {J : RawImpSI}
    (hq : p.1.2 = none) (hc : impChild p = some J) :
    ∃ J', winChild (p.1.1, p.2.1, p.2.2) = some J' ∧ J = (J', none) := by
  rw [impChild_chain hq, liftWin] at hc
  rcases hw : winChild (p.1.1, p.2.1, p.2.2) with _ | J'
  · rw [hw] at hc; exact absurd hc (by simp)
  · rw [hw] at hc
    exact ⟨J', rfl, (Option.some.inj hc).symm⟩

/-- **The Imprimitive Luks round** (§11.1, Theorem 11.1.9).  `solveW` is the rest of Procedure
String-Isomorphism: it answers an instance whose group is transitive on the window, where
neither the descent nor the Chain Rule has anything left to say. -/
def impRound (n : ℕ) (solveW : RawWinSI → RawCoset) : Round RawImpSI RawCoset RawCoset where
  WF := ImpWF n
  ground := fun I => Enc.size I.1.2.2.2
  measure := fun I => 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
  width := fun I => I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2)
  child := impChild
  init := impInit
  combine := impCombine
  finish := impFinish solveW
  bot := none
  child_eq_none := by
    intro I j s hj
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        have hj' : I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) ≤ j := hj
        rw [hq] at hj'
        simp only [Option.elim] at hj'
        have hw : winChild (I.1, j, s) = none :=
          (chainRound n solveW).child_eq_none I.1 j s hj'
        show impChild (I, j, s) = none
        rw [impChild_chain (p := (I, j, s)) hq]
        show liftWin (winChild (I.1, j, s)) = none
        rw [hw, liftWin]
        rfl
    | some q =>
        have hj' : I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) ≤ j := hj
        rw [hq] at hj'
        simp only [Option.elim] at hj'
        show impChild (I, j, s) = none
        rw [impChild, hq]
        simp only [Option.elim]
        rw [if_pos hj']
  child_wf := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := impChild_chain_eq_some (p := (I, j, s)) hq hc
        refine ⟨(chainRound n solveW).child_wf I.1 j s J' hI.1 hw, ?_⟩
        intro bl idx hcon
        exact absurd hcon (by simp)
    | some q =>
        obtain ⟨bl, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := impChild_desc_eq_some (p := (I, j, s)) hq hc
        obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI.1
        refine ⟨⟨hx, hy, hnd, hlt, wf_impKer hI, length_impKer_le hI, wf_impRep hI j, ?_⟩, ?_⟩
        · rw [rawIsInvariant_eq_true_iff (wf_impKer (bl := bl) hI) hlt]
          exact isInvariant_of_le ((rawIsInvariant_eq_true_iff hgs hlt).1 hinv)
            (impKer_le hI hq)
        · intro bl' idx' hcon
          exact absurd hcon (by simp)
  child_measure := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := impChild_chain_eq_some (p := (I, j, s)) hq hc
        have h : J'.1.length < I.1.1.length :=
          (chainRound n solveW).child_measure I.1 j s J' hI.1 hw
        show 2 * J'.1.length + Option.elim (none : Option (RawBlocks × ℕ)) 0 (fun _ => 1)
          < 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
        rw [hq]
        simp only [Option.elim]
        omega
    | some q =>
        obtain ⟨bl, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := impChild_desc_eq_some (p := (I, j, s)) hq hc
        show 2 * I.1.1.length + Option.elim (none : Option (RawBlocks × ℕ)) 0 (fun _ => 1)
          < 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
        rw [hq]
        simp
  child_ground := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := impChild_chain_eq_some (p := (I, j, s)) hq hc
        exact (chainRound n solveW).child_ground I.1 j s J' hI.1 hw
    | some q =>
        obtain ⟨bl, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := impChild_desc_eq_some (p := (I, j, s)) hq hc
        exact le_refl _

/-! ## The link to the mathematical layer -/

/-- The mathematical round the imprimitive round implements: the descent of Eq. (62) over the
coset representatives of `N` in the descend phase, and Eq. (63) iterated over the orbits of
Eq. (64) in the Chain Rule phase. -/
noncomputable def impRoundReduction (n : ℕ) (solveW : RawWinSI → RawCoset) (I : RawImpSI) :
    Babai.SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  I.2.elim (chainRoundReduction n solveW I.1) (fun q =>
    descentChain (decGroup n (impKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
      (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∅ (impPerms n I.1 q))

/-- **The fold of the descend phase walks the descent chain.** -/
theorem loopMatch_impDesc (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawImpSI}
    (hI : ImpWF n I) {q : RawBlocks × ℕ} (hq : I.2 = some q) :
    ∀ (k j : ℕ), j + k = q.2 →
      ∀ (acc : Set (Perm (Fin n))) (s : RawCoset), decCoset n s = acc →
        LoopMatch (impRound n solveW) (decImpSI n) (decCoset n) I k j s
          (descentChain (decGroup n (impKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
            (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) acc
            ((impPerms n I.1 q).drop j)) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  intro k
  induction k with
  | zero =>
      intro j hj acc s hs
      have hdrop : (impPerms n I.1 q).drop j = [] := by
        apply List.drop_eq_nil_of_le
        rw [length_impPerms]; omega
      rw [hdrop, descentChain]
      refine LoopMatch.done 0 j s acc ?_ ?_
      · exact (impRound n solveW).child_eq_none I j s
          (by show I.2.elim _ (fun q => q.2) ≤ j; rw [hq]; simp only [Option.elim]; omega)
      · show decCoset n (impFinish solveW (I, s)) = acc
        rw [impFinish, hq]
        exact hs
  | succ k ih =>
      intro j hj acc s hs
      have hjl : j < (impPerms n I.1 q).length := by rw [length_impPerms]; omega
      have hdrop : (impPerms n I.1 q).drop j
          = ((impPerms n I.1 q)[j]'hjl) :: (impPerms n I.1 q).drop (j + 1) :=
        List.drop_eq_getElem_cons hjl
      rw [hdrop, descentChain]
      have hjlt : j < q.2 := by rw [length_impPerms] at hjl; omega
      set J : RawImpSI :=
        ((I.1.1, impKer I.1 q.1, impRep I.1 q.1 j, I.1.2.2.2.1, I.1.2.2.2.2), none) with hJ
      have hchild : (impRound n solveW).child (I, j, s) = some J :=
        impChild_desc_eq_some_of (p := (I, j, s)) hq hjlt
      have hdec : decImpSI n J
          = ⟨((impPerms n I.1 q)[j]'hjl) • (decGroup n (impKer I.1 q.1) : Set (Perm (Fin n))),
              winSet n I.1.1, decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
        rw [decImpSI, decWinSI, hJ]
        simp only
        rw [decCoset_some, getElem_impPerms]
      rw [← hdec]
      refine LoopMatch.call k j s J _ hchild ?_
      intro a ha
      refine ih (j + 1) (by omega) (cosetHull (acc ∪ (decImpSI n J).answer))
        ((impRound n solveW).combine (I, j, s, a)) ?_
      show decCoset n (impCombine (I, j, s, a)) = _
      rw [impCombine, hq]
      simp only [Option.elim]
      rw [decCoset_rawCosetJoin hx, hs, ha]

/-- **The fold of the Chain Rule phase walks the chain of Eq. (63).**  This is
`Algo.loopMatch_chainRound` for the phase-marked round. -/
theorem loopMatch_impChain (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawImpSI}
    (hI : ImpWF n I) (hq : I.2 = none) (h2 : 1 < (winOrbits (I.1.2.1, I.1.1)).length) :
    ∀ (k j : ℕ), j + k = (winOrbits (I.1.2.1, I.1.1)).length →
      ∀ (C : Set (Perm (Fin n))) (s : RawCoset), StateOK n I.1 C s →
        LoopMatch (impRound n solveW) (decImpSI n) (decCoset n) I k j s
          (cosetChain (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2)
            (((winOrbits (I.1.2.1, I.1.1)).drop j).map (winSet n)) C) := by
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI.1
  intro k
  induction k with
  | zero =>
      intro j hj C s hs
      have hdrop : (winOrbits (I.1.2.1, I.1.1)).drop j = [] := by
        apply List.drop_eq_nil_of_le; omega
      rw [hdrop, List.map_nil, cosetChain]
      refine LoopMatch.done 0 j s C ?_ ?_
      · exact (impRound n solveW).child_eq_none I j s
          (by show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length _ ≤ j
              rw [hq]; simp only [Option.elim]; omega)
      · show decCoset n (impFinish solveW (I, s)) = C
        rw [impFinish, hq]
        simp only [Option.elim]
        rw [if_neg (by omega)]
        exact hs.1
  | succ k ih =>
      intro j hj C s hs
      have hjl : j < (winOrbits (I.1.2.1, I.1.1)).length := by omega
      have hdrop : (winOrbits (I.1.2.1, I.1.1)).drop j
          = ((winOrbits (I.1.2.1, I.1.1))[j]'hjl) :: (winOrbits (I.1.2.1, I.1.1)).drop (j + 1) :=
        List.drop_eq_getElem_cons hjl
      rw [hdrop, List.map_cons, cosetChain]
      cases s with
      | none =>
        have hCe : C = ∅ := by rw [← hs.1]; rfl
        rw [if_pos hCe]
        refine LoopMatch.done (k + 1) j none ∅ ?_ ?_
        · show impChild (I, j, none) = none
          rw [impChild_chain (p := (I, j, (none : RawCoset))) hq]
          show liftWin (winChild (I.1, j, (none : RawCoset))) = none
          rw [show winChild (I.1, j, (none : RawCoset)) = none from rfl, liftWin]
          rfl
        · show decCoset n (impFinish solveW (I, (none : RawCoset))) = ∅
          rw [impFinish, hq]
          simp only [Option.elim]
          rw [if_neg (by omega)]
          rfl
      | some gτ =>
        obtain ⟨g, τ⟩ := gτ
        have hsv : (some (g, τ) : RawCoset) = some (g, τ) := rfl
        have hCne : C ≠ ∅ := by
          rw [← hs.1]
          intro hc
          have : decPerm n τ ∈ decCoset n (some (g, τ)) := ⟨1, one_mem _, by rw [mul_one]⟩
          rw [hc] at this
          exact this
        rw [if_neg hCne]
        have hgetd : (winOrbits (I.1.2.1, I.1.1)).getD j []
            = (winOrbits (I.1.2.1, I.1.1))[j]'hjl := List.getD_eq_getElem _ _ hjl
        have hmemw : (winOrbits (I.1.2.1, I.1.1))[j]'hjl ∈ winOrbits (I.1.2.1, I.1.1) :=
          List.getElem_mem hjl
        have hne : (winOrbits (I.1.2.1, I.1.1)).getD j [] ≠ [] := by
          rw [hgetd]; exact winOrbits_ne_nil hmemw
        have hgle : decGroup n g ≤ decGroup n I.1.2.1 := hs.2.2 g τ hsv
        have htidy : decGroup n (tidyGens (I.1.2.2.2.1, g)) = decGroup n g :=
          decGroup_tidyGens hx g
        have hinvw : rawIsInvariant (tidyGens (I.1.2.2.2.1, g),
            (winOrbits (I.1.2.1, I.1.1)).getD j []) = true := by
          rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g)
            (by rw [hgetd]; exact winOrbits_lt hgs hlt hinv hmemw)]
          obtain ⟨p, hp, hpe⟩ := winOrbits_mem hmemw
          have hpn : p < n := hlt p hp
          have hset : {y : Fin n | (y : ℕ) ∈ (winOrbits (I.1.2.1, I.1.1)).getD j []}
              = {y : Fin n | (y : ℕ) ∈ rawOrbit (I.1.2.1, p)} := by
            rw [hgetd, hpe]
          rw [hset, htidy]
          exact isInvariant_of_le (isInvariant_rawOrbit hgs hpn) hgle
        have hwchild : winChild (I.1, j, (some (g, τ) : RawCoset))
            = some ((winOrbits (I.1.2.1, I.1.1)).getD j [], tidyGens (I.1.2.2.2.1, g),
              normPerm (I.1.2.2.2.1, τ), I.1.2.2.2.1, I.1.2.2.2.2) :=
          winChild_eq_some_of (p := (I.1, j, (some (g, τ) : RawCoset))) hsv hne h2 hinvw
        set J' : RawWinSI := ((winOrbits (I.1.2.1, I.1.1)).getD j [], tidyGens (I.1.2.2.2.1, g),
          normPerm (I.1.2.2.2.1, τ), I.1.2.2.2.1, I.1.2.2.2.2) with hJ'
        have hchild : (impRound n solveW).child (I, j, (some (g, τ) : RawCoset))
            = some ((J', none) : RawImpSI) := by
          show impChild (I, j, (some (g, τ) : RawCoset)) = _
          rw [impChild_chain (p := (I, j, (some (g, τ) : RawCoset))) hq]
          show liftWin (winChild (I.1, j, (some (g, τ) : RawCoset))) = _
          rw [hwchild, liftWin]
          rfl
        have hdec : decImpSI n ((J', none) : RawImpSI)
            = ⟨C, winSet n ((winOrbits (I.1.2.1, I.1.1))[j]'hjl),
                decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
          have hK : decCoset n (some (tidyGens (I.1.2.2.2.1, g),
              normPerm (I.1.2.2.2.1, τ))) = C := by
            rw [← hs.1, hsv]
            show {ρ | ∃ u ∈ decGroup n (tidyGens (I.1.2.2.2.1, g)),
              ρ = decPerm n (normPerm (I.1.2.2.2.1, τ)) * u} = _
            rw [htidy, decPerm_normPerm hx τ]
            rfl
          rw [decImpSI, decWinSI, hJ']
          simp only
          rw [hK, hgetd]
        rw [← hdec]
        refine LoopMatch.call k j (some (g, τ)) ((J', none) : RawImpSI) _ hchild ?_
        intro a ha
        have hans : (decImpSI n ((J', none) : RawImpSI)).answer
            = Babai.wIso (winSet n ((winOrbits (I.1.2.1, I.1.1))[j]'hjl)) C
                (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) := by
          rw [Babai.SIInstance.answer, hdec]
        have hsub : (decImpSI n ((J', none) : RawImpSI)).answer ⊆ C := by
          rw [hans]; exact fun ρ hρ => hρ.1
        have hcomb : (impRound n solveW).combine (I, j, (some (g, τ) : RawCoset), a) = a := by
          show impCombine (I, j, (some (g, τ) : RawCoset), a) = a
          rw [impCombine, hq]
          rfl
        rw [hcomb]
        refine ih (j + 1) (by omega) ((decImpSI n ((J', none) : RawImpSI)).answer) a ?_
        refine ⟨ha, le_trans hsub hs.2.1, ?_⟩
        intro g₂ τ₂ ha2
        refine decGroup_le_of_subset (σ₀ := decPerm n I.1.2.2.1) (τ := decPerm n τ₂) ?_
        have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I.1).K := by
          rw [← ha2, ha]
          exact le_trans hsub hs.2.1
        exact h1

/-- **The link (Theorem 11.1.9).**  The imprimitive round implements the descent of Eq. (62)
to `N` followed by the Chain Rule over the orbits. -/
theorem implements_impRound (n : ℕ) (solveW : RawWinSI → RawCoset) :
    Implements (impRound n solveW) id (decImpSI n) (decCoset n) (impRoundReduction n solveW) := by
  intro I hI
  show LoopMatch (impRound n solveW) (decImpSI n) (decCoset n) I
    (I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2)) 0 (impInit I)
    (impRoundReduction n solveW I)
  rw [impRoundReduction, impInit]
  obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [hq]
      simp only [Option.elim]
      rw [chainRoundReduction]
      by_cases h2 : (winOrbits (I.1.2.1, I.1.1)).length ≤ 1
      · rw [if_pos h2]
        refine LoopMatch.done _ 0 _ _ ?_ ?_
        · have hw : winChild (I.1, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset)) = none := by
            rw [winChild, Option.bind_some]
            by_cases hd : (winOrbits (I.1.2.1, I.1.1)).getD 0 [] = []
            · rw [if_pos hd]
            · rw [if_neg hd, if_pos h2]
          show impChild (I, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset)) = none
          rw [impChild_chain (p := (I, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset))) hq]
          show liftWin (winChild (I.1, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset))) = none
          rw [hw, liftWin]
          rfl
        · show decCoset n (impFinish solveW (I, some (I.1.2.1, I.1.2.2.1)))
            = decCoset n (solveW I.1)
          rw [impFinish, hq]
          simp only [Option.elim]
          rw [if_pos h2]
      · rw [if_neg h2]
        have h2' : 1 < (winOrbits (I.1.2.1, I.1.1)).length := by omega
        have := loopMatch_impChain n solveW hI hq h2'
          (winOrbits (I.1.2.1, I.1.1)).length 0 (by omega)
          (decWinSI n I.1).K (some (I.1.2.1, I.1.2.2.1)) ⟨rfl, le_refl _, ?_⟩
        · simpa using this
        · intro g τ hgt
          have : g = I.1.2.1 := congrArg (fun z => (Option.getD z (I.1.2.1, I.1.2.2.1)).1) hgt.symm
          rw [this]
  | some q =>
      rw [hq]
      simp only [Option.elim]
      have := loopMatch_impDesc n solveW hI hq q.2 0 (by omega) ∅ none rfl
      simpa using this

/-- **The mathematical round is correct**: its value is the answer of the instance, provided
`solveW` answers the instances the round hands on.

*Proof.*  In the descend phase, `Algo.cover_impPerms` is the decomposition of the candidate
set into the `|Ḡ|` left cosets of `N` (Prop. 2.2.6 (a) for the block action) and
Observation 11.1.11 says the answer is empty or a coset, so `Algo.run_descentChain` is
Eq. (62).  In the Chain Rule phase it is `Algo.run_chainRoundReduction`. -/
theorem run_impRoundReduction (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawImpSI}
    (hI : ImpWF n I)
    (hsolve : I.2 = none → (winOrbits (I.1.2.1, I.1.1)).length ≤ 1 →
      decCoset n (solveW I.1) = (decImpSI n I).answer) :
    (impRoundReduction n solveW I).run = (decImpSI n I).answer := by
  rw [impRoundReduction]
  obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [hq]
      simp only [Option.elim]
      exact run_chainRoundReduction n solveW hI.1 (hsolve hq)
  | some q =>
      rw [hq]
      simp only [Option.elim]
      have hinv : Babai.IsInvariant (decGroup n I.1.2.1) (winSet n I.1.1) :=
        (rawIsInvariant_eq_true_iff hI.1.2.2.2.2.1 hI.1.2.2.2.1).1 hI.1.2.2.2.2.2.2.2
      refine run_descentChain _ _ _ _ _ _ (cover_impPerms hI hq) ?_
      intro τ hτ
      refine ⟨Babai.wAutSubgroup (decGroup n I.1.2.1) (winSet n I.1.1) hinv
        (decStrN n I.1.2.2.2.1), ?_⟩
      have hK : (decImpSI n I).K
          = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
        rw [decImpSI, decWinSI, decCoset_some]
      have h := Babai.wIso_eq_smul_wAut (G := decGroup n I.1.2.1) (Δ := winSet n I.1.1) hinv
        (decPerm n I.1.2.2.1) (σ' := τ) (x := decStrN n I.1.2.2.2.1)
        (y := decStrN n I.1.2.2.2.2) (by rwa [← hK])
      rw [hK, h]
      rfl

/-! ## The running time -/

theorem polyFun_liftWin : PolyFun liftWin := by
  have hopt := PolyFun.optionElim (g := fun _ : Option RawWinSI => (none : Option RawImpSI))
    (h := fun z : RawWinSI × Option RawWinSI => some ((z.1, none) : RawImpSI))
    (polyFun_const (none : Option RawImpSI))
    ((polyFun_fst.pair (polyFun_const (none : Option (RawBlocks × ℕ)))).comp polyFun_some)
  exact ((polyFun_id.pair polyFun_id).comp hopt).of_eq (fun _ => rfl)

theorem polyFun_impKer : PolyFun (fun z : RawBlocks × RawWinSI => impKer z.2 z.1) := by
  have hx : PolyFun (fun z : RawBlocks × RawWinSI => z.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : RawBlocks × RawWinSI => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  exact ((hx.pair (((hx.pair hgens).pair polyFun_fst).comp polyFun_blockKerGens)).comp
    polyFun_tidyGens).of_eq (fun _ => rfl)

theorem polyFun_impRep :
    PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => impRep z.2 z.1.1 z.1.2) := by
  have hx : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => z.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hrep : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hbl : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hj : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hcos : PolyFun (fun z : (RawBlocks × ℕ) × RawWinSI =>
      blockCosetRep (((z.2.2.2.2.1, z.2.2.1), z.1.1), z.1.2)) :=
    (((hx.pair hgens).pair hbl).pair hj).comp polyFun_blockCosetRep
  exact ((hrep.pair ((hx.pair hcos).comp polyFun_normPerm)).comp polyFun_rawMul).of_eq
    (fun _ => rfl)

theorem polyFun_impChild : PolyFun impChild := by
  classical
  have hΔ : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.2) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd
  have hW : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hbl : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hidx : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hj : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hker : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) => impKer z.2.1 z.1.1) :=
    (hbl.pair hW).comp polyFun_impKer
  have hrep : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) =>
      impRep z.2.1 z.1.1 z.2.2) :=
    ((hbl.pair hj).pair hW).comp polyFun_impRep
  have hcond : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) =>
      decide (z.1.2 ≤ z.2.2)) := (hidx.pair hj).comp polyFun_le
  have hsome : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) =>
      (some ((z.2.1.1, impKer z.2.1 z.1.1, impRep z.2.1 z.1.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none) : Option RawImpSI)) :=
    ((hΔ.pair (hker.pair (hrep.pair (hx.pair hy)))).pair
      (polyFun_const (none : Option (RawBlocks × ℕ)))).comp polyFun_some
  have hbody : PolyFun (fun z : (RawBlocks × ℕ) × (RawWinSI × ℕ) =>
      if z.1.2 ≤ z.2.2 then (none : Option RawImpSI)
      else some ((z.2.1.1, impKer z.2.1 z.1.1, impRep z.2.1 z.1.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none)) :=
    (PolyFun.ite hcond (polyFun_const (none : Option RawImpSI)) hsome).of_eq (fun z => by
      by_cases h : z.1.2 ≤ z.2.2 <;> simp [h])
  have hchain : PolyFun (fun p : RawImpSI × ℕ × RawCoset =>
      liftWin (winChild (p.1.1, p.2.1, p.2.2))) :=
    (((polyFun_fst.comp polyFun_fst).pair ((polyFun_snd.comp polyFun_fst).pair
      (polyFun_snd.comp polyFun_snd))).comp polyFun_winChild).comp polyFun_liftWin
  have hmid : PolyFun (fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset) =>
      ((z.1, (z.2.1.1, z.2.2.1)) : (RawBlocks × ℕ) × (RawWinSI × ℕ))) :=
    polyFun_fst.pair (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))
  have hopt := PolyFun.optionElim
    (g := fun z : RawImpSI × ℕ × RawCoset => liftWin (winChild (z.1.1, z.2.1, z.2.2)))
    (h := fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset) =>
      if z.1.2 ≤ z.2.2.1 then (none : Option RawImpSI)
      else some ((z.2.1.1.1, impKer z.2.1.1 z.1.1, impRep z.2.1.1 z.1.1 z.2.2.1,
        z.2.1.1.2.2.2.1, z.2.1.1.2.2.2.2), none))
    hchain (hmid.comp hbody)
  have hin : PolyFun (fun p : RawImpSI × ℕ × RawCoset =>
      ((p.1.2, p) : Option (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  refine (hin.comp hopt).of_eq (fun p => ?_)
  rw [impChild]

theorem polyFun_impCombine : PolyFun impCombine := by
  have hx : PolyFun (fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset × RawCoset) =>
      z.2.1.1.2.2.2.1) :=
    ((((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hs : PolyFun (fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset × RawCoset) =>
      z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset × RawCoset) =>
      z.2.2.2.2) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  have hopt := PolyFun.optionElim
    (g := fun z : RawImpSI × ℕ × RawCoset × RawCoset => z.2.2.2)
    (h := fun z : (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset × RawCoset) =>
      rawCosetJoin (z.2.1.1.2.2.2.1, z.2.2.2.1, z.2.2.2.2))
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)
    ((hx.pair (hs.pair ha)).comp polyFun_rawCosetJoin)
  have hin : PolyFun (fun p : RawImpSI × ℕ × RawCoset × RawCoset =>
      ((p.1.2, p) : Option (RawBlocks × ℕ) × (RawImpSI × ℕ × RawCoset × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  exact (hin.comp hopt).of_eq (fun p => rfl)

theorem polyFun_impInit : PolyFun impInit := by
  have hopt := PolyFun.optionElim
    (g := fun I : RawImpSI => (some (I.1.2.1, I.1.2.2.1) : RawCoset))
    (h := fun z : (RawBlocks × ℕ) × RawImpSI => (none : RawCoset))
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp polyFun_some)
    (polyFun_const (none : RawCoset))
  have hin : PolyFun (fun I : RawImpSI =>
      ((I.2, I) : Option (RawBlocks × ℕ) × RawImpSI)) := polyFun_snd.pair polyFun_id
  exact (hin.comp hopt).of_eq (fun I => rfl)


/-! ## The cost of the round -/

/-- The size of the block data: a block system and the index of `N`, a natural of at most
`4m² + 1` bits. -/
def impDataBound (m : ℕ) : ℕ := 2 + 2 * blocksBound m + 2 * (4 * (m * m) + 3)

/-- **The size bound of the imprimitive round.** -/
def impBound (m : ℕ) : ℕ := 2 * chainBound m + 2 * impDataBound m

theorem chainBound_le_impBound (m : ℕ) : chainBound m ≤ impBound m := by
  have h1 : impBound m = 2 * chainBound m + 2 * impDataBound m := rfl
  omega

theorem four_le_impBound (m : ℕ) : 4 ≤ impBound m := by
  have h1 : impBound m = 2 * chainBound m + 2 * impDataBound m := rfl
  have h2 : impDataBound m = 2 + 2 * blocksBound m + 2 * (4 * (m * m) + 3) := rfl
  omega

theorem polyBound_impDataBound : PolyBound impDataBound :=
  ((polyBound_const 2).add ((polyBound_const 2).mul polyBound_blocksBound)).add
    ((polyBound_const 2).mul
      (((polyBound_const 4).mul (polyBound_id.mul polyBound_id)).add (polyBound_const 3)))

theorem polyBound_impBound : PolyBound impBound :=
  ((polyBound_const 2).mul polyBound_chainBound).add
    ((polyBound_const 2).mul polyBound_impDataBound)

theorem mono_impDataBound : Monotone impDataBound := by
  intro a b hab
  have h1 : blocksBound a ≤ blocksBound b := mono_blocksBound hab
  have h2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
  have h3 : impDataBound a = 2 + 2 * blocksBound a + 2 * (4 * (a * a) + 3) := rfl
  have h4 : impDataBound b = 2 + 2 * blocksBound b + 2 * (4 * (b * b) + 3) := rfl
  omega

theorem mono_impBound : Monotone impBound := by
  intro a b hab
  have h1 : chainBound a ≤ chainBound b := mono_chainBound hab
  have h2 : impDataBound a ≤ impDataBound b := mono_impDataBound hab
  have h3 : impBound a = 2 * chainBound a + 2 * impDataBound a := rfl
  have h4 : impBound b = 2 * chainBound b + 2 * impDataBound b := rfl
  omega

/-- The domain size is at most the size of the strings, which is the ground size. -/
theorem imp_le_ground {I : RawImpSI} (hI : ImpWF n I) : n ≤ Enc.size I.1.2.2.2 :=
  le_size_strings hI.1

/-- **The block data is polynomially small.**  The block system is a partition of at most `n`
points, and the index of `N` is below `(n + m)^(n + m)` with `m ≤ n`
(`Algo.size_winCosetIndex_le`). -/
theorem size_impData_le {I : RawImpSI} (hI : ImpWF n I) :
    Enc.size I.2 ≤ impDataBound (Enc.size I.1.2.2.2) := by
  set m := Enc.size I.1.2.2.2 with hm
  have hnm : n ≤ m := imp_le_ground hI
  have hbd : impDataBound m = 2 + 2 * blocksBound m + 2 * (4 * (m * m) + 3) := rfl
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [ho]
      have h1 : Enc.size (none : Option (RawBlocks × ℕ)) = 2 := size_none
      omega
  | some q =>
      obtain ⟨hb, -, hidx⟩ := hI.2 q.1 q.2 ho
      rw [ho]
      have h0 : Enc.size (some q) = Enc.size q + 2 := size_some_eq _
      have h1 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := size_pair_le' q
      have h2 : Enc.size q.1 ≤ blocksBound m := size_blocks_le hb hnm
      have h3 : Enc.size q.2 ≤ 4 * (m * m) + 3 := by
        have e1 : Enc.size q.2 = Nat.size q.2 + 2 := Small.size_nat q.2
        have e2 : Nat.size q.2 ≤ (n + q.1.length) * (n + q.1.length) + 1 := by
          rw [hidx]
          exact size_winCosetIndex_le (nodup_extWin n q.1.length)
            (fun x hx => lt_extWin hx) _
        have e3 : q.1.length ≤ n := hb.length_le
        have e4 : (n + q.1.length) * (n + q.1.length) ≤ (2 * m) * (2 * m) :=
          Nat.mul_le_mul (by omega) (by omega)
        have e5 : (2 * m) * (2 * m) = 4 * (m * m) := by ring
        omega
      omega

/-- **A well-formed instance is small.** -/
theorem size_impSI_le {I : RawImpSI} (hI : ImpWF n I) :
    Enc.size I ≤ impBound (Enc.size I.1.2.2.2) := by
  have h1 : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := size_pair_le' I
  have h2 : Enc.size I.1 ≤ chainBound (Enc.size I.1.2.2.2) := size_winSI_le hI.1
  have h3 : Enc.size I.2 ≤ impDataBound (Enc.size I.1.2.2.2) := size_impData_le hI
  have h4 : impBound (Enc.size I.1.2.2.2)
      = 2 * chainBound (Enc.size I.1.2.2.2) + 2 * impDataBound (Enc.size I.1.2.2.2) := rfl
  omega

/-- **The cost data of the imprimitive round.**  `solveW` is charged for, as in
`Algo.chainCost`.  The width bound `wb` of the descend phase comes from the caller:
Theorem 11.1.9 says the multiplicative cost of the descent is `|Ḡ|`, and it is §15 line 2 that
bounds `|Ḡ|` quasipolynomially (`|Ḡ| ≤ ℓ!` with `ℓ = (log n)³`).  The Chain Rule phase has at
most as many children as the window has points, which is at most the ground size. -/
def impCost (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (wb : ℕ → ℕ) (hwb : QuasiPolyBound wb)
    (hwidth : ∀ I, ImpWF n I → I.2.elim 0 (fun q => q.2) ≤ wb (Enc.size I.1.2.2.2)) :
    Round.Cost (impRound n solveW) where
  bound := impBound
  polyBound_bound := polyBound_impBound
  mono_bound := mono_impBound
  widthBound := fun m => wb m + m
  quasiPolyBound_widthBound := hwb.add polyBound_id.quasiPoly
  quasiPolyFun_child := polyFun_impChild.quasiPolyFun
  quasiPolyFun_init := polyFun_impInit.quasiPolyFun
  quasiPolyFun_combine := polyFun_impCombine.quasiPolyFun
  quasiPolyFun_finish := by
    have horbW : PolyFun (fun z : RawImpSI × RawCoset =>
        decide ((winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1)) := by
      have h1 : PolyFun (fun z : RawImpSI × RawCoset =>
          winOrbits (z.1.1.2.1, z.1.1.1)) :=
        (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
          ((polyFun_fst.comp polyFun_fst).comp polyFun_fst))).comp polyFun_winOrbits
      exact ((h1.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
    have hg : QuasiPolyFun (fun z : RawImpSI × RawCoset =>
        if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then solveW z.1.1 else z.2) :=
      (QuasiPolyFun.ite horbW ((polyFun_fst.comp polyFun_fst).comp_quasi hsolve)
        polyFun_snd.quasiPolyFun).of_eq (fun z => by
          by_cases h : (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 <;> simp [h])
    have hopt := QuasiPolyFun.optionElim
      (g := fun z : RawImpSI × RawCoset =>
        if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then solveW z.1.1 else z.2)
      (h := fun z : (RawBlocks × ℕ) × (RawImpSI × RawCoset) => z.2.2)
      hg ((polyFun_snd.comp polyFun_snd).quasiPolyFun)
    have hin : PolyFun (fun p : RawImpSI × RawCoset =>
        ((p.1.2, p) : Option (RawBlocks × ℕ) × (RawImpSI × RawCoset))) :=
      (polyFun_fst.comp polyFun_snd).pair polyFun_id
    exact (hin.comp_quasi hopt).of_eq (fun p => rfl)
  ground_le := by
    intro I
    show Enc.size I.1.2.2.2 ≤ Enc.size I
    have h1 : Enc.size I.1.2.2.2 ≤ Enc.size I.1 :=
      le_trans (size_snd_le' I.1.2.2) (le_trans (size_snd_le' I.1.2) (size_snd_le' I.1))
    have h2 : Enc.size I.1 ≤ Enc.size I := size_fst_le' I
    omega
  size_le := fun I hI => size_impSI_le hI
  init_le := by
    intro I hI
    show Enc.size (impInit I) ≤ impBound (Enc.size I.1.2.2.2)
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    have hcb := chainBound_le_impBound (Enc.size I.1.2.2.2)
    cases o with
    | none =>
        have h0 : impInit I = some (I.1.2.1, I.1.2.2.1) := by rw [impInit, ho]; rfl
        have h1 : Enc.size (some (I.1.2.1, I.1.2.2.1) : RawCoset)
            = Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm) + 2 := size_some_eq _
        have h2 : Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm)
            ≤ 2 * Enc.size I.1.2.1 + 2 * Enc.size I.1.2.2.1 := size_pair_le' _
        have h3 := size_gens_le hI.1
        have h4 := size_rep_le hI.1
        have hSG := strBound_le_gensBound (Enc.size I.1.2.2.2)
        have h5 : chainBound (Enc.size I.1.2.2.2)
            = 16 * (gensBound (Enc.size I.1.2.2.2) + Enc.size I.1.2.2.2 + 1) := rfl
        rw [h0]
        omega
    | some q =>
        have h0 : impInit I = none := by rw [impInit, ho]; rfl
        have h1 : Enc.size (none : RawCoset) = 2 := size_none
        have h2 := four_le_impBound (Enc.size I.1.2.2.2)
        rw [h0]
        omega
  combine_le := by
    intro I j s a hI hs ha
    show Enc.size (impCombine (I, j, s, a)) ≤ impBound (Enc.size I.1.2.2.2)
    rw [impCombine]
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none => rw [ho]; exact ha
    | some q =>
        rw [ho]
        simp only [Option.elim]
        exact size_rawCosetJoin_le (n := n) hI.1.1 (imp_le_ground hI)
          (chainBound_le_impBound _) hs ha
  finish_le := by
    intro I s hI hs
    show Enc.size (impFinish solveW (I, s)) ≤ impBound (Enc.size I.1.2.2.2)
    rw [impFinish]
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        rw [ho]
        simp only [Option.elim]
        by_cases h : (winOrbits (I.1.2.1, I.1.1)).length ≤ 1
        · rw [if_pos h]
          exact le_trans (hsize I.1 hI.1) (chainBound_le_impBound _)
        · rw [if_neg h]; exact hs
    | some q => rw [ho]; exact hs
  bot_le := by
    intro m
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := four_le_impBound m
    show Enc.size (none : RawCoset) ≤ impBound m
    omega
  width_le := by
    intro I hI
    show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2)
      ≤ wb (Enc.size I.1.2.2.2) + Enc.size I.1.2.2.2
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        rw [ho]
        simp only [Option.elim]
        have h1 : (winOrbits (I.1.2.1, I.1.1)).length ≤ I.1.1.length :=
          length_winOrbits_le _ _
        have h2 : I.1.1.length ≤ n := length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1
        have h3 : n ≤ Enc.size I.1.2.2.2 := imp_le_ground hI
        omega
    | some q =>
        have h := hwidth I hI
        rw [ho] at h ⊢
        simp only [Option.elim] at h ⊢
        omega

/-! ## §15, line 2: the width bound the master procedure supplies

Theorem 11.1.9 alone says nothing about `|Ḡ|`; §15 line 2 is where it is bounded, by `ℓ!`
with `ℓ = (log₂ n)³` (`Babai.ellOf`, `Workspace/Master/TestSet.lean`, spelled out here so that
the algorithmic layer stays independent of `Workspace/Master/`).  That bound is
quasipolynomial, so a caller that has it can hand `Algo.impCost` its width bound and the round
composes; `Algo.impCostLine2` is that instance. -/

/-- `ℓ!` with `ℓ = (log₂ m)³`: the multiplicative cost of §15, line 2. -/
def ellBound (m : ℕ) : ℕ := Nat.factorial (Nat.log 2 m ^ 3)

/-- **`ℓ!` is quasipolynomial** (§15, line 2): `ℓ! ≤ ℓ^ℓ ≤ (2^ℓ)^ℓ = 2^{ℓ²}` and
`ℓ² ≤ (log₂ m + 2)^6`. -/
theorem quasiPolyBound_ellBound : QuasiPolyBound ellBound := by
  refine ⟨6, fun m => ?_⟩
  set a := Nat.log 2 m with ha
  set L := (a + 2) ^ 3 with hL
  have h1 : a ^ 3 ≤ L := Nat.pow_le_pow_left (by omega) 3
  have hL1 : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  have h2 : ellBound m ≤ L ^ L := by
    calc ellBound m ≤ (a ^ 3) ^ (a ^ 3) := Nat.factorial_le_pow _
      _ ≤ L ^ (a ^ 3) := Nat.pow_le_pow_left h1 _
      _ ≤ L ^ L := Nat.pow_le_pow_right hL1 h1
  have h3 : L ^ L ≤ (2 ^ L) ^ L :=
    Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) L
  have h4 : (2 ^ L) ^ L = 2 ^ (L * L) := by rw [← pow_mul]
  have h5 : L * L = (a + 2) ^ 6 := by rw [hL, ← pow_add]
  calc ellBound m ≤ L ^ L := h2
    _ ≤ (2 ^ L) ^ L := h3
    _ = 2 ^ (L * L) := h4
    _ = 2 ^ ((a + 2) ^ 6) := by rw [h5]

/-- **The cost data of the imprimitive round at an instance of §15, line 2**: a caller that
knows `|Ḡ| ≤ ℓ!` — which is what line 2 tests — gets the round's `Algo.Round.Cost` with no
further hypothesis on the width. -/
def impCostLine2 (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (hwidth : ∀ I, ImpWF n I →
      I.2.elim 0 (fun q => q.2) ≤ ellBound (Enc.size I.1.2.2.2)) :
    Round.Cost (impRound n solveW) :=
  impCost n solveW hsolve hsize ellBound quasiPolyBound_ellBound hwidth

/-! ## Discharging the width bound from `|Ḡ| ≤ ℓ!` (risk R-A7-3)

`Algo.impCostLine2` asks its caller for a bound on the *stored* index of the descend phase.
That index is now known to be `|Ḡ|` (`Algo.blockCosetIndex_eq_card_range`,
`Algo.blockCosetIndex_eq_card_onBlocks`), so a caller who has line 2's test `|Ḡ| ≤ ℓ!` can
discharge the hypothesis without knowing anything about the stabilizer chain. -/

section WidthCard

/-- **The stored width of a descend instance is `|Ḡ|`**: the order of the image of the action
on the blocks.  Paper: Theorem 11.1.9, "`m|Ḡ| = m|G/N|` instances". -/
theorem impWidth_eq_card_range {I : RawImpSI} (hI : ImpWF n I) {bl : RawBlocks} {idx : ℕ}
    (hs : I.2 = some (bl, idx))
    {ϕ : genGroup (descGens n I.1) →* Perm (Fin bl.length)}
    (hϕ : ImgsOf (descGens n I.1) (blockImgsOf n bl (descGens n I.1)) ϕ) :
    idx = Nat.card ϕ.range := by
  obtain ⟨-, -, hidx⟩ := hI.2 bl idx hs
  rw [hidx]
  exact blockCosetIndex_eq_card_range hI.1.1 hϕ

/-- **The cost data of §15, line 2, from `|Ḡ| ≤ ℓ!` alone.**  This is `Algo.impCostLine2` with
its width hypothesis discharged: the caller states line 2's bound on the order of the induced
group `Ḡ`, which is what line 2 actually tests, instead of a bound on the number the
stabilizer chain happens to produce. -/
def impCostLine2_of_card (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (hcard : ∀ I : RawImpSI, ImpWF n I → ∀ (bl : RawBlocks) (idx : ℕ),
      I.2 = some (bl, idx) →
      ∀ ϕ : genGroup (descGens n I.1) →* Perm (Fin bl.length),
        ImgsOf (descGens n I.1) (blockImgsOf n bl (descGens n I.1)) ϕ →
        Nat.card ϕ.range ≤ ellBound (Enc.size I.1.2.2.2)) :
    Round.Cost (impRound n solveW) :=
  impCostLine2 n solveW hsolve hsize (by
    intro I hI
    rcases ho : I.2 with _ | ⟨bl, idx⟩
    · exact Nat.zero_le _
    · obtain ⟨-, ⟨-, ϕ, hϕ⟩, -⟩ := hI.2 bl idx ho
      simp only [Option.elim]
      rw [impWidth_eq_card_range hI ho hϕ]
      exact hcard I hI bl idx ho ϕ hϕ)

end WidthCard

end Algo
