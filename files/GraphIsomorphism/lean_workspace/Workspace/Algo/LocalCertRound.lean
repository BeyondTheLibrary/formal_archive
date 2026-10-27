/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Recompute `H(W)` (§13.1, lines 04a–04h) as one computable
round.
-/
import Workspace.Algo.LocalCertAff
import Workspace.Algo.Imprimitive

/-!
# Procedure Recompute `H(W)` (§13.1) as one round

> 04a  `N ← H(W_old)^T_(T)`  (: the kernel of the `H(W_old) → S(T)` map :)
> 04b  `L ← ∅`
> 04c  for `σ̄ ∈ H(W_old)^T` do
> 04d    pick `σ ∈ H(W_old)` with `σ^{ψ_T} = σ̄`
> 04e    `L ← L ∪ Aut^{W_new}_{Nσ}(x)`  (: by strong Luks reduction over the orbits of `N`
>        in `W_new` :)
> 04h  `H(W_new) ← L`

Eq. (69) — `H(W_old) = ⋃_σ̄ Nσ` — is `Babai.eq_69`, and that the union of the window
automorphisms over those cosets is `H(W_new)` is `Babai.recompute_eq`.  So the shape of the
round is exactly the shape of Theorem 11.1.9 (`Algo.impRound`): **descend** to `N = ker ψ_T`
over the `|H(W_old)^T|` cosets, then run the **Chain Rule** over the orbits of `N` inside the
window.  The only difference is where the homomorphism comes from: there it is the action on
a block system, here it is `ψ_T`, handed to the routine as the images of the generators
(`Algo.ImgsOf`, the convention of Prop. 2.2.6).  The three routines of Prop. 2.2.6 (a) for an
action given that way are `Algo.actKerGens`, `Algo.actCosetRep` and `Algo.actCosetIndex`
(`Workspace/Algo/Extend.lean`), and they replace `Algo.blockKerGens`, `Algo.blockCosetRep`,
`Algo.blockCosetIndex` one for one.

## The raw instance

```
Algo.RawLCSI := RawWinSI × Option (RawTAct × ℕ)
Algo.RawTAct := List ℕ × RawGens
```

The window of the `RawWinSI` is `W_new` (the caller has already run line 03, which is
`Algo.rawAff` of `Workspace/Algo/LocalCertAff.lean`), its group is `H(W_old)` and its
representative is the coset representative carried along.  The option is the phase marker: in
the phase `some ((tdom, imgs), idx)` the round descends, `tdom` being a domain witness of the
test set `T` and `imgs` the images of the generators under `ψ_T`; `idx` is the number of
cosets, which is `|H(W_old)^T|` (`Algo.lcWidth_eq_card_range`) and hence at most `t!`
(`Algo.lcWidth_le_factorial`).  In the phase `none` the round is Luks's Chain Rule over the
orbits of `N` in `W_new`, line 04e.

## Main definitions

* `Algo.RawLCSI`, `Algo.LCWF` — the phase-marked instances and their well-formedness;
* `Algo.lcKer`, `Algo.lcRep` — `N = ker ψ_T` and the coset representatives of line 04d;
* `Algo.lcChild`, `Algo.lcRound` — the round;
* `Algo.lcRoundReduction` — the mathematical round it implements;
* `Algo.lcCost` — its cost data.

## Main results

* `Algo.cover_lcPerms` — Eq. (69): the candidate set is the union of the `|H(W_old)^T|` left
  cosets of `N`;
* `Algo.implements_lcRound` — **the link**: the raw round walks that tree;
* `Algo.run_lcRoundReduction` — the tree computes the answer of the instance;
* `Algo.lcWidth_le_factorial` — "`≤ t!` instances of string `N`-isomorphism";
* `Algo.lcCost` — every routine is a `RAM.PolyFun` and instances stay polynomially small.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The phase-marked instances -/

/-- The action of the current group on the test set `T`, on raw data: a domain witness of `T`
together with the images of the generators under `ψ_T`. -/
abbrev RawTAct := List ℕ × RawGens

/-- A raw instance of the Recompute round: an instance with a window (`Algo.RawWinSI`)
together with, in the descend phase, the action `ψ_T` on the test set and the number
`|H(W_old)^T|` of cosets of `N`.  `none` marks the Chain Rule phase (line 04e). -/
abbrev RawLCSI := RawWinSI × Option (RawTAct × ℕ)

/-- The instance a raw instance describes.  Paper: Definition 11.1.2. -/
noncomputable def decLCSI (n : ℕ) (I : RawLCSI) : Babai.SIInstance (Fin n) ℕ :=
  decWinSI n I.1

/-- The images of the generators under `ψ_T`, decoded. -/
noncomputable def lcImgs (td : RawTAct) : List (Perm (Fin td.1.length)) :=
  td.2.map (decPerm td.1.length)

/-- **Generators of `N = ker ψ_T`** (line 04a, through Prop. 2.2.6 (a)), shortened to at most
`n²` of them so that a child is a well-formed instance. -/
def lcKer (W : RawWinSI) (td : RawTAct) : RawGens :=
  tidyGens (W.2.2.2.1, actKerGens ((W.2.2.2.1, W.2.1), td))

/-- The `j`-th representative of a child (line 04d): the parent's representative times the
`j`-th coset representative of `N` in `H(W_old)`, read off the stabilizer chain of the graph
group, with the index `j` in binary. -/
def lcRep (W : RawWinSI) (td : RawTAct) (j : ℕ) : RawPerm :=
  rawMul (W.2.2.1, normPerm (W.2.2.2.1, actCosetRep (((W.2.2.2.1, W.2.1), td), j)))

/-- The representatives of the children, decoded: the `σ` of line 04d, one per `σ̄`. -/
noncomputable def lcPerms (n : ℕ) (W : RawWinSI) (q : RawTAct × ℕ) : List (Perm (Fin n)) :=
  (List.range q.2).map (fun j => decPerm n (lcRep W q.1 j))

@[simp] theorem length_lcPerms (n : ℕ) (W : RawWinSI) (q : RawTAct × ℕ) :
    (lcPerms n W q).length = q.2 := by simp [lcPerms]

theorem getElem_lcPerms (n : ℕ) (W : RawWinSI) (q : RawTAct × ℕ) {j : ℕ}
    (hj : j < (lcPerms n W q).length) :
    (lcPerms n W q)[j] = decPerm n (lcRep W q.1 j) := by
  simp only [lcPerms, List.getElem_map, List.getElem_range]

/-- **Well-formed raw instances.**  Besides `Algo.WinWF`, the test set is a domain witness of
at most `n` points, the images are well formed, the assignment `generator ↦ image` extends to
a homomorphism `ψ_T` (which is data about the input, not a runtime test: Prop. 2.2.6's
convention), and the stored index is the number of cosets the transversal produces. -/
def LCWF (n : ℕ) (I : RawLCSI) : Prop :=
  WinWF n I.1 ∧
    ∀ td idx, I.2 = some (td, idx) →
      (td.1.length ≤ n ∧ ∀ u ∈ td.1, u < n) ∧ RawGens.WF td.1.length td.2 ∧
        (∃ ψ : genGroup (descGens n I.1) →* Perm (Fin td.1.length),
          ImgsOf (descGens n I.1) (lcImgs td) ψ) ∧
        idx = actCosetIndex n td.1.length I.1.2.2.2.1 td.1 (descGens n I.1) (lcImgs td)

section Data

variable {I : RawLCSI} {td : RawTAct} {idx : ℕ}

/-- The generator list of the instance is the encoding of its decoding. -/
theorem lc_gens_eq (hI : LCWF n I) : I.1.2.1 = (descGens n I.1).map (encPerm n) :=
  (map_encPerm_decPerm hI.1.2.2.2.2.1).symm

/-- The image list of the action data is the encoding of its decoding. -/
theorem lc_imgs_eq (hwf : RawGens.WF td.1.length td.2) :
    td = ((td.1, (lcImgs td).map (encPerm td.1.length)) : RawTAct) := by
  refine Prod.ext rfl ?_
  exact (map_encPerm_decPerm hwf).symm

/-- **The subgroup descended to is `N = ker ψ_T`** (line 04a). -/
theorem decGroup_lcKer (hI : LCWF n I) (hs : I.2 = some (td, idx))
    {ψ : genGroup (descGens n I.1) →* Perm (Fin td.1.length)}
    (hψ : ImgsOf (descGens n I.1) (lcImgs td) ψ) :
    decGroup n (lcKer I.1 td) = actKer (descGens n I.1) ψ := by
  obtain ⟨-, hwf, -, -⟩ := hI.2 td idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  rw [lcKer, decGroup_tidyGens hx]
  show decGroup n (actKerGens ((I.1.2.2.2.1, I.1.2.1), td)) = _
  rw [lc_gens_eq hI]
  conv_lhs => rw [lc_imgs_eq hwf]
  exact decGroup_actKerGens hx rfl hψ

/-- `N ≤ H(W_old)`. -/
theorem lcKer_le (hI : LCWF n I) (hs : I.2 = some (td, idx)) :
    decGroup n (lcKer I.1 td) ≤ decGroup n I.1.2.1 := by
  obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI.2 td idx hs
  rw [decGroup_lcKer hI hs hψ]
  intro a ha
  exact actKer_le ψ ha

/-- The kernel generators are well formed and short. -/
theorem wf_lcKer (hI : LCWF n I) : RawGens.WF n (lcKer I.1 td) :=
  wf_tidyGens hI.1.1 _

theorem length_lcKer_le (hI : LCWF n I) : (lcKer I.1 td).length ≤ n * n :=
  length_tidyGens hI.1.1 _

/-- The `j`-th representative of a child is well formed. -/
theorem wf_lcRep (hI : LCWF n I) (j : ℕ) : RawPerm.WF n (lcRep I.1 td j) :=
  wf_rawMul hI.1.2.2.2.2.2.2.1 (wf_normPerm hI.1.1 _)

/-- The `j`-th representative, decoded. -/
theorem decPerm_lcRep (hI : LCWF n I) (j : ℕ) :
    decPerm n (lcRep I.1 td j)
      = decPerm n I.1.2.2.1 * decPerm n (actCosetRep (((I.1.2.2.2.1, I.1.2.1), td), j)) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hσ : RawPerm.WF n I.1.2.2.1 := hI.1.2.2.2.2.2.2.1
  rw [lcRep, rawMul_of_wf hσ (wf_normPerm hx _), decPerm_encPerm, decPerm_normPerm hx]

/-- **Eq. (69)**, as the routine computes it: the candidate set of the instance is the union
of the `|H(W_old)^T|` left cosets `σ·N` (`Babai.eq_69`, through Prop. 2.2.6 (a)). -/
theorem cover_lcPerms (hI : LCWF n I) (hs : I.2 = some (td, idx)) :
    (decLCSI n I).K = ⋃ σ ∈ lcPerms n I.1 (td, idx),
      σ • (decGroup n (lcKer I.1 td) : Set (Perm (Fin n))) := by
  obtain ⟨-, hwf, ⟨ψ, hψ⟩, hidx⟩ := hI.2 td idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hK : (decLCSI n I).K
      = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
    rw [decLCSI, decWinSI, decCoset_some]
  have hH : (decGroup n (lcKer I.1 td) : Set (Perm (Fin n)))
      = (actKer (descGens n I.1) ψ : Set (Perm (Fin n))) := by
    rw [decGroup_lcKer hI hs hψ]
  have hcov := cover_actCosetRep (dom := I.1.2.2.2.1) (gdom := td.1)
    (gens := descGens n I.1) (imgs := lcImgs td) hx rfl hψ
  have hlist : lcPerms n I.1 (td, idx)
      = (List.range idx).map (fun j => decPerm n I.1.2.2.1 *
          decPerm n (actCosetRep (((I.1.2.2.2.1,
            (descGens n I.1).map (encPerm n)), (td.1,
              (lcImgs td).map (encPerm td.1.length))), j))) := by
    rw [lcPerms]
    refine List.map_congr_left (fun j _ => ?_)
    rw [decPerm_lcRep hI j, ← lc_gens_eq hI]
    conv_lhs => rw [lc_imgs_eq hwf]
  rw [hK, hH, hlist, show (decGroup n I.1.2.1 : Set (Perm (Fin n)))
      = (genGroup (descGens n I.1) : Set (Perm (Fin n))) from rfl, hcov, ← hidx,
    smul_biUnion_index]

end Data

/-! ## The computable round -/

/-- Lift a child of the Chain Rule round to a child of this round: the same instance, with the
phase marker `none`. -/
def liftLC (o : Option RawWinSI) : Option RawLCSI :=
  o.elim none (fun J => some ((J, none) : RawLCSI))

/-- The `j`-th child: in the descend phase (lines 04c–04d) the instance whose group is `N` and
whose representative is the `j`-th lift `σ`, in the Chain Rule phase (line 04e) the child of
`Algo.chainRound`. -/
def lcChild (p : RawLCSI × ℕ × RawCoset) : Option RawLCSI :=
  p.1.2.elim (liftLC (winChild (p.1.1, p.2.1, p.2.2)))
    (fun q => if q.2 ≤ p.2.1 then none
      else some ((p.1.1.1, lcKer p.1.1 q.1, lcRep p.1.1 q.1 p.2.1,
        p.1.1.2.2.2.1, p.1.1.2.2.2.2), none))

/-- The fold step: the join of the answers in the descend phase (line 04e's `L ← L ∪ …`,
`Algo.rawCosetJoin`), the answer of the child in the Chain Rule phase. -/
def lcCombine (p : RawLCSI × ℕ × RawCoset × RawCoset) : RawCoset :=
  p.1.2.elim p.2.2.2 (fun _ => rawCosetJoin (p.1.1.2.2.2.1, p.2.2.1, p.2.2.2))

/-- The empty partial answer: the candidate set itself in the Chain Rule phase, the empty
coset `L ← ∅` of line 04b in the descend phase. -/
def lcInit (I : RawLCSI) : RawCoset :=
  I.2.elim (some (I.1.2.1, I.1.2.2.1)) (fun _ => none)

/-- The answer of the instance, read off the final state. -/
def lcFinish (solveW : RawWinSI → RawCoset) (p : RawLCSI × RawCoset) : RawCoset :=
  p.1.2.elim (if (winOrbits (p.1.1.2.1, p.1.1.1)).length ≤ 1 then solveW p.1.1 else p.2)
    (fun _ => p.2)

theorem lcChild_desc_eq_some {p : RawLCSI × ℕ × RawCoset} {J : RawLCSI}
    {td : RawTAct} {idx : ℕ}
    (hq : p.1.2 = some (td, idx)) (hc : lcChild p = some J) :
    p.2.1 < idx ∧ J = ((p.1.1.1, lcKer p.1.1 td, lcRep p.1.1 td p.2.1,
      p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [lcChild, hq] at hc
  simp only [Option.elim] at hc
  by_cases hj : idx ≤ p.2.1
  · rw [if_pos hj] at hc; exact absurd hc (by simp)
  · rw [if_neg hj] at hc
    exact ⟨by omega, (Option.some.inj hc).symm⟩

theorem lcChild_desc_eq_some_of {p : RawLCSI × ℕ × RawCoset}
    {td : RawTAct} {idx : ℕ}
    (hq : p.1.2 = some (td, idx)) (hj : p.2.1 < idx) :
    lcChild p = some ((p.1.1.1, lcKer p.1.1 td, lcRep p.1.1 td p.2.1,
      p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [lcChild, hq]
  simp only [Option.elim]
  rw [if_neg (by omega)]

theorem lcChild_chain {p : RawLCSI × ℕ × RawCoset} (hq : p.1.2 = none) :
    lcChild p = liftLC (winChild (p.1.1, p.2.1, p.2.2)) := by
  rw [lcChild, hq]
  rfl

theorem lcChild_chain_eq_some {p : RawLCSI × ℕ × RawCoset} {J : RawLCSI}
    (hq : p.1.2 = none) (hc : lcChild p = some J) :
    ∃ J', winChild (p.1.1, p.2.1, p.2.2) = some J' ∧ J = (J', none) := by
  rw [lcChild_chain hq, liftLC] at hc
  rcases hw : winChild (p.1.1, p.2.1, p.2.2) with _ | J'
  · rw [hw] at hc; exact absurd hc (by simp)
  · rw [hw] at hc
    exact ⟨J', rfl, (Option.some.inj hc).symm⟩

/-- **Procedure Recompute `H(W)`** (§13.1, lines 04a–04h) as one round.  `solveW` is the rest
of Procedure String-Isomorphism: it answers an instance whose group is transitive on the
window, where neither the descent of line 04d nor the Chain Rule of line 04e has anything
left to say. -/
def lcRound (n : ℕ) (solveW : RawWinSI → RawCoset) : Round RawLCSI RawCoset RawCoset where
  WF := LCWF n
  ground := fun I => Enc.size I.1.2.2.2
  measure := fun I => 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
  width := fun I => I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2)
  child := lcChild
  init := lcInit
  combine := lcCombine
  finish := lcFinish solveW
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
        show lcChild (I, j, s) = none
        rw [lcChild_chain (p := (I, j, s)) hq]
        show liftLC (winChild (I.1, j, s)) = none
        rw [hw, liftLC]
        rfl
    | some q =>
        have hj' : I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) ≤ j := hj
        rw [hq] at hj'
        simp only [Option.elim] at hj'
        show lcChild (I, j, s) = none
        rw [lcChild, hq]
        simp only [Option.elim]
        rw [if_pos hj']
  child_wf := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := lcChild_chain_eq_some (p := (I, j, s)) hq hc
        refine ⟨(chainRound n solveW).child_wf I.1 j s J' hI.1 hw, ?_⟩
        intro td idx hcon
        exact absurd hcon (by simp)
    | some q =>
        obtain ⟨td, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := lcChild_desc_eq_some (p := (I, j, s)) hq hc
        obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI.1
        refine ⟨⟨hx, hy, hnd, hlt, wf_lcKer hI, length_lcKer_le hI, wf_lcRep hI j, ?_⟩, ?_⟩
        · rw [rawIsInvariant_eq_true_iff (wf_lcKer (td := td) hI) hlt]
          exact isInvariant_of_le ((rawIsInvariant_eq_true_iff hgs hlt).1 hinv)
            (lcKer_le hI hq)
        · intro td' idx' hcon
          exact absurd hcon (by simp)
  child_measure := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := lcChild_chain_eq_some (p := (I, j, s)) hq hc
        have h : J'.1.length < I.1.1.length :=
          (chainRound n solveW).child_measure I.1 j s J' hI.1 hw
        show 2 * J'.1.length + Option.elim (none : Option (RawTAct × ℕ)) 0 (fun _ => 1)
          < 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
        rw [hq]
        simp only [Option.elim]
        omega
    | some q =>
        obtain ⟨td, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := lcChild_desc_eq_some (p := (I, j, s)) hq hc
        show 2 * I.1.1.length + Option.elim (none : Option (RawTAct × ℕ)) 0 (fun _ => 1)
          < 2 * I.1.1.length + I.2.elim 0 (fun _ => 1)
        rw [hq]
        simp
  child_ground := by
    rintro I j s J hI hc
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        obtain ⟨J', hw, rfl⟩ := lcChild_chain_eq_some (p := (I, j, s)) hq hc
        exact (chainRound n solveW).child_ground I.1 j s J' hI.1 hw
    | some q =>
        obtain ⟨td, idx⟩ := q
        obtain ⟨hjlt, rfl⟩ := lcChild_desc_eq_some (p := (I, j, s)) hq hc
        exact le_refl _

/-! ## The link to the mathematical layer -/

/-- The mathematical round the Recompute round implements: the union of Eq. (69) over the
`|H(W_old)^T|` coset representatives in the descend phase, and the Chain Rule over the orbits
of `N` in `W_new` (line 04e) in the Chain Rule phase. -/
noncomputable def lcRoundReduction (n : ℕ) (solveW : RawWinSI → RawCoset) (I : RawLCSI) :
    Babai.SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  I.2.elim (chainRoundReduction n solveW I.1) (fun q =>
    descentChain (decGroup n (lcKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
      (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∅ (lcPerms n I.1 q))

/-- **The fold of the descend phase walks the union of Eq. (69).** -/
theorem loopMatch_lcDesc (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawLCSI}
    (hI : LCWF n I) {q : RawTAct × ℕ} (hq : I.2 = some q) :
    ∀ (k j : ℕ), j + k = q.2 →
      ∀ (acc : Set (Perm (Fin n))) (s : RawCoset), decCoset n s = acc →
        LoopMatch (lcRound n solveW) (decLCSI n) (decCoset n) I k j s
          (descentChain (decGroup n (lcKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
            (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) acc
            ((lcPerms n I.1 q).drop j)) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  intro k
  induction k with
  | zero =>
      intro j hj acc s hs
      have hdrop : (lcPerms n I.1 q).drop j = [] := by
        apply List.drop_eq_nil_of_le
        rw [length_lcPerms]; omega
      rw [hdrop, descentChain]
      refine LoopMatch.done 0 j s acc ?_ ?_
      · exact (lcRound n solveW).child_eq_none I j s
          (by show I.2.elim _ (fun q => q.2) ≤ j; rw [hq]; simp only [Option.elim]; omega)
      · show decCoset n (lcFinish solveW (I, s)) = acc
        rw [lcFinish, hq]
        exact hs
  | succ k ih =>
      intro j hj acc s hs
      have hjl : j < (lcPerms n I.1 q).length := by rw [length_lcPerms]; omega
      have hdrop : (lcPerms n I.1 q).drop j
          = ((lcPerms n I.1 q)[j]'hjl) :: (lcPerms n I.1 q).drop (j + 1) :=
        List.drop_eq_getElem_cons hjl
      rw [hdrop, descentChain]
      have hjlt : j < q.2 := by rw [length_lcPerms] at hjl; omega
      set J : RawLCSI :=
        ((I.1.1, lcKer I.1 q.1, lcRep I.1 q.1 j, I.1.2.2.2.1, I.1.2.2.2.2), none) with hJ
      have hchild : (lcRound n solveW).child (I, j, s) = some J :=
        lcChild_desc_eq_some_of (p := (I, j, s)) hq hjlt
      have hdec : decLCSI n J
          = ⟨((lcPerms n I.1 q)[j]'hjl) • (decGroup n (lcKer I.1 q.1) : Set (Perm (Fin n))),
              winSet n I.1.1, decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
        rw [decLCSI, decWinSI, hJ]
        simp only
        rw [decCoset_some, getElem_lcPerms]
      rw [← hdec]
      refine LoopMatch.call k j s J _ hchild ?_
      intro a ha
      refine ih (j + 1) (by omega) (cosetHull (acc ∪ (decLCSI n J).answer))
        ((lcRound n solveW).combine (I, j, s, a)) ?_
      show decCoset n (lcCombine (I, j, s, a)) = _
      rw [lcCombine, hq]
      simp only [Option.elim]
      rw [decCoset_rawCosetJoin hx, hs, ha]

/-- **The fold of the Chain Rule phase walks the chain of line 04e.** -/
theorem loopMatch_lcChain (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawLCSI}
    (hI : LCWF n I) (hq : I.2 = none) (h2 : 1 < (winOrbits (I.1.2.1, I.1.1)).length) :
    ∀ (k j : ℕ), j + k = (winOrbits (I.1.2.1, I.1.1)).length →
      ∀ (C : Set (Perm (Fin n))) (s : RawCoset), StateOK n I.1 C s →
        LoopMatch (lcRound n solveW) (decLCSI n) (decCoset n) I k j s
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
      · exact (lcRound n solveW).child_eq_none I j s
          (by show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length _ ≤ j
              rw [hq]; simp only [Option.elim]; omega)
      · show decCoset n (lcFinish solveW (I, s)) = C
        rw [lcFinish, hq]
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
        · show lcChild (I, j, none) = none
          rw [lcChild_chain (p := (I, j, (none : RawCoset))) hq]
          show liftLC (winChild (I.1, j, (none : RawCoset))) = none
          rw [show winChild (I.1, j, (none : RawCoset)) = none from rfl, liftLC]
          rfl
        · show decCoset n (lcFinish solveW (I, (none : RawCoset))) = ∅
          rw [lcFinish, hq]
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
        have hchild : (lcRound n solveW).child (I, j, (some (g, τ) : RawCoset))
            = some ((J', none) : RawLCSI) := by
          show lcChild (I, j, (some (g, τ) : RawCoset)) = _
          rw [lcChild_chain (p := (I, j, (some (g, τ) : RawCoset))) hq]
          show liftLC (winChild (I.1, j, (some (g, τ) : RawCoset))) = _
          rw [hwchild, liftLC]
          rfl
        have hdec : decLCSI n ((J', none) : RawLCSI)
            = ⟨C, winSet n ((winOrbits (I.1.2.1, I.1.1))[j]'hjl),
                decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
          have hK : decCoset n (some (tidyGens (I.1.2.2.2.1, g),
              normPerm (I.1.2.2.2.1, τ))) = C := by
            rw [← hs.1, hsv]
            show {ρ | ∃ u ∈ decGroup n (tidyGens (I.1.2.2.2.1, g)),
              ρ = decPerm n (normPerm (I.1.2.2.2.1, τ)) * u} = _
            rw [htidy, decPerm_normPerm hx τ]
            rfl
          rw [decLCSI, decWinSI, hJ']
          simp only
          rw [hK, hgetd]
        rw [← hdec]
        refine LoopMatch.call k j (some (g, τ)) ((J', none) : RawLCSI) _ hchild ?_
        intro a ha
        have hans : (decLCSI n ((J', none) : RawLCSI)).answer
            = Babai.wIso (winSet n ((winOrbits (I.1.2.1, I.1.1))[j]'hjl)) C
                (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) := by
          rw [Babai.SIInstance.answer, hdec]
        have hsub : (decLCSI n ((J', none) : RawLCSI)).answer ⊆ C := by
          rw [hans]; exact fun ρ hρ => hρ.1
        have hcomb : (lcRound n solveW).combine (I, j, (some (g, τ) : RawCoset), a) = a := by
          show lcCombine (I, j, (some (g, τ) : RawCoset), a) = a
          rw [lcCombine, hq]
          rfl
        rw [hcomb]
        refine ih (j + 1) (by omega) ((decLCSI n ((J', none) : RawLCSI)).answer) a ?_
        refine ⟨ha, le_trans hsub hs.2.1, ?_⟩
        intro g₂ τ₂ ha2
        refine decGroup_le_of_subset (σ₀ := decPerm n I.1.2.2.1) (τ := decPerm n τ₂) ?_
        have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I.1).K := by
          rw [← ha2, ha]
          exact le_trans hsub hs.2.1
        exact h1

/-- **The link (§13.1, Procedure Recompute `H(W)`).**  The Recompute round implements the
union of Eq. (69) over the cosets of `N`, followed by the Chain Rule over the orbits of `N`
in `W_new`. -/
theorem implements_lcRound (n : ℕ) (solveW : RawWinSI → RawCoset) :
    Implements (lcRound n solveW) id (decLCSI n) (decCoset n) (lcRoundReduction n solveW) := by
  intro I hI
  show LoopMatch (lcRound n solveW) (decLCSI n) (decCoset n) I
    (I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2)) 0 (lcInit I)
    (lcRoundReduction n solveW I)
  rw [lcRoundReduction, lcInit]
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
          show lcChild (I, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset)) = none
          rw [lcChild_chain (p := (I, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset))) hq]
          show liftLC (winChild (I.1, 0, (some (I.1.2.1, I.1.2.2.1) : RawCoset))) = none
          rw [hw, liftLC]
          rfl
        · show decCoset n (lcFinish solveW (I, some (I.1.2.1, I.1.2.2.1)))
            = decCoset n (solveW I.1)
          rw [lcFinish, hq]
          simp only [Option.elim]
          rw [if_pos h2]
      · rw [if_neg h2]
        have h2' : 1 < (winOrbits (I.1.2.1, I.1.1)).length := by omega
        have := loopMatch_lcChain n solveW hI hq h2'
          (winOrbits (I.1.2.1, I.1.1)).length 0 (by omega)
          (decWinSI n I.1).K (some (I.1.2.1, I.1.2.2.1)) ⟨rfl, le_refl _, ?_⟩
        · simpa using this
        · intro g τ hgt
          have : g = I.1.2.1 := congrArg (fun z => (Option.getD z (I.1.2.1, I.1.2.2.1)).1) hgt.symm
          rw [this]
  | some q =>
      rw [hq]
      simp only [Option.elim]
      have := loopMatch_lcDesc n solveW hI hq q.2 0 (by omega) ∅ none rfl
      simpa using this

/-- **The mathematical round is correct**: its value is the answer of the instance, provided
`solveW` answers the instances the round hands on.

*Proof.*  In the descend phase, `Algo.cover_lcPerms` is Eq. (69) — the decomposition of
`H(W_old)` into the cosets of `N` — and Observation 11.1.11 says the answer of each
sub-instance is empty or a coset, so `Algo.run_descentChain` is the union of line 04e.  That
union is `H(W_new)` by `Babai.recompute_eq`.  In the Chain Rule phase it is
`Algo.run_chainRoundReduction`. -/
theorem run_lcRoundReduction (n : ℕ) (solveW : RawWinSI → RawCoset) {I : RawLCSI}
    (hI : LCWF n I)
    (hsolve : I.2 = none → (winOrbits (I.1.2.1, I.1.1)).length ≤ 1 →
      decCoset n (solveW I.1) = (decLCSI n I).answer) :
    (lcRoundReduction n solveW I).run = (decLCSI n I).answer := by
  rw [lcRoundReduction]
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
      refine run_descentChain _ _ _ _ _ _ (cover_lcPerms hI hq) ?_
      intro τ hτ
      refine ⟨Babai.wAutSubgroup (decGroup n I.1.2.1) (winSet n I.1.1) hinv
        (decStrN n I.1.2.2.2.1), ?_⟩
      have hK : (decLCSI n I).K
          = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
        rw [decLCSI, decWinSI, decCoset_some]
      have h := Babai.wIso_eq_smul_wAut (G := decGroup n I.1.2.1) (Δ := winSet n I.1.1) hinv
        (decPerm n I.1.2.2.1) (σ' := τ) (x := decStrN n I.1.2.2.2.1)
        (y := decStrN n I.1.2.2.2.2) (by rwa [← hK])
      rw [hK, h]
      rfl

/-! ## The running time -/

theorem polyFun_liftLC : PolyFun liftLC := by
  have hopt := PolyFun.optionElim (g := fun _ : Option RawWinSI => (none : Option RawLCSI))
    (h := fun z : RawWinSI × Option RawWinSI => some ((z.1, none) : RawLCSI))
    (polyFun_const (none : Option RawLCSI))
    ((polyFun_fst.pair (polyFun_const (none : Option (RawTAct × ℕ)))).comp polyFun_some)
  exact ((polyFun_id.pair polyFun_id).comp hopt).of_eq (fun _ => rfl)

theorem polyFun_lcKer : PolyFun (fun z : RawTAct × RawWinSI => lcKer z.2 z.1) := by
  have hx : PolyFun (fun z : RawTAct × RawWinSI => z.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : RawTAct × RawWinSI => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  exact ((hx.pair (((hx.pair hgens).pair polyFun_fst).comp polyFun_actKerGens)).comp
    polyFun_tidyGens).of_eq (fun _ => rfl)

theorem polyFun_lcRep :
    PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => lcRep z.2 z.1.1 z.1.2) := by
  have hx : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => z.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hrep : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have htd : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hj : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hcos : PolyFun (fun z : (RawTAct × ℕ) × RawWinSI =>
      actCosetRep (((z.2.2.2.2.1, z.2.2.1), z.1.1), z.1.2)) :=
    (((hx.pair hgens).pair htd).pair hj).comp polyFun_actCosetRep
  exact ((hrep.pair ((hx.pair hcos).comp polyFun_normPerm)).comp polyFun_rawMul).of_eq
    (fun _ => rfl)

theorem polyFun_lcChild : PolyFun lcChild := by
  classical
  have hΔ : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.2) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd
  have hW : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have htd : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hidx : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hj : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hker : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) => lcKer z.2.1 z.1.1) :=
    (htd.pair hW).comp polyFun_lcKer
  have hrep : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) =>
      lcRep z.2.1 z.1.1 z.2.2) :=
    ((htd.pair hj).pair hW).comp polyFun_lcRep
  have hcond : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) =>
      decide (z.1.2 ≤ z.2.2)) := (hidx.pair hj).comp polyFun_le
  have hsome : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) =>
      (some ((z.2.1.1, lcKer z.2.1 z.1.1, lcRep z.2.1 z.1.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none) : Option RawLCSI)) :=
    ((hΔ.pair (hker.pair (hrep.pair (hx.pair hy)))).pair
      (polyFun_const (none : Option (RawTAct × ℕ)))).comp polyFun_some
  have hbody : PolyFun (fun z : (RawTAct × ℕ) × (RawWinSI × ℕ) =>
      if z.1.2 ≤ z.2.2 then (none : Option RawLCSI)
      else some ((z.2.1.1, lcKer z.2.1 z.1.1, lcRep z.2.1 z.1.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none)) :=
    (PolyFun.ite hcond (polyFun_const (none : Option RawLCSI)) hsome).of_eq (fun z => by
      by_cases h : z.1.2 ≤ z.2.2 <;> simp [h])
  have hchain : PolyFun (fun p : RawLCSI × ℕ × RawCoset =>
      liftLC (winChild (p.1.1, p.2.1, p.2.2))) :=
    (((polyFun_fst.comp polyFun_fst).pair ((polyFun_snd.comp polyFun_fst).pair
      (polyFun_snd.comp polyFun_snd))).comp polyFun_winChild).comp polyFun_liftLC
  have hmid : PolyFun (fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset) =>
      ((z.1, (z.2.1.1, z.2.2.1)) : (RawTAct × ℕ) × (RawWinSI × ℕ))) :=
    polyFun_fst.pair (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))
  have hopt := PolyFun.optionElim
    (g := fun z : RawLCSI × ℕ × RawCoset => liftLC (winChild (z.1.1, z.2.1, z.2.2)))
    (h := fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset) =>
      if z.1.2 ≤ z.2.2.1 then (none : Option RawLCSI)
      else some ((z.2.1.1.1, lcKer z.2.1.1 z.1.1, lcRep z.2.1.1 z.1.1 z.2.2.1,
        z.2.1.1.2.2.2.1, z.2.1.1.2.2.2.2), none))
    hchain (hmid.comp hbody)
  have hin : PolyFun (fun p : RawLCSI × ℕ × RawCoset =>
      ((p.1.2, p) : Option (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  refine (hin.comp hopt).of_eq (fun p => ?_)
  rw [lcChild]

theorem polyFun_lcCombine : PolyFun lcCombine := by
  have hx : PolyFun (fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset × RawCoset) =>
      z.2.1.1.2.2.2.1) :=
    ((((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hs : PolyFun (fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset × RawCoset) =>
      z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset × RawCoset) =>
      z.2.2.2.2) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  have hopt := PolyFun.optionElim
    (g := fun z : RawLCSI × ℕ × RawCoset × RawCoset => z.2.2.2)
    (h := fun z : (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset × RawCoset) =>
      rawCosetJoin (z.2.1.1.2.2.2.1, z.2.2.2.1, z.2.2.2.2))
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)
    ((hx.pair (hs.pair ha)).comp polyFun_rawCosetJoin)
  have hin : PolyFun (fun p : RawLCSI × ℕ × RawCoset × RawCoset =>
      ((p.1.2, p) : Option (RawTAct × ℕ) × (RawLCSI × ℕ × RawCoset × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  exact (hin.comp hopt).of_eq (fun p => rfl)

theorem polyFun_lcInit : PolyFun lcInit := by
  have hopt := PolyFun.optionElim
    (g := fun I : RawLCSI => (some (I.1.2.1, I.1.2.2.1) : RawCoset))
    (h := fun z : (RawTAct × ℕ) × RawLCSI => (none : RawCoset))
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp polyFun_some)
    (polyFun_const (none : RawCoset))
  have hin : PolyFun (fun I : RawLCSI =>
      ((I.2, I) : Option (RawTAct × ℕ) × RawLCSI)) := polyFun_snd.pair polyFun_id
  exact (hin.comp hopt).of_eq (fun I => rfl)

/-! ## The cost of the round -/

/-- The size of the action data `(tdom, imgs)`: a domain witness of at most `m` points below
`m`, and at most `m²` permutations of it. -/
def tactBound (m : ℕ) : ℕ := 2 * strBound m + 2 * gensBound m

/-- The size of the descend-phase data: the action on the test set, and the number of cosets,
a natural of at most `4m² + 1` bits. -/
def lcDataBound (m : ℕ) : ℕ := 2 + 2 * tactBound m + 2 * (4 * (m * m) + 3)

/-- **The size bound of the Recompute round.** -/
def lcBound (m : ℕ) : ℕ := 2 * chainBound m + 2 * lcDataBound m

theorem chainBound_le_lcBound (m : ℕ) : chainBound m ≤ lcBound m := by
  have h1 : lcBound m = 2 * chainBound m + 2 * lcDataBound m := rfl
  omega

theorem four_le_lcBound (m : ℕ) : 4 ≤ lcBound m := by
  have h1 : lcBound m = 2 * chainBound m + 2 * lcDataBound m := rfl
  have h2 : lcDataBound m = 2 + 2 * tactBound m + 2 * (4 * (m * m) + 3) := rfl
  omega

theorem polyBound_tactBound : PolyBound tactBound := by
  have hS : PolyBound strBound :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1)))
  have hG : PolyBound gensBound :=
    (polyBound_const 1).add ((polyBound_id.mul polyBound_id).mul
      (((polyBound_const 2).mul hS).add (polyBound_const 1)))
  exact ((polyBound_const 2).mul hS).add ((polyBound_const 2).mul hG)

theorem polyBound_lcDataBound : PolyBound lcDataBound :=
  ((polyBound_const 2).add ((polyBound_const 2).mul polyBound_tactBound)).add
    ((polyBound_const 2).mul
      (((polyBound_const 4).mul (polyBound_id.mul polyBound_id)).add (polyBound_const 3)))

theorem polyBound_lcBound : PolyBound lcBound :=
  ((polyBound_const 2).mul polyBound_chainBound).add
    ((polyBound_const 2).mul polyBound_lcDataBound)

theorem mono_tactBound : Monotone tactBound := by
  intro a b hab
  have h1 : strBound a ≤ strBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul hab (by omega)) 1
  have h2 : gensBound a ≤ gensBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul hab hab) (by omega)) 1
  have h3 : tactBound a = 2 * strBound a + 2 * gensBound a := rfl
  have h4 : tactBound b = 2 * strBound b + 2 * gensBound b := rfl
  omega

theorem mono_lcDataBound : Monotone lcDataBound := by
  intro a b hab
  have h1 : tactBound a ≤ tactBound b := mono_tactBound hab
  have h2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
  have h3 : lcDataBound a = 2 + 2 * tactBound a + 2 * (4 * (a * a) + 3) := rfl
  have h4 : lcDataBound b = 2 + 2 * tactBound b + 2 * (4 * (b * b) + 3) := rfl
  omega

theorem mono_lcBound : Monotone lcBound := by
  intro a b hab
  have h1 : chainBound a ≤ chainBound b := mono_chainBound hab
  have h2 : lcDataBound a ≤ lcDataBound b := mono_lcDataBound hab
  have h3 : lcBound a = 2 * chainBound a + 2 * lcDataBound a := rfl
  have h4 : lcBound b = 2 * chainBound b + 2 * lcDataBound b := rfl
  omega

/-- The domain size is at most the size of the strings, which is the ground size. -/
theorem lc_le_ground {I : RawLCSI} (hI : LCWF n I) : n ≤ Enc.size I.1.2.2.2 :=
  le_size_strings hI.1

/-- **The action data is polynomially small.**  The number of images is the number of
generators, at most `n²`; each image is a permutation of the `t ≤ n` points of the test set;
and the number of cosets is below `(n + t)^(n + t)` (`Algo.size_winCosetIndex_le`). -/
theorem size_lcData_le {I : RawLCSI} (hI : LCWF n I) :
    Enc.size I.2 ≤ lcDataBound (Enc.size I.1.2.2.2) := by
  set m := Enc.size I.1.2.2.2 with hm
  have hnm : n ≤ m := lc_le_ground hI
  have hbd : lcDataBound m = 2 + 2 * tactBound m + 2 * (4 * (m * m) + 3) := rfl
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [ho]
      have h1 : Enc.size (none : Option (RawTAct × ℕ)) = 2 := size_none
      omega
  | some q =>
      obtain ⟨⟨htl, htlt⟩, hwf, ⟨ψ, hψ⟩, hidx⟩ := hI.2 q.1 q.2 ho
      rw [ho]
      have h0 : Enc.size (some q) = Enc.size q + 2 := size_some_eq _
      have h1 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := size_pair_le' q
      -- the action data
      have hdom : Enc.size q.1.1 ≤ strBound m :=
        size_natList_le (le_trans htl hnm) (fun a ha => lt_of_lt_of_le (htlt a ha) hnm)
      have hlenimgs : q.1.2.length ≤ n * n := by
        have h1' : (descGens n I.1).length = (lcImgs q.1).length := hψ.1
        have h2' : (lcImgs q.1).length = q.1.2.length := by simp [lcImgs]
        have h3' : (descGens n I.1).length = I.1.2.1.length := by simp [descGens]
        have h4' : I.1.2.1.length ≤ n * n := hI.1.2.2.2.2.2.1
        omega
      have himgs : Enc.size q.1.2 ≤ gensBound m := by
        have hentry : ∀ g ∈ q.1.2, Enc.size g ≤ strBound m := by
          intro g hg
          exact size_natList_le (by rw [(hwf g hg).length]; omega)
            (fun a ha => lt_of_lt_of_le ((hwf g hg).lt ha) (by omega))
        have e1 := size_list_le_of_entries q.1.2 (strBound m) hentry
        have e2 : q.1.2.length * (2 * strBound m + 1) ≤ m * m * (2 * strBound m + 1) :=
          Nat.mul_le_mul_right _ (le_trans hlenimgs (Nat.mul_le_mul hnm hnm))
        have e3 : gensBound m = 1 + m * m * (2 * strBound m + 1) := rfl
        omega
      have h2 : Enc.size q.1 ≤ tactBound m := by
        have := size_pair_le' q.1
        have h4 : tactBound m = 2 * strBound m + 2 * gensBound m := rfl
        omega
      have h3 : Enc.size q.2 ≤ 4 * (m * m) + 3 := by
        have e1 : Enc.size q.2 = Nat.size q.2 + 2 := Small.size_nat q.2
        have e2 : Nat.size q.2 ≤ (n + q.1.1.length) * (n + q.1.1.length) + 1 := by
          rw [hidx, actCosetIndex]
          exact size_winCosetIndex_le (nodup_extWin n q.1.1.length)
            (fun x hx => lt_extWin hx) _
        have e4 : (n + q.1.1.length) * (n + q.1.1.length) ≤ (2 * m) * (2 * m) :=
          Nat.mul_le_mul (by omega) (by omega)
        have e5 : (2 * m) * (2 * m) = 4 * (m * m) := by ring
        omega
      omega

/-- **A well-formed instance is small.** -/
theorem size_lcSI_le {I : RawLCSI} (hI : LCWF n I) :
    Enc.size I ≤ lcBound (Enc.size I.1.2.2.2) := by
  have h1 : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := size_pair_le' I
  have h2 : Enc.size I.1 ≤ chainBound (Enc.size I.1.2.2.2) := size_winSI_le hI.1
  have h3 : Enc.size I.2 ≤ lcDataBound (Enc.size I.1.2.2.2) := size_lcData_le hI
  have h4 : lcBound (Enc.size I.1.2.2.2)
      = 2 * chainBound (Enc.size I.1.2.2.2) + 2 * lcDataBound (Enc.size I.1.2.2.2) := rfl
  omega

/-- **The cost data of the Recompute round.**  `solveW` is charged for, as in
`Algo.chainCost`.  The width bound `wb` of the descend phase comes from the caller: §13.1
says the multiplicative cost of line 04c is `|H(W_old)^T| ≤ t!`
(`Algo.lcWidth_le_factorial`), and it is the choice of the test set — `t = O(log n)` — that
makes `t!` quasipolynomial.  The Chain Rule phase of line 04e has at most as many children as
the window has points, which is at most the ground size. -/
def lcCost (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (wb : ℕ → ℕ) (hwb : QuasiPolyBound wb)
    (hwidth : ∀ I, LCWF n I → I.2.elim 0 (fun q => q.2) ≤ wb (Enc.size I.1.2.2.2)) :
    Round.Cost (lcRound n solveW) where
  bound := lcBound
  polyBound_bound := polyBound_lcBound
  mono_bound := mono_lcBound
  widthBound := fun m => wb m + m
  quasiPolyBound_widthBound := hwb.add polyBound_id.quasiPoly
  quasiPolyFun_child := polyFun_lcChild.quasiPolyFun
  quasiPolyFun_init := polyFun_lcInit.quasiPolyFun
  quasiPolyFun_combine := polyFun_lcCombine.quasiPolyFun
  quasiPolyFun_finish := by
    have horbW : PolyFun (fun z : RawLCSI × RawCoset =>
        decide ((winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1)) := by
      have h1 : PolyFun (fun z : RawLCSI × RawCoset =>
          winOrbits (z.1.1.2.1, z.1.1.1)) :=
        (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
          ((polyFun_fst.comp polyFun_fst).comp polyFun_fst))).comp polyFun_winOrbits
      exact ((h1.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
    have hg : QuasiPolyFun (fun z : RawLCSI × RawCoset =>
        if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then solveW z.1.1 else z.2) :=
      (QuasiPolyFun.ite horbW ((polyFun_fst.comp polyFun_fst).comp_quasi hsolve)
        polyFun_snd.quasiPolyFun).of_eq (fun z => by
          by_cases h : (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 <;> simp [h])
    have hopt := QuasiPolyFun.optionElim
      (g := fun z : RawLCSI × RawCoset =>
        if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then solveW z.1.1 else z.2)
      (h := fun z : (RawTAct × ℕ) × (RawLCSI × RawCoset) => z.2.2)
      hg ((polyFun_snd.comp polyFun_snd).quasiPolyFun)
    have hin : PolyFun (fun p : RawLCSI × RawCoset =>
        ((p.1.2, p) : Option (RawTAct × ℕ) × (RawLCSI × RawCoset))) :=
      (polyFun_fst.comp polyFun_snd).pair polyFun_id
    exact (hin.comp_quasi hopt).of_eq (fun p => rfl)
  ground_le := by
    intro I
    show Enc.size I.1.2.2.2 ≤ Enc.size I
    have h1 : Enc.size I.1.2.2.2 ≤ Enc.size I.1 :=
      le_trans (size_snd_le' I.1.2.2) (le_trans (size_snd_le' I.1.2) (size_snd_le' I.1))
    have h2 : Enc.size I.1 ≤ Enc.size I := size_fst_le' I
    omega
  size_le := fun I hI => size_lcSI_le hI
  init_le := by
    intro I hI
    show Enc.size (lcInit I) ≤ lcBound (Enc.size I.1.2.2.2)
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    have hcb := chainBound_le_lcBound (Enc.size I.1.2.2.2)
    cases o with
    | none =>
        have h0 : lcInit I = some (I.1.2.1, I.1.2.2.1) := by rw [lcInit, ho]; rfl
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
        have h0 : lcInit I = none := by rw [lcInit, ho]; rfl
        have h1 : Enc.size (none : RawCoset) = 2 := size_none
        have h2 := four_le_lcBound (Enc.size I.1.2.2.2)
        rw [h0]
        omega
  combine_le := by
    intro I j s a hI hs ha
    show Enc.size (lcCombine (I, j, s, a)) ≤ lcBound (Enc.size I.1.2.2.2)
    rw [lcCombine]
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none => rw [ho]; exact ha
    | some q =>
        rw [ho]
        simp only [Option.elim]
        exact size_rawCosetJoin_le (n := n) hI.1.1 (lc_le_ground hI)
          (chainBound_le_lcBound _) hs ha
  finish_le := by
    intro I s hI hs
    show Enc.size (lcFinish solveW (I, s)) ≤ lcBound (Enc.size I.1.2.2.2)
    rw [lcFinish]
    obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none =>
        rw [ho]
        simp only [Option.elim]
        by_cases h : (winOrbits (I.1.2.1, I.1.1)).length ≤ 1
        · rw [if_pos h]
          exact le_trans (hsize I.1 hI.1) (chainBound_le_lcBound _)
        · rw [if_neg h]; exact hs
    | some q => rw [ho]; exact hs
  bot_le := by
    intro m
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := four_le_lcBound m
    show Enc.size (none : RawCoset) ≤ lcBound m
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
        have h3 : n ≤ Enc.size I.1.2.2.2 := lc_le_ground hI
        omega
    | some q =>
        have h := hwidth I hI
        rw [ho] at h ⊢
        simp only [Option.elim] at h ⊢
        omega

/-! ## "`≤ t!` instances of string `N`-isomorphism" (§13.1)

> We have reduced this to `≤ t!` instances of string `N`-isomorphism on the window `W_new`.

The number of children of the descend phase is the number of cosets the transversal produces,
which is `|H(W_old) : N| = |H(W_old)^{ψ_T}|` (`Algo.actCosetIndex_eq_card_range`, risk
R-A7-3), and that is a subgroup of `S(T)`, so it has at most `t!` elements.  This is the raw
counterpart of `Babai.card_imgOn_le_factorial`. -/

section Width

variable {I : RawLCSI} {td : RawTAct} {idx : ℕ}

/-- **The stored width of a descend instance is `|H(W_old)^{ψ_T}|`.** -/
theorem lcWidth_eq_card_range (hI : LCWF n I) (hs : I.2 = some (td, idx))
    {ψ : genGroup (descGens n I.1) →* Perm (Fin td.1.length)}
    (hψ : ImgsOf (descGens n I.1) (lcImgs td) ψ) :
    idx = Nat.card ψ.range := by
  obtain ⟨-, -, -, hidx⟩ := hI.2 td idx hs
  rw [hidx]
  exact actCosetIndex_eq_card_range hI.1.1 rfl hψ

/-- **§13.1: at most `t!` instances.**  The descend phase of Procedure Recompute `H(W)` has
at most `t!` children, `t` being the size of the test set. -/
theorem lcWidth_le_factorial (hI : LCWF n I) (hs : I.2 = some (td, idx))
    {ψ : genGroup (descGens n I.1) →* Perm (Fin td.1.length)}
    (hψ : ImgsOf (descGens n I.1) (lcImgs td) ψ) :
    idx ≤ Nat.factorial td.1.length := by
  rw [lcWidth_eq_card_range hI hs hψ]
  have h1 : Nat.card ψ.range ≤ Nat.card (Perm (Fin td.1.length)) :=
    Nat.card_le_card_of_injective (fun g => (g : Perm (Fin td.1.length)))
      Subtype.val_injective
  have h2 : Nat.card (Perm (Fin td.1.length)) = Nat.factorial td.1.length := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rwa [h2] at h1

end Width

/-- **The cost data from the size of the test set.**  A caller who knows that the test sets
it uses have at most `ℓ(n)` points — in §15 that is `ℓ = (log₂ n)³`, and `ℓ!` is
quasipolynomial (`Algo.quasiPolyBound_ellBound`) — gets the `Algo.Round.Cost` of the Recompute
round with no further hypothesis on the width, because the descend phase has at most `t!`
children (`Algo.lcWidth_le_factorial`). -/
def lcCostOfTestSize (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (ℓ : ℕ → ℕ) (hℓ : QuasiPolyBound (fun m => Nat.factorial (ℓ m)))
    (ht : ∀ I : RawLCSI, LCWF n I → ∀ (td : RawTAct) (idx : ℕ), I.2 = some (td, idx) →
      td.1.length ≤ ℓ (Enc.size I.1.2.2.2)) :
    Round.Cost (lcRound n solveW) :=
  lcCost n solveW hsolve hsize (fun m => Nat.factorial (ℓ m)) hℓ (by
    intro I hI
    rcases ho : I.2 with _ | ⟨td, idx⟩
    · exact Nat.zero_le _
    · obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI.2 td idx ho
      simp only [Option.elim]
      exact le_trans (lcWidth_le_factorial hI ho hψ)
        (Nat.factorial_le (ht I hI td idx ho)))

/-- **The cost data at a test set of size `(log₂ n)³`**, the choice of §15: `ℓ!` is
quasipolynomial (`Algo.quasiPolyBound_ellBound`). -/
def lcCostLine2 (n : ℕ) (solveW : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solveW)
    (hsize : ∀ W, WinWF n W → Enc.size (solveW W) ≤ chainBound (Enc.size W.2.2.2))
    (ht : ∀ I : RawLCSI, LCWF n I → ∀ (td : RawTAct) (idx : ℕ), I.2 = some (td, idx) →
      td.1.length ≤ Nat.log 2 (Enc.size I.1.2.2.2) ^ 3) :
    Round.Cost (lcRound n solveW) :=
  lcCostOfTestSize n solveW hsolve hsize (fun m => Nat.log 2 m ^ 3)
    quasiPolyBound_ellBound ht

end Algo
