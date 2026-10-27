/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the naming of the test set `T` of §13.1, and the transport of
`ψ_T : H → S(T)` to `H → S(Fin t)`.
-/
import Workspace.Algo.LocalCertOut
import Workspace.LocalCertificates.Calls

/-!
# Naming the test set (§13.1)

A test set of the paper is a subset `T ⊆ Γ`; §13.1 speaks of `S(T)`, `A(T)`, `H(W)^T` and
`ψ_T : G_T → S(T)`, all indexed by the *points* of `T`.  A test set on the machine is a
repetition-free list `tdom` of points of `Γ = Fin m`, and every raw statement of `Algo/`
speaks of `Perm (Fin t)` with `t = tdom.length`.  This file builds the identification once
and carries `ψ_T` across it, so that the raw side of §13.1 can be compared with
`Workspace/LocalCertificates/` literally.

The identification is not new: it is the labelling of a window, `Algo.winEquiv`
(`Workspace/Algo/Restrict.lean`), which sends the label `k` to the point `tdom[k]`.  Read as
the naming of a test set it is `Algo.tName`.

## Main definitions

* `Algo.tName` — `Fin t ≃ ↥T`, the naming of the test set;
* `Algo.psiFin` — `ψ_T` in test-set labels, `H →* Perm (Fin t)`;
* `Algo.tActImgs`, `Algo.rawTAct` — the `Algo.RawTAct` a stage of the while loop carries.

## Main results

* `Algo.ncard_winSet` — `|T| = t`, so the paper's `t!` and the raw `t!` are the same number;
* `Algo.psiFin_val` — what `ψ_T` computes, on raw data: the label of `σ^{ψ_T}(k)` names the
  point `ϕ(σ)(tdom[k])`;
* `Algo.range_psiFin`, `Algo.alternating_le_range_psiFin_iff` — `H^T` and the test
  `H^T ≥ A(T)` of lines 02 and 07 cross the naming;
* `Algo.affectedIn_psiFin` — Definition 13.1.4 crosses the naming;
* `Algo.imgsOf_lcImgs_rawTAct` — **the raw action data of a stage decodes to `ψ_T`**;
* `Algo.rawIsFullT_iff_isFull` — line 07 decides the paper's `H(W)^T ≥ A(T)`;
* `Algo.run_lcRoundReduction_eq_recomputeReduction` — **the link**: the Recompute round of
  `Algo/LocalCertRound.lean` and `Babai.recomputeReduction` have the same value, `H(W_new)`;
* `Algo.lcWidth_le_factorial_ncard` — and the same width bound, `t!` with `t = |T|`.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Classical

variable {n m : ℕ} {G H : Subgroup (Perm (Fin n))}

/-! ## The naming of the test set -/

/-- **The naming of the test set** (§13.1).  A test set is handed to the machine as a
repetition-free list `tdom` of points of `Γ = Fin m`; its `k`-th entry is the point named by
the label `k`.  This is the labelling of a window (`Algo.winEquiv`), read as the naming of a
test set. -/
noncomputable abbrev tName (m : ℕ) (tdom : List ℕ) (hnd : tdom.Nodup)
    (hlt : ∀ u ∈ tdom, u < m) : Fin tdom.length ≃ ↥(winSet m tdom) :=
  winEquiv m tdom hnd hlt

/-- **`|T| = t`**: the paper's `t = |T|` and the machine's `t = tdom.length` are the same
number, so the two readings of the bound `t!` agree. -/
theorem ncard_winSet (tdom : List ℕ) (hnd : tdom.Nodup) (hlt : ∀ u ∈ tdom, u < m) :
    (winSet m tdom).ncard = tdom.length := by
  have h : Nat.card (Fin tdom.length) = Nat.card ↥(winSet m tdom) :=
    Nat.card_congr (tName m tdom hnd hlt)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at h
  exact h.symm

/-! ## `ψ_T` in test-set labels -/

/-- **`ψ_T` in test-set labels** (Notation 13.1.1).  The paper's `ψ_T : G_T → S(T)`
restricted to `H ≤ G_T` is `Babai.psiOn`; carried along the naming of the test set it is a
homomorphism into `S(Fin t)`, which is what the routines of `Algo/` speak of. -/
noncomputable def psiFin (ϕ : G →* Perm (Fin m)) (tdom : List ℕ) (hnd : tdom.Nodup)
    (hlt : ∀ u ∈ tdom, u < m) (hH : H ≤ Babai.bigGT ϕ (winSet m tdom)) :
    H →* Perm (Fin tdom.length) :=
  ((tName m tdom hnd hlt).symm.permCongrHom :
      Perm ↥(winSet m tdom) ≃* Perm (Fin tdom.length)).toMonoidHom.comp
    (Babai.psiOn ϕ (winSet m tdom) hH)

section Psi

variable {ϕ : G →* Perm (Fin m)} {tdom : List ℕ} {hnd : tdom.Nodup}
  {hlt : ∀ u ∈ tdom, u < m} {hH : H ≤ Babai.bigGT ϕ (winSet m tdom)}

theorem psiFin_apply (g : H) (k : Fin tdom.length) :
    psiFin ϕ tdom hnd hlt hH g k
      = (tName m tdom hnd hlt).symm
          (Babai.psiOn ϕ (winSet m tdom) hH g (tName m tdom hnd hlt k)) := by
  show ((tName m tdom hnd hlt).symm.permCongr
      (Babai.psiOn ϕ (winSet m tdom) hH g)) k = _
  rw [Equiv.permCongr_apply, Equiv.symm_symm]

/-- **What `ψ_T` computes**, in the vocabulary of the raw data: the point named by the label
`σ^{ψ_T}(k)` is the image under `ϕ(σ)` of the point named by `k`.  This is the equation a
routine has to satisfy to hold the images of the generators. -/
theorem psiFin_val (g : H) {k : ℕ} (hk : k < tdom.length) :
    tdom.getD ((psiFin ϕ tdom hnd hlt hH g ⟨k, hk⟩ : Fin tdom.length) : ℕ) 0
      = ((ϕ ⟨(g : Perm (Fin n)), Babai.stabIn_le_top (hH g.2)⟩ : Perm (Fin m))
          ⟨tdom[k], hlt _ (List.getElem_mem hk)⟩ : ℕ) := by
  rw [psiFin_apply, winEquiv_symm_val]
  have h1 : ((Babai.psiOn ϕ (winSet m tdom) hH g (tName m tdom hnd hlt ⟨k, hk⟩) :
        ↥(winSet m tdom)) : Fin m)
      = (ϕ ⟨(g : Perm (Fin n)), Babai.stabIn_le_top (hH g.2)⟩ : Perm (Fin m))
          ((tName m tdom hnd hlt ⟨k, hk⟩ : ↥(winSet m tdom)) : Fin m) :=
    Babai.psi_apply_coe ϕ (winSet m tdom) _ _
  rw [h1, winEquiv_coe tdom hnd hlt hk]

/-- **`H^T` crosses the naming**: the image of `ψ_T` in test-set labels is the paper's
`H^T = H^{ψ_T}` (`Babai.imgOn`), carried along `Algo.tName`. -/
theorem range_psiFin :
    (psiFin ϕ tdom hnd hlt hH).range
      = (Babai.imgOn ϕ (winSet m tdom) hH).map
          ((tName m tdom hnd hlt).symm.permCongrHom :
            Perm ↥(winSet m tdom) ≃* Perm (Fin tdom.length)).toMonoidHom := by
  rw [psiFin, MonoidHom.range_comp, Babai.imgOn_eq_range]

/-- **The test of lines 02 and 07 crosses the naming**: `A(Fin t) ≤ H^{ψ_T}` in test-set
labels says exactly `A(T) ≤ H^T`. -/
theorem alternating_le_range_psiFin_iff :
    alternatingGroup (Fin tdom.length) ≤ (psiFin ϕ tdom hnd hlt hH).range
      ↔ alternatingGroup ↥(winSet m tdom) ≤ Babai.imgOn ϕ (winSet m tdom) hH := by
  rw [range_psiFin]
  exact Babai.alternating_le_map_permCongrHom_iff _ _

/-- **Definition 13.1.4 crosses the naming**: a point is affected by `ψ_T` in test-set
labels exactly when it is affected by `ψ_T` in the paper's sense. -/
theorem affectedIn_psiFin (u : Fin n) :
    Babai.AffectedIn (psiFin ϕ tdom hnd hlt hH) u
      ↔ Babai.AffectedIn (Babai.psiOn ϕ (winSet m tdom) hH) u := by
  show ¬ _ ≤ _ ↔ ¬ _ ≤ _
  rw [psiFin, ← Subgroup.map_map]
  exact not_congr (Babai.alternating_le_map_permCongrHom_iff _ _)

/-- **`ψ_T` as a total function on `S(Ω)`**, with junk outside `H`.  A routine stores one
image per generator, so what it applies is a function of a permutation, not of an element of
the subgroup; the junk value is never read, because `Algo.psiFinOf_of_mem` is applied only to
generators. -/
noncomputable def psiFinOf (ϕ : G →* Perm (Fin m)) (tdom : List ℕ) (hnd : tdom.Nodup)
    (hlt : ∀ u ∈ tdom, u < m) (hH : H ≤ Babai.bigGT ϕ (winSet m tdom))
    (g : Perm (Fin n)) : Perm (Fin tdom.length) :=
  if h : g ∈ H then psiFin ϕ tdom hnd hlt hH ⟨g, h⟩ else 1

theorem psiFinOf_of_mem {g : Perm (Fin n)} (h : g ∈ H) :
    psiFinOf ϕ tdom hnd hlt hH g = psiFin ϕ tdom hnd hlt hH ⟨g, h⟩ := dif_pos h

end Psi

/-! ## The raw action data of a stage -/

section Data

variable {ϕ : G →* Perm (Fin m)} {tdom : List ℕ} (hnd : tdom.Nodup)
  (hlt : ∀ u ∈ tdom, u < m) (gens : List (Perm (Fin n)))
  (hgen : genGroup gens ≤ Babai.bigGT ϕ (winSet m tdom))

/-- **The images of a generator list under `ψ_T`**, in test-set labels: the `imgs`
component of the `Algo.RawTAct` that a stage of the while loop carries. -/
noncomputable def tActImgs : List (Perm (Fin tdom.length)) :=
  gens.map (psiFinOf ϕ tdom hnd hlt hgen)

/-- **The action data really are the images of the generators** (`Algo.ImgsOf`, the
convention of Prop. 2.2.6). -/
theorem imgsOf_tActImgs :
    ImgsOf gens (tActImgs hnd hlt gens hgen) (psiFin ϕ tdom hnd hlt hgen) := by
  refine ⟨by simp [tActImgs], ?_⟩
  intro i hi hi'
  show (gens.map (psiFinOf ϕ tdom hnd hlt hgen))[i]'hi' = _
  rw [List.getElem_map]
  exact psiFinOf_of_mem (Subgroup.subset_closure (List.getElem_mem hi))

/-- **The `Algo.RawTAct` of a stage**: the domain witness of the test set together with the
encoded images of the generators of `H(W)` under `ψ_T`. -/
noncomputable def rawTAct : RawTAct :=
  (tdom, (tActImgs hnd hlt gens hgen).map (encPerm tdom.length))

@[simp] theorem rawTAct_fst : (rawTAct hnd hlt gens hgen (ϕ := ϕ)).1 = tdom := rfl

theorem lcImgs_rawTAct :
    lcImgs (rawTAct hnd hlt gens hgen (ϕ := ϕ)) = tActImgs hnd hlt gens hgen := by
  show ((tActImgs hnd hlt gens hgen).map (encPerm tdom.length)).map
      (decPerm tdom.length) = _
  rw [List.map_map]
  refine Eq.trans (List.map_congr_left ?_) (List.map_id _)
  intro a _
  exact decPerm_encPerm tdom.length a

theorem wf_rawTAct : RawGens.WF tdom.length (rawTAct hnd hlt gens hgen (ϕ := ϕ)).2 :=
  wf_map_encPerm tdom.length _

/-- **The raw action data of a stage decodes to `ψ_T`** — session 2's open point 2 (ii).
This is the hypothesis `Algo.LCWF` demands of the descend phase of the Recompute round, and
the hypothesis `Algo.rawIsFullT_eq_true_iff` and `Algo.decGroup_rawCertM` demand of the
certificates: what the routine holds is `ψ_T` and nothing else. -/
theorem imgsOf_lcImgs_rawTAct :
    ImgsOf gens (lcImgs (rawTAct hnd hlt gens hgen (ϕ := ϕ)))
      (psiFin ϕ tdom hnd hlt hgen) := by
  rw [lcImgs_rawTAct]
  exact imgsOf_tActImgs hnd hlt gens hgen

/-- **Line 07 decides the paper's test** (Definition 13.1.2): applied to the action data of
a stage, `Algo.rawIsFullT` says exactly `H(W)^T ≥ A(T)`. -/
theorem rawIsFullT_iff_isFull :
    rawIsFullT (rawTAct hnd hlt gens hgen (ϕ := ϕ)) = true
      ↔ alternatingGroup ↥(winSet m tdom) ≤ Babai.imgOn ϕ (winSet m tdom) hgen := by
  rw [rawIsFullT_eq_true_iff (wf_rawTAct hnd hlt gens hgen)
      (imgsOf_lcImgs_rawTAct hnd hlt gens hgen)]
  exact alternating_le_range_psiFin_iff

/-- **Line 10 returns `M(T) = H(W)^T`**, read in the paper's `S(T)`: the stored image list
generates the image of `ψ_T`, which is `Babai.imgOn` carried along the naming. -/
theorem decGroup_rawCertM_imgOn :
    decGroup tdom.length (rawCertM (rawTAct hnd hlt gens hgen (ϕ := ϕ)))
      = (Babai.imgOn ϕ (winSet m tdom) hgen).map
          ((tName m tdom hnd hlt).symm.permCongrHom :
            Perm ↥(winSet m tdom) ≃* Perm (Fin tdom.length)).toMonoidHom := by
  refine Eq.trans ?_ range_psiFin
  exact decGroup_rawCertM (wf_rawTAct hnd hlt gens hgen)
    (imgsOf_lcImgs_rawTAct hnd hlt gens hgen)

end Data

/-! ## The link to `Babai.recomputeReduction`

`Babai.recomputeReduction` flattens the two levels of the round: its calls are the *orbit*
instances, one per (coset, orbit) pair, while a raw round's children are instances that the
recursion answers — the per-coset instance on `W_new`, whose own round makes the orbit
calls.  That is the convention `Algo.impRound` follows against `Babai.Theorem_11_1_9`, and
the leaves of the two trees are the same instances.  What can be stated literally is that
the two reductions have the same *value* — `H(W_new)` — and the same width bound `t!`. -/

section Link

variable {ϕ : G →* Perm (Fin m)} {tdom : List ℕ} {x : Fin n → ℕ}

/-- **The link (§13.1, Procedure Recompute `H(W)`).**  On a raw instance that describes the
situation of lines 04a–04h at a stage `s` — candidate set `H(W_old)`, window
`W_new = Aff(H(W_old), ψ_T)`, strings `x, x` — the round of `Algo/LocalCertRound.lean` and
the mathematical reduction `Babai.recomputeReduction` return the same set of permutations,
namely `H(W_new)`.

*Proof.*  `Algo.run_lcRoundReduction` says the raw round's value is the answer of the
instance, which here is `Aut^{W_new}_{H(W_old)}(x) = H(W_new)`; and
`Babai.run_recomputeReduction` — Eq. (69), the correctness of the strong Luks reduction and
`Babai.recompute_eq` — says the same of the mathematical reduction. -/
theorem run_lcRoundReduction_eq_recomputeReduction (solveW : RawWinSI → RawCoset)
    {I : RawLCSI} (hI : LCWF n I)
    (hsolve : I.2 = none → (winOrbits (I.1.2.1, I.1.1)).length ≤ 1 →
      decCoset n (solveW I.1) = (decLCSI n I).answer)
    (s : Babai.Stage ϕ x (winSet m tdom))
    (lift : Babai.imgOn ϕ (winSet m tdom) s.le → Perm (Fin n))
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H,
      Babai.psiOn ϕ (winSet m tdom) s.le ⟨lift sb, h⟩ = (sb : Perm ↥(winSet m tdom)))
    (hK : (decLCSI n I).K = (s.H : Set (Perm (Fin n))))
    (hΔ : (decLCSI n I).Δ = s.aff)
    (hx : (decLCSI n I).x = x) (hy : (decLCSI n I).y = x) :
    (lcRoundReduction n solveW I).run
      = (Babai.recomputeReduction (Λ := ℕ) (x := x) s lift).run := by
  rw [run_lcRoundReduction n solveW hI hsolve,
    Babai.run_recomputeReduction s lift hlift]
  show Babai.wIso (decLCSI n I).Δ (decLCSI n I).K (decLCSI n I).x (decLCSI n I).y = _
  rw [hK, hΔ, hx, hy, Babai.Stage.step]
  rfl

/-- **The same width bound.**  The descend phase of the raw round has at most `t!` children
with `t` the length of the domain witness of the test set (`Algo.lcWidth_le_factorial`), and
that length is `|T|` (`Algo.ncard_winSet`), so the bound is the paper's `t!` with `t = |T|`
— the same number `Babai.card_imgOn_le_factorial` bounds on the mathematical side. -/
theorem lcWidth_le_factorial_ncard {I : RawLCSI} {td : RawTAct} {idx : ℕ}
    (hI : LCWF n I) (hs : I.2 = some (td, idx))
    {ψ : genGroup (descGens n I.1) →* Perm (Fin td.1.length)}
    (hψ : ImgsOf (descGens n I.1) (lcImgs td) ψ)
    (hnd : td.1.Nodup) (hlt : ∀ u ∈ td.1, u < m) :
    idx ≤ Nat.factorial (winSet m td.1).ncard := by
  rw [ncard_winSet td.1 hnd hlt]
  exact lcWidth_le_factorial hI hs hψ

end Link

end Algo
