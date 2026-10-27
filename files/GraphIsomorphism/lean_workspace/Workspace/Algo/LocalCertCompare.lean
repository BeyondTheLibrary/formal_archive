/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Proposition 13.1.11 on raw data.
-/
import Workspace.Algo.LocalCertRAM
import Workspace.LocalCertificates.ComparePairedCount

/-!
# Proposition 13.1.11 on raw data: comparing local certificates

> **Proposition 13.1.11** (Comparing local certificates). For all test sets `T, T' ⊆ Γ` with
> `|T| = |T'| = t` and all strings `x, x' : Ω → Σ` we can compute
> `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})` by making `≤ t!n²` calls to String Isomorphism
> problems on domains of size `≤ n/t` and performing `t! poly(n)` computation.
>
> *Proof.* Run procedure LocalCertificates simultaneously on `(x, T)` and on `(x', T')`,
> … Further maintain the set `Q = Iso_G(x_T^W, (x')_{T'}^{W'})`. On line 01 we shall have
> `Q = G_Tσ` for any `σ ∈ G` that takes `T` to `T'`. Change line 04 to "recompute `H(W)`
> and `Q`." (Procedure Recompute `H(W)` and `Q`, lines 04a–04h.)

This file is the raw procedure.  A state is the state of Procedure LocalCertificates on
`(x, T)`, the second string `x'`, and the current `Q`.  One round of the while loop computes
`H(W_new)` (the automorphism descent of line 04, `Algo.lcInst`) and `Q_new` (the comparison
descent of lines 04c0–04e2, `Algo.pcInst`): both descend to the kernel `N` of line 04a, on
the same new window, with the same `t!` coset representatives; the comparison one starts from
a representative `π₀` of `Q_old` (line 04c0) and compares `x` with `x'`.  An empty `Q` stops
the loop (line 04g, "reject isomorphism").

The target window `W'` is not maintained separately: every surviving candidate carries `W` to
`W'` (`Babai.pairedQ_next_window`), and comparing plain letters on the new window is the
printed comparison of colored truncated strings (`Babai.pairedQ_colored_round`); this is the
repaired invariant of entries 49 and 102 of the corrected paper.

* `Algo.pcOut_eq_pairedQ` — the output decodes to `Babai.pairedQ … (haltIndex …)`;
* `Algo.pcOut_eq_compareIso` — hence to `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})`, for every
  pair of test sets (the initial `Q` is the transporter set `G_Tσ` of line 01, empty when no
  `σ` exists);
* `Algo.length_pcCallsQ_le`, `Algo.window_pcCallsQ_le` — at most `t!·n²` calls, each on a
  window of at most `n/t` points.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets Babai
open Equiv (Perm)
open scoped Pointwise

/-! ## The procedure -/

/-- The state of the paired loop: the loop of Procedure LocalCertificates on `(x, T)`, the
second string `x'`, and the current value of `Q`. -/
abbrev RawPCLoop := RawLCLoop × RawStr × RawCoset

/-- Line 02 of the paired loop: the test of Procedure LocalCertificates, and `Q ≠ ∅` (an
empty `Q` has been rejected on line 04g). -/
def pcCond (z : RawPCLoop) : Bool := lcCond z.1 && z.2.2.isSome

/-- Line 04c0: `π₀ ∈ Q_old`, the representative of the stored coset. -/
def pcRep (z : RawPCLoop) : RawPerm :=
  normPerm (z.1.1.1, (z.2.2.getD ([], rawOne z.1.1.1)).2)

/-- **Lines 04c0–04e2**, the comparison instance: candidates `π₀·H(W_old)` (which is
`Q_old`), window `W_new`, strings `x` and `x'`, descending to `N` with the data of line 04
(`Algo.lcInst`).  Its answer is `Q_new`. -/
def pcInst (z : RawPCLoop) : RawLCSI :=
  (((lcInst z.1).1.1, (lcInst z.1).1.2.1, pcRep z, z.1.1.1, z.2.1), (lcInst z.1).2)

/-- One round with the two answers `H(W_new)` and `Q_new` given. -/
def pcStepWith (a b : RawCoset) (z : RawPCLoop) : RawPCLoop := (lcStepWith a z.1, z.2.1, b)

/-- **One round of the paired loop**: "recompute `H(W)` and `Q`". -/
def pcStep (solve : RawLCSI → RawCoset) (z : RawPCLoop) : RawPCLoop :=
  if pcCond z then pcStepWith (solve (lcInst z.1)) (solve (pcInst z)) z else z

/-- The output: `Q` after `n` rounds (the loop stops after at most `n` rounds). -/
def pcOut (solve : RawLCSI → RawCoset) (z : RawPCLoop) : RawCoset :=
  ((pcStep solve)^[z.1.1.1.length] z).2.2

/-- The String Isomorphism calls of one round, with Recompute answered through `ansQ`. -/
def pcStepCalls (ansQ : RawWinSI → RawCoset) (z : RawPCLoop) : List RawWinSI :=
  if pcCond z then lcDescCalls ansQ (lcInst z.1) ++ lcDescCalls ansQ (pcInst z) else []

/-- All String Isomorphism calls of the paired procedure. -/
def pcCallsQ (ansQ : RawWinSI → RawCoset) (z : RawPCLoop) : List RawWinSI :=
  (List.range z.1.1.1.length).flatMap
    (fun j => pcStepCalls ansQ ((pcStep (lcSolveQ ansQ))^[j] z))

theorem pcStep_ctx (solve : RawLCSI → RawCoset) (z : RawPCLoop) :
    (pcStep solve z).1.1 = z.1.1 ∧ (pcStep solve z).2.1 = z.2.1 := by
  unfold pcStep
  split
  · exact ⟨lcStep_fst (fun _ => solve (lcInst z.1)) z.1 ▸ rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem pcStep_iterate_ctx (solve : RawLCSI → RawCoset) :
    ∀ (j : ℕ) (z : RawPCLoop),
      ((pcStep solve)^[j] z).1.1 = z.1.1 ∧ ((pcStep solve)^[j] z).2.1 = z.2.1
  | 0, _ => ⟨rfl, rfl⟩
  | j + 1, z => by
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := pcStep_ctx solve ((pcStep solve)^[j] z)
      obtain ⟨h3, h4⟩ := pcStep_iterate_ctx solve j z
      exact ⟨h1.trans h3, h2.trans h4⟩

theorem pcStep_of_not_cond (solve : RawLCSI → RawCoset) {z : RawPCLoop}
    (h : pcCond z = false) : pcStep solve z = z := by
  rw [pcStep, if_neg (by simp [h])]

theorem pcStep_iterate_of_not_cond (solve : RawLCSI → RawCoset) {z : RawPCLoop}
    (h : pcCond z = false) : ∀ k, (pcStep solve)^[k] z = z
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply', pcStep_iterate_of_not_cond solve h k,
        pcStep_of_not_cond solve h]

/-! ## Correctness -/

section Correct

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}

/-- The comparison instance is well formed. -/
theorem lcwf_pcInst {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}
    (h : StateFor hc s st) (hy : ys.length = n) (q : RawCoset) :
    LCWF n (pcInst (((xs, tdom), st), ys, q)) := by
  have hI := lcwf_lcInst h
  refine ⟨⟨hI.1.1, hy, hI.1.2.2.1, hI.1.2.2.2.1, hI.1.2.2.2.2.1, hI.1.2.2.2.2.2.1,
    wf_normPerm hc.lenStr _, hI.1.2.2.2.2.2.2.2⟩, ?_⟩
  exact hI.2

/-- The representative of line 04c0 lies in `Q_old`, and `Q_old = π₀·H(W_old)`. -/
theorem decCoset_pcRep {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {i : ℕ}
    {st : RawLCSt} (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    {g : RawGens} {r : RawPerm}
    (hQ : decCoset n (some (g, r))
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i) :
    decPerm n (pcRep (((xs, tdom), st), ys, some (g, r))) • (decGroup n st.2.1 : Set (Perm (Fin n)))
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i := by
  have hr : decPerm n (pcRep (((xs, tdom), st), ys, some (g, r))) = decPerm n r :=
    decPerm_normPerm hc.lenStr r
  have hmem : decPerm n r ∈ pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i := by
    rw [← hQ, decCoset_some]
    exact ⟨1, (decGroup n g).one_mem, by simp⟩
  rw [hr, pairedQ_eq_coset hσ₀ i hmem, h.grp]

/-- **The answer of the comparison instance is `Q_new`** (line 04e2 and Remark 13.1.12's
repaired invariant, `Babai.pairedQ_succ`). -/
theorem answer_pcInst {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {i : ℕ}
    {st : RawLCSt} (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    {g : RawGens} {r : RawPerm}
    (hQ : decCoset n (some (g, r))
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i) :
    (decLCSI n (pcInst (((xs, tdom), st), ys, some (g, r)))).answer
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ (i + 1) := by
  have hK : (decLCSI n (pcInst (((xs, tdom), st), ys, some (g, r)))).K
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i := by
    show decCoset n (some (st.2.1, pcRep (((xs, tdom), st), ys, some (g, r)))) = _
    rw [decCoset_some]
    exact decCoset_pcRep hσ₀ h hQ
  have hΔ : (decLCSI n (pcInst (((xs, tdom), st), ys, some (g, r)))).Δ
      = (stages ϕ (decStrN n xs) (winSet m tdom) i).aff := winSet_lcAffNew h
  show wIso _ _ _ _ = _
  rw [hK, hΔ, pairedQ_succ]
  rfl

variable (hc) in
/-- **The invariant of the paired loop.**  The second string is kept; and either the loop is
live, its state decodes to the stage of round `i` and `Q` decodes to `Babai.pairedQ … i`, or
`Q` has been rejected (line 04g) and `Babai.pairedQ … i` is empty. -/
def PCInv (ϕ : G →* Perm (Fin m)) (ys : RawStr) (σ₀ : Perm (Fin n)) (i : ℕ)
    (z : RawPCLoop) : Prop :=
  z.2.1 = ys ∧
    ((∃ st, z.1 = ((xs, tdom), st) ∧
        StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st ∧
        decCoset n z.2.2 = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i) ∨
      (z.2.2 = none ∧ pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i = ∅))

variable {solve : RawLCSI → RawCoset}

/-- **One round of the paired loop** carries the invariant from round `i` to round `i + 1`. -/
theorem pcInv_step (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {i : ℕ}
    (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom)) {z : RawPCLoop}
    (hz : PCInv hc ϕ ys σ₀ i z) : PCInv hc ϕ ys σ₀ (i + 1) (pcStep solve z) := by
  obtain ⟨hzy, hz⟩ := hz
  rcases hz with ⟨st, hz1, hst, hQ⟩ | ⟨hnone, hemp⟩
  · obtain ⟨p, y', q⟩ := z
    simp only at hz1 hzy hQ
    subst hz1; subst y'
    cases q with
    | none =>
      have hemp : pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ i = ∅ := by
        rw [← hQ]; rfl
      rw [pcStep_of_not_cond solve (by simp [pcCond])]
      exact ⟨rfl, Or.inr ⟨rfl, pairedQ_succ_empty _ σ₀ i (by rw [hemp]; simp)⟩⟩
    | some gr =>
      obtain ⟨g, r⟩ := gr
      have hcond : lcCond ((xs, tdom), st) = true :=
        (lcCond_eq_true_iff hst).2 (loopCond_of_lt_haltIndex ϕ _ _ hi)
      have hpc : pcCond (((xs, tdom), st), ys, some (g, r)) = true := by
        simp [pcCond, hcond]
      rw [pcStep, if_pos hpc]
      refine ⟨rfl, Or.inl ⟨(lcStepWith (solve (lcInst ((xs, tdom), st))) ((xs, tdom), st)).2,
        ?_, ?_, ?_⟩⟩
      · show lcStepWith _ ((xs, tdom), st) = _
        exact Prod.ext (lcStep_fst (fun _ => solve (lcInst ((xs, tdom), st))) _) rfl
      · exact lcwStateFor_succ (hsolve _ (lcwf_lcInst hst)) hst hcond
      · show decCoset n (solve (pcInst (((xs, tdom), st), ys, some (g, r)))) = _
        rw [hsolve _ (lcwf_pcInst hst hy _)]
        exact answer_pcInst hσ₀ hst hQ
  · rw [pcStep_of_not_cond solve (by simp [pcCond, hnone])]
    exact ⟨hzy, Or.inr ⟨hnone, pairedQ_succ_empty _ σ₀ i (by rw [hemp]; simp)⟩⟩

/-- At the halting round the paired loop has stopped. -/
theorem pcCond_haltIndex {σ₀ : Perm (Fin n)} {z : RawPCLoop}
    (hz : PCInv hc ϕ ys σ₀ (haltIndex ϕ (decStrN n xs) (winSet m tdom)) z) :
    pcCond z = false := by
  rcases hz.2 with ⟨st, hz1, hst, -⟩ | ⟨hnone, -⟩
  · have h : lcCond z.1 = false := by
      rw [hz1]
      by_contra hne
      exact not_loopCond_outStage ϕ _ _ ((lcCond_eq_true_iff hst).1 (by simpa using hne))
    simp [pcCond, h]
  · simp [pcCond, hnone]

/-- The invariant along the loop, up to the halting round. -/
theorem pcInv_iterate (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {z : RawPCLoop}
    (hz : PCInv hc ϕ ys σ₀ 0 z) :
    ∀ j ≤ haltIndex ϕ (decStrN n xs) (winSet m tdom),
      PCInv hc ϕ ys σ₀ j ((pcStep solve)^[j] z)
  | 0, _ => hz
  | j + 1, hj => by
      rw [Function.iterate_succ_apply']
      exact pcInv_step hsolve hy hσ₀ (by omega) (pcInv_iterate hsolve hy hσ₀ hz j (by omega))

/-- **A round that passes the test of line 02** is one of the first `haltIndex` rounds, and
the loop is live there. -/
theorem pcCond_iterate (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {z : RawPCLoop}
    (hz : PCInv hc ϕ ys σ₀ 0 z) {j : ℕ} (hj : pcCond ((pcStep solve)^[j] z) = true) :
    j < haltIndex ϕ (decStrN n xs) (winSet m tdom) ∧
      ∃ st, ((pcStep solve)^[j] z).1 = ((xs, tdom), st) ∧
        StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) j) st ∧
        ((pcStep solve)^[j] z).2.1 = ys ∧
        decCoset n ((pcStep solve)^[j] z).2.2
          = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀ j := by
  set H := haltIndex ϕ (decStrN n xs) (winSet m tdom)
  have hlt : j < H := by
    by_contra hge
    push Not at hge
    have hH := pcInv_iterate hsolve hy hσ₀ hz H le_rfl
    have hc0 := pcCond_haltIndex hH
    have he : (pcStep solve)^[j] z = (pcStep solve)^[H] z := by
      rw [show j = (j - H) + H by omega, Function.iterate_add_apply,
        pcStep_iterate_of_not_cond solve hc0]
    rw [he, hc0] at hj
    exact absurd hj (by simp)
  refine ⟨hlt, ?_⟩
  obtain ⟨hzy, hzz⟩ := pcInv_iterate hsolve hy hσ₀ hz j hlt.le
  rcases hzz with ⟨st, h1, h2, h3⟩ | ⟨hnone, -⟩
  · exact ⟨st, h1, h2, hzy, h3⟩
  · simp [pcCond, hnone] at hj

/-- **The output decodes to `Q` at the halting round**. -/
theorem pcOut_eq_pairedQ (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {st0 : RawLCSt} {q0 : RawCoset}
    (hz : PCInv hc ϕ ys σ₀ 0 (((xs, tdom), st0), ys, q0)) :
    decCoset n (pcOut solve (((xs, tdom), st0), ys, q0))
      = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ₀
          (haltIndex ϕ (decStrN n xs) (winSet m tdom)) := by
  set H := haltIndex ϕ (decStrN n xs) (winSet m tdom)
  have hHn : H ≤ xs.length := by
    have := haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [hc.lenStr]; exact this
  have hH := pcInv_iterate hsolve hy hσ₀ hz H le_rfl
  have he : (pcStep solve)^[xs.length] (((xs, tdom), st0), ys, q0)
      = (pcStep solve)^[H] (((xs, tdom), st0), ys, q0) := by
    rw [show xs.length = (xs.length - H) + H by omega, Function.iterate_add_apply,
      pcStep_iterate_of_not_cond solve (pcCond_haltIndex hH)]
  show decCoset n ((pcStep solve)^[xs.length] _).2.2 = _
  rw [he]
  rcases hH.2 with ⟨-, -, -, h3⟩ | ⟨hnone, hemp⟩
  · exact h3
  · rw [hnone, hemp]; rfl

/-- The transporter set of line 01, `{σ ∈ G : σ(T) = T'}`, is `σ₀·G_T` for any of its
members `σ₀`. -/
theorem transporter_eq_smul {σ₀ : Perm (Fin n)} (hσ₀ : σ₀ ∈ G) {T T' : Set (Fin m)}
    (hmap : (ϕ ⟨σ₀, hσ₀⟩ : Perm (Fin m)) '' T = T') :
    {σ : Perm (Fin n) | ∃ h : σ ∈ G, (ϕ ⟨σ, h⟩ : Perm (Fin m)) '' T = T'}
      = σ₀ • (bigGT ϕ T : Set (Perm (Fin n))) := by
  ext σ
  constructor
  · rintro ⟨hσ, himg⟩
    refine ⟨σ₀⁻¹ * σ, ?_, by simp⟩
    have hG : σ₀⁻¹ * σ ∈ G := G.mul_mem (G.inv_mem hσ₀) hσ
    show σ₀⁻¹ * σ ∈ stabIn ϕ (le_refl G) T
    refine mem_stabIn.2 ⟨hG, ?_⟩
    have he : (⟨σ₀⁻¹ * σ, hG⟩ : G) = (⟨σ₀, hσ₀⟩ : G)⁻¹ * ⟨σ, hσ⟩ := rfl
    rw [he, map_mul, map_inv, Perm.coe_mul, Set.image_comp, himg, ← hmap, ← Set.image_comp,
      ← Perm.coe_mul, inv_mul_cancel, Perm.coe_one, Set.image_id]
  · rintro ⟨κ, hκ, rfl⟩
    obtain ⟨hG, hT⟩ := initialCoset_testImage (ϕ := ϕ) (T := T) hσ₀ ⟨κ, hκ, rfl⟩
    exact ⟨hG, by rw [← testImage_def, hT, testImage_def, hmap]⟩

end Correct

/-! ## Line 01 and the output -/

section Output

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}

variable (ϕ) in
/-- **Line 01**: the initial value of `Q`, the set of `σ ∈ G` that take `T` to `T'`.  It is
`G_Tσ₀` for any such `σ₀` (`Algo.transporter_eq_smul`; the paper: "on line 01 we shall have
`Q = G_Tσ` for any `σ ∈ G` that takes `T` to `T'`"), and empty when there is none. -/
def pcTransporters (T T' : Set (Fin m)) : Set (Perm (Fin n)) :=
  {σ | ∃ h : σ ∈ G, (ϕ ⟨σ, h⟩ : Perm (Fin m)) '' T = T'}

theorem pairedQ_zero (x y : Fin n → ℕ) (T : Set (Fin m)) (σ₀ : Perm (Fin n)) :
    pairedQ ϕ x y T σ₀ 0 = σ₀ • (bigGT ϕ T : Set (Perm (Fin n))) := by
  ext σ
  simp [pairedQ, wIso, Stage.init]

theorem decCoset_ne_empty_of_some {g : RawGens} {r : RawPerm} :
    decCoset n (some (g, r)) ≠ ∅ := by
  intro he
  have : decPerm n r ∈ decCoset n (some (g, r)) := ⟨1, (decGroup n g).one_mem, by rw [mul_one]⟩
  rw [he] at this
  exact this

/-- **The loop is live whenever it runs**: a round that passes the test of line 02 is one of
the first `haltIndex` rounds, and its state decodes to the stage of that round. -/
theorem pc_live {solve : RawLCSI → RawCoset}
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) {T' : Set (Fin m)} {st0 : RawLCSt} {q0 : RawCoset}
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hq0 : decCoset n q0 = pcTransporters ϕ (winSet m tdom) T') {j : ℕ}
    (hj : pcCond ((pcStep solve)^[j] (((xs, tdom), st0), ys, q0)) = true) :
    j < haltIndex ϕ (decStrN n xs) (winSet m tdom) ∧
      ∃ st, ((pcStep solve)^[j] (((xs, tdom), st0), ys, q0)).1 = ((xs, tdom), st) ∧
        StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) j) st := by
  by_cases hex : ∃ σ₀ : Perm (Fin n), ∃ h : σ₀ ∈ G,
      (ϕ ⟨σ₀, h⟩ : Perm (Fin m)) '' winSet m tdom = T'
  · obtain ⟨σ₀, hσ₀, hmap⟩ := hex
    have hz : PCInv hc ϕ ys σ₀ 0 (((xs, tdom), st0), ys, q0) := by
      refine ⟨rfl, Or.inl ⟨st0, rfl, h0, ?_⟩⟩
      show decCoset n q0 = _
      rw [hq0, pcTransporters, transporter_eq_smul hσ₀ hmap, pairedQ_zero]
    obtain ⟨hlt, st, h1, h2, -, -⟩ := pcCond_iterate hsolve hy hσ₀ hz hj
    exact ⟨hlt, st, h1, h2⟩
  · have hnone : q0 = none := by
      cases q0 with
      | none => rfl
      | some gr =>
        exfalso
        obtain ⟨g, r⟩ := gr
        obtain ⟨σ, hσ⟩ := Set.nonempty_iff_ne_empty.2 (decCoset_ne_empty_of_some (n := n))
        rw [hq0] at hσ
        obtain ⟨h, himg⟩ := hσ
        exact hex ⟨σ, h, himg⟩
    have hc0 : pcCond (((xs, tdom), st0), ys, q0) = false := by simp [pcCond, hnone]
    rw [pcStep_iterate_of_not_cond solve hc0, hc0] at hj
    exact absurd hj (by simp)

/-- **Proposition 13.1.11, the output**: for every pair of test sets `T, T'` of the same size
`t`, the paired procedure started with `Q = G_Tσ` (line 01) returns
`Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})`, provided each Recompute instance is answered
correctly. -/
theorem pcOut_eq_compareIso {solve : RawLCSI → RawCoset}
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (hy : ys.length = n) (hset : LocalCertSetting G ϕ)
    (ht : LargeK (winSet m tdom).ncard (Nat.card (Fin n)))
    (htm : 10 * (winSet m tdom).ncard ≤ Nat.card (Fin m))
    {T' : Set (Fin m)} (hT' : T'.ncard = (winSet m tdom).ncard) [Nonempty (Fin n)]
    {st0 : RawLCSt} {q0 : RawCoset}
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hq0 : decCoset n q0 = pcTransporters ϕ (winSet m tdom) T') :
    decCoset n (pcOut solve (((xs, tdom), st0), ys, q0))
      = compareIso ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) T' := by
  by_cases hex : ∃ σ₀ : Perm (Fin n), ∃ h : σ₀ ∈ G,
      (ϕ ⟨σ₀, h⟩ : Perm (Fin m)) '' winSet m tdom = T'
  · obtain ⟨σ₀, hσ₀, hmap⟩ := hex
    have hz : PCInv hc ϕ ys σ₀ 0 (((xs, tdom), st0), ys, q0) := by
      refine ⟨rfl, Or.inl ⟨st0, rfl, h0, ?_⟩⟩
      show decCoset n q0 = _
      rw [hq0, pcTransporters, transporter_eq_smul hσ₀ hmap, pairedQ_zero]
    rw [pcOut_eq_pairedQ hsolve hy hσ₀ hz]
    exact pairedQ_out_eq_compareIso hset ht htm hT' σ₀ hσ₀ hmap
  · have hnone : q0 = none := by
      cases q0 with
      | none => rfl
      | some gr =>
        exfalso
        obtain ⟨g, r⟩ := gr
        obtain ⟨σ, hσ⟩ := Set.nonempty_iff_ne_empty.2 (decCoset_ne_empty_of_some (n := n))
        rw [hq0] at hσ
        obtain ⟨h, himg⟩ := hσ
        exact hex ⟨σ, h, himg⟩
    have hc0 : pcCond (((xs, tdom), st0), ys, q0) = false := by simp [pcCond, hnone]
    have hout : pcOut solve (((xs, tdom), st0), ys, q0) = none := by
      show ((pcStep solve)^[xs.length] _).2.2 = none
      rw [pcStep_iterate_of_not_cond solve hc0]
      exact hnone
    rw [hout]
    symm
    apply Set.eq_empty_iff_forall_notMem.2
    intro σ hσ
    obtain ⟨hG, hm⟩ := compareIso_testImage ϕ _ _ _ _ hset ht htm hT' hσ
    exact hex ⟨σ, hG, hm⟩

end Output

/-! ## The calls -/

section Calls

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {ansQ : RawWinSI → RawCoset}

/-- A sum over the first `N` rounds, of terms bounded by `B` that vanish from round `H` on. -/
theorem sum_range_le_of_vanish (f : ℕ → ℕ) (B H : ℕ) (hB : ∀ j, f j ≤ B)
    (hz : ∀ j, H ≤ j → f j = 0) : ∀ N, ((List.range N).map f).sum ≤ H * B := by
  have key : ∀ N, ((List.range N).map f).sum ≤ min N H * B := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rcases lt_or_ge N H with h | h
      · rw [show min (N + 1) H = min N H + 1 by omega, Nat.add_mul, one_mul]
        exact Nat.add_le_add ih (hB N)
      · rw [hz N h, show min (N + 1) H = min N H by omega]
        omega
  intro N
  exact (key N).trans (Nat.mul_le_mul_right _ (min_le_right _ _))

/-- One live round makes at most `2·t!·n` calls: two runs of Procedure Recompute, at most
`t!` cosets each, at most `n` calls on each coset. -/
theorem length_pcStepCalls_le {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}
    (h : StateFor hc s st) (hy : ys.length = n) (q : RawCoset) (hn : 1 ≤ n) :
    (pcStepCalls ansQ (((xs, tdom), st), ys, q)).length
      ≤ 2 * (Nat.factorial tdom.length * n) := by
  unfold pcStepCalls
  split
  · rw [List.length_append]
    have hI := lcwf_lcInst h
    have hJ := lcwf_pcInst h hy q
    have hs : (lcInst ((xs, tdom), st)).2 = some ((tdom, st.2.2), lcIdx ((xs, tdom), st)) := rfl
    have hsJ : (pcInst (((xs, tdom), st), ys, q)).2
        = some ((tdom, st.2.2), lcIdx ((xs, tdom), st)) := rfl
    obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI.2 _ _ hs
    have hidx : lcIdx ((xs, tdom), st) ≤ Nat.factorial tdom.length :=
      lcWidth_le_factorial hI hs hψ
    have h1 : (lcDescCalls ansQ (lcInst (((xs, tdom), st), ys, q).1)).length
        ≤ lcIdx ((xs, tdom), st) * n := length_lcDescCalls_le hI hs hn
    have h2 : (lcDescCalls ansQ (pcInst (((xs, tdom), st), ys, q))).length
        ≤ lcIdx ((xs, tdom), st) * n := length_lcDescCalls_le hJ hsJ hn
    have h3 : lcIdx ((xs, tdom), st) * n ≤ Nat.factorial tdom.length * n :=
      Nat.mul_le_mul_right _ hidx
    omega
  · simp

variable (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
include hQ

/-- **Proposition 13.1.11, the number of calls**: at most `t!·n²`.  Each live round makes at
most `2·t!·n` calls, and there are at most `n/t` live rounds, because the window grows by at
least `t` points per round (`Babai.haltIndex_mul_le_card`, entry 102 of the corrected paper). -/
theorem length_pcCallsQ_le (hy : ys.length = n) (h5 : 5 ≤ tdom.length) {T' : Set (Fin m)}
    {st0 : RawLCSt} {q0 : RawCoset}
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hq0 : decCoset n q0 = pcTransporters ϕ (winSet m tdom) T') :
    (pcCallsQ ansQ (((xs, tdom), st0), ys, q0)).length ≤ Nat.factorial tdom.length * n ^ 2 := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  set z0 : RawPCLoop := (((xs, tdom), st0), ys, q0)
  have hT : (winSet m tdom).ncard = tdom.length := ncard_winSet tdom hc.nodup hc.ltM
  have hH : haltIndex ϕ (decStrN n xs) (winSet m tdom) * tdom.length ≤ n := by
    have := haltIndex_mul_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)
      (by rw [hT]; exact h5)
    rw [hT, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  unfold pcCallsQ
  rw [List.length_flatMap]
  let f : ℕ → ℕ := fun j => (pcStepCalls ansQ ((pcStep (lcSolveQ ansQ))^[j] z0)).length
  have hB : ∀ j, f j ≤ 2 * (Nat.factorial tdom.length * n) := by
    intro j
    by_cases hj : pcCond ((pcStep (lcSolveQ ansQ))^[j] z0) = true
    · obtain ⟨hlt, st, h1, h2⟩ := pc_live hsolve hy h0 hq0 hj
      have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z0
      have he : (pcStep (lcSolveQ ansQ))^[j] z0
          = (((xs, tdom), st), ys, ((pcStep (lcSolveQ ansQ))^[j] z0).2.2) :=
        Prod.ext h1 (Prod.ext hctx.2 rfl)
      show (pcStepCalls ansQ ((pcStep (lcSolveQ ansQ))^[j] z0)).length ≤ _
      rw [he]
      have hpos : 1 ≤ haltIndex ϕ (decStrN n xs) (winSet m tdom) * tdom.length :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      exact length_pcStepCalls_le h2 hy _ (by omega)
    · show (pcStepCalls ansQ ((pcStep (lcSolveQ ansQ))^[j] z0)).length ≤ _
      simp [pcStepCalls, hj]
  have hz : ∀ j, haltIndex ϕ (decStrN n xs) (winSet m tdom) ≤ j → f j = 0 := by
    intro j hj
    by_cases hc' : pcCond ((pcStep (lcSolveQ ansQ))^[j] z0) = true
    · exact absurd (pc_live hsolve hy h0 hq0 hc').1 (not_lt.2 hj)
    · show (pcStepCalls ansQ ((pcStep (lcSolveQ ansQ))^[j] z0)).length = 0
      simp [pcStepCalls, hc']
  refine (sum_range_le_of_vanish f _ _ hB hz _).trans ?_
  exact rounds_calls_le hH (by omega)

/-- **Proposition 13.1.11, the size of the domains**: every call is a well-formed instance on
a window of at most `n/t` points. -/
theorem window_pcCallsQ_le (hy : ys.length = n) (h5 : 5 ≤ tdom.length) {T' : Set (Fin m)}
    {st0 : RawLCSt} {q0 : RawCoset}
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hq0 : decCoset n q0 = pcTransporters ϕ (winSet m tdom) T') :
    ∀ W ∈ pcCallsQ ansQ (((xs, tdom), st0), ys, q0), WinWF n W ∧ tdom.length * W.1.length ≤ n := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  intro W hW
  unfold pcCallsQ at hW
  obtain ⟨j, -, hWj⟩ := List.mem_flatMap.1 hW
  unfold pcStepCalls at hWj
  by_cases hcond : pcCond ((pcStep (lcSolveQ ansQ))^[j] (((xs, tdom), st0), ys, q0)) = true
  swap
  · rw [if_neg hcond] at hWj; simp at hWj
  rw [if_pos hcond] at hWj
  obtain ⟨hlt, st, h1, h2⟩ := pc_live hsolve hy h0 hq0 hcond
  have hrun := loopCond_of_lt_haltIndex ϕ (decStrN n xs) (winSet m tdom) hlt
  have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j (((xs, tdom), st0), ys, q0)
  set z := (pcStep (lcSolveQ ansQ))^[j] (((xs, tdom), st0), ys, q0)
  have he : z = (((xs, tdom), st), ys, z.2.2) := Prod.ext h1 (Prod.ext hctx.2 rfl)
  rw [he] at hWj
  rcases List.mem_append.1 hWj with hW1 | hW2
  · exact window_lcDescCalls_le h2 hrun h5 (lcwf_lcInst h2) rfl rfl rfl W hW1
  · exact window_lcDescCalls_le h2 hrun h5 (lcwf_pcInst h2 hy _) rfl rfl rfl W hW2

end Calls

end Algo
