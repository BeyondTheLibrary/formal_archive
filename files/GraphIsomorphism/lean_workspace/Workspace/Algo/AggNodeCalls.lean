import Workspace.Algo.LocalCertStepWith
import Workspace.Algo.PhaseMatch
import Workspace.LocalCertificates.AggregateRound

/-!
# Calls at the boundary of Procedure Recompute (§13.1)

The raw loop asks one Recompute child for `H(W_new)`. The mathematical
`certRun` has already expanded that child into calls on kernel cosets and
kernel orbits. The two lists of calls are different. This file states the
exact schedule and proves the obstruction to matching these two levels by
`PhaseMatch`. It does not replace the requested certificate phase.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

section Match

variable {ι ω α Ω Λ β : Type*} {R : Round ι ω α}
  {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)}
  {I : ι} {w j : ℕ} {s : ω} {T : SIReduction Ω Λ β}
  {Q : β → ℕ → ℕ → ω → Prop}

/-- A phase match must ask the first call of the mathematical reduction.
Changing the kind of a raw child does not remove this requirement. -/
theorem aggnLoopMatchK_first {J : SIInstance Ω Λ} {rest : List (SIInstance Ω Λ)}
    (hT : T.calls = J :: rest) (h : LoopMatchK R decI decA I w j s T Q) :
    ∃ K, R.child (I, j, s) = some K ∧ decI K = J := by
  cases h with
  | done => simp at hT
  | call w j s K k Q hc hn =>
      exact ⟨K, hc, (List.cons.inj hT).1⟩

end Match

section Typed

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Perm Ω)}
  {ϕ : G →* Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- Each Recompute round in §13.1 makes one call per image element and
per affected point. The mathematical list can repeat a kernel orbit. -/
theorem aggnLength_recompute (s : Stage ϕ x T)
    (lift : imgOn ϕ T s.le → Perm Ω) :
    (recomputeReduction s lift).calls.length =
      Fintype.card (imgOn ϕ T s.le) * s.aff.ncard := by
  simp [recomputeReduction, calls_unionAnswers, calls_interAnswers,
    roundInstances, List.length_flatMap]
  rw [show Finset.filter (Membership.mem s.aff) Finset.univ = s.aff.toFinset by
    ext u
    simp]
  exact (Set.ncard_eq_toFinset_card' s.aff).symm

/-- The calls of the first `i` local rounds are the concatenated lists of
their Recompute calls, in stage order. -/
theorem aggnCalls_loop (ϕ : G →* Perm Γ) (x : Ω → Λ) (T : Set Γ)
    (lift : ∀ i : ℕ, imgOn ϕ T (stages ϕ x T i).le → Perm Ω) :
    ∀ i, (loopReduction ϕ x T lift i).calls =
      (List.range i).flatMap fun j =>
        (recomputeReduction (stages ϕ x T j) (lift j)).calls := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopReduction, SIReduction.calls_bind, ih, List.range_succ]

/-- The exact calls of the certificate run in §13.2 retain all the
internal calls of every Recompute round. -/
theorem aggnCalls_certRun (ϕ : G →* Perm Γ) (x : Ω → Λ) (T : Set Γ) :
    (certRun ϕ x T).calls =
      (List.range (haltIndex ϕ x T)).flatMap fun j =>
        (recomputeReduction (stages ϕ x T j) (certLift (stages ϕ x T j))).calls := by
  rw [calls_certRun, localCertRound, localCertReduction, SIReduction.calls_bind]
  simpa using aggnCalls_loop ϕ x T (fun j => certLift (stages ϕ x T j))
    (haltIndex ϕ x T)

/-- The candidate set of each internal call is one kernel coset. -/
theorem aggnCall_kernelCoset (s : Stage ϕ x T)
    (lift : imgOn ϕ T s.le → Perm Ω) {I : SIInstance Ω Λ}
    (hI : I ∈ (recomputeReduction s lift).calls) :
    ∃ sb, I.K = lift sb • (kerN s : Set (Perm Ω)) := by
  rw [calls_recomputeReduction, List.mem_flatMap] at hI
  obtain ⟨l, hl, hIl⟩ := hI
  obtain ⟨sb, _, rfl⟩ := List.mem_map.1 hl
  obtain ⟨u, _, rfl⟩ := (mem_roundInstances_iff s _).1 hIl
  exact ⟨sb, rfl⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- A coset of a proper subgroup cannot be the whole larger group. -/
theorem aggnCoset_ne_group {H N : Subgroup (Perm Ω)} (hne : N ≠ H)
    (σ : Perm Ω) : σ • (N : Set (Perm Ω)) ≠ (H : Set (Perm Ω)) := by
  intro he
  have hσ : σ ∈ H := by
    change σ ∈ (H : Set (Perm Ω))
    rw [← he]
    exact ⟨1, N.one_mem, by simp⟩
  apply hne
  apply SetLike.coe_injective
  calc
    (N : Set (Perm Ω)) = σ⁻¹ • (σ • (N : Set (Perm Ω))) :=
      (inv_smul_smul σ _).symm
    _ = σ⁻¹ • (H : Set (Perm Ω)) := by rw [he]
    _ = (H : Set (Perm Ω)) := smul_coe_set (H.inv_mem hσ)

/-- While line 02 holds and the test set has at least three points,
the action kernel is a proper subgroup of the current group. -/
theorem aggnKer_ne_of_loop (s : Stage ϕ x T) (hcond : s.LoopCond)
    (h3 : 3 ≤ T.ncard) : kerN s ≠ s.H := by
  have hc : 3 ≤ Fintype.card T := by
    simpa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using h3
  letI : Nontrivial (alternatingGroup T) :=
    alternatingGroup.nontrivial_of_three_le_card hc
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup T)
  have ham : (a : Perm T) ∈ (psiOn ϕ T s.le).range := hcond.1 a.2
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 ham
  intro he
  have hmem : (g : Perm Ω) ∈ kerN s := he.symm ▸ g.2
  obtain ⟨h, hk⟩ := (mem_kerN s).1 hmem
  have hg1 : (a : Perm T) = 1 := hg.symm.trans hk
  exact ha (Subtype.ext hg1)

/-- No internal call of a running Recompute round has candidate group
`H(W_old)`. This is the failing call equality in the proposed phase match. -/
theorem aggnCall_ne_recomputeInput (s : Stage ϕ x T)
    (lift : imgOn ϕ T s.le → Perm Ω) (hcond : s.LoopCond) (h3 : 3 ≤ T.ncard)
    {I : SIInstance Ω Λ} (hI : I ∈ (recomputeReduction s lift).calls) :
    I ≠ (⟨(s.H : Set (Perm Ω)), s.aff, x, x⟩ : SIInstance Ω Λ) := by
  obtain ⟨sb, hK⟩ := aggnCall_kernelCoset s lift hI
  intro he
  have hEq := congrArg SIInstance.K he
  rw [hK] at hEq
  exact aggnCoset_ne_group (aggnKer_ne_of_loop s hcond h3) (lift sb) hEq

/-- A running stage has an affected point, so its expanded call list is
nonempty. This only uses the growth clause of line 02. -/
theorem aggnRecompute_calls_ne_nil (s : Stage ϕ x T) (hcond : s.LoopCond)
    (lift : imgOn ϕ T s.le → Perm Ω) : (recomputeReduction s lift).calls ≠ [] := by
  obtain ⟨u, hu, _⟩ := Set.not_subset.mp hcond.2
  have hp : 0 < (recomputeReduction s lift).calls.length := by
    rw [aggnLength_recompute]
    exact Nat.mul_pos Fintype.card_pos ((Set.ncard_pos (Set.toFinite _)).2 ⟨u, hu⟩)
  intro he
  simp [he] at hp

/-- If the initial stage runs, the first call of `certRun` comes from its
expanded Recompute reduction. -/
theorem aggnCertRun_first (hcond : (stages ϕ x T 0).LoopCond) :
    ∃ J rest, (certRun ϕ x T).calls = J :: rest ∧
      J ∈ (recomputeReduction (stages ϕ x T 0) (certLift (stages ϕ x T 0))).calls := by
  have hp : 0 < haltIndex ϕ x T := by
    by_contra hn
    have he : haltIndex ϕ x T = 0 := by omega
    exact not_loopCond_outStage ϕ x T (by simpa [outStage, he] using hcond)
  obtain ⟨k, hk⟩ : ∃ k, haltIndex ϕ x T = k + 1 := ⟨haltIndex ϕ x T - 1, by omega⟩
  have hpre : ∃ rest, (certRun ϕ x T).calls =
      (recomputeReduction (stages ϕ x T 0) (certLift (stages ϕ x T 0))).calls ++ rest := by
    rw [aggnCalls_certRun, hk, List.range_succ_eq_map, List.flatMap_cons]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hpre⟩ := hpre
  cases he : (recomputeReduction (stages ϕ x T 0) (certLift (stages ϕ x T 0))).calls with
  | nil => exact (aggnRecompute_calls_ne_nil _ hcond _ he).elim
  | cons J Js =>
      rw [he] at hpre
      exact ⟨J, Js ++ rest, hpre, List.mem_cons_self⟩

end Typed

section Raw

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}

/-- The raw child is the whole Recompute problem of §13.1, line 04. -/
theorem aggnDec_lcInst (h : StateFor hc s st) :
    decLCSI n (lcInst ((xs, tdom), st)) =
      ⟨(s.H : Set (Perm (Fin n))), s.aff, decStrN n xs, decStrN n xs⟩ := by
  have hK : (decLCSI n (lcInst ((xs, tdom), st))).K =
      (s.H : Set (Perm (Fin n))) := by
    show decCoset n (some (st.2.1, rawOne xs)) = _
    rw [← h.grp]
    ext τ
    constructor
    · rintro ⟨g, hg, rfl⟩
      rwa [decPerm_rawOne hc.lenStr, one_mul]
    · intro hτ
      exact ⟨τ, hτ, by rw [decPerm_rawOne hc.lenStr, one_mul]⟩
  exact congrArg₂
    (fun K Δ => (⟨K, Δ, decStrN n xs, decStrN n xs⟩ : SIInstance (Fin n) ℕ))
    hK (winSet_lcAffNew h)

/-- The whole Recompute child has the same answer as the expanded
Recompute reduction, for every valid choice of lifts. -/
theorem aggnAnswer_recompute (h : StateFor hc s st)
    (lift : imgOn ϕ (winSet m tdom) s.le → Perm (Fin n))
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H,
      psiOn ϕ (winSet m tdom) s.le ⟨lift sb, h⟩ = (sb : Perm (winSet m tdom))) :
    (decLCSI n (lcInst ((xs, tdom), st))).answer = (recomputeReduction s lift).run := by
  rw [answer_lcInst h, run_recomputeReduction s lift hlift]

/-- The raw Recompute child is absent from the corresponding expanded
call list while the loop runs on a test set of size at least three. -/
theorem aggnLcInst_not_mem_calls (h : StateFor hc s st)
    (hcond : lcCond ((xs, tdom), st) = true) (h3 : 3 ≤ (winSet m tdom).ncard)
    (lift : imgOn ϕ (winSet m tdom) s.le → Perm (Fin n)) :
    decLCSI n (lcInst ((xs, tdom), st)) ∉ (recomputeReduction s lift).calls := by
  intro hmem
  exact aggnCall_ne_recomputeInput s lift ((lcCond_eq_true_iff h).1 hcond) h3 hmem
    (aggnDec_lcInst h)

/-- The requested match against `certRun` cannot start with one whole
Recompute child. The contradiction holds for every budget and postcondition,
and also for an embedding into any larger raw instance type. -/
theorem aggnNo_loopMatchK_certRun {ι ω : Type*} (R : Round ι ω RawCoset)
    (decI : ι → SIInstance (Fin n) ℕ) (I J : ι) (j w : ℕ) (v : ω)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st)
    (hcond : lcCond ((xs, tdom), st) = true) (h3 : 3 ≤ (winSet m tdom).ncard)
    (hchild : R.child (I, j, v) = some J)
    (hdec : decI J = decLCSI n (lcInst ((xs, tdom), st)))
    (Q : (Set (Fin n) × Subgroup (Perm (Fin n))) → ℕ → ℕ → ω → Prop) :
    ¬ LoopMatchK R decI (decCoset n) I w j v
      (certRun ϕ (decStrN n xs) (winSet m tdom)) Q := by
  intro hm
  obtain ⟨K, rest, hfirst, hmem⟩ := aggnCertRun_first ((lcCond_eq_true_iff h).1 hcond)
  obtain ⟨J', hJ', hK⟩ := aggnLoopMatchK_first hfirst hm
  have hJJ : J' = J := Option.some.inj (hJ'.symm.trans hchild)
  rw [hJJ, hdec] at hK
  rw [← hK] at hmem
  exact aggnLcInst_not_mem_calls h hcond h3 _ hmem

/-- `PhaseMatch` has the same obstruction, independent of its width. -/
theorem aggnNo_phaseMatch_certRun {ι ω : Type*} (R : Round ι ω RawCoset)
    (decI : ι → SIInstance (Fin n) ℕ) (I J : ι) (j c : ℕ) (v : ω)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st)
    (hcond : lcCond ((xs, tdom), st) = true) (h3 : 3 ≤ (winSet m tdom).ncard)
    (hchild : R.child (I, j, v) = some J)
    (hdec : decI J = decLCSI n (lcInst ((xs, tdom), st)))
    (P : (Set (Fin n) × Subgroup (Perm (Fin n))) → ℕ → ω → Prop) :
    ¬ PhaseMatch R decI (decCoset n) I c j v
      (certRun ϕ (decStrN n xs) (winSet m tdom)) P := by
  intro hm
  exact aggnNo_loopMatchK_certRun R decI I J j (c + 0) v h hcond h3 hchild hdec _ (hm 0)

end Raw

end Algo
