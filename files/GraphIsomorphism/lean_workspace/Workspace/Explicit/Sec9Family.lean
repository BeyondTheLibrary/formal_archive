/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the number of
versions of Theorems 9.2.1–9.2.3 on the RAM. Not part of the faithful formalization.
-/
import Workspace.Explicit.Sec9Outcomes
import Workspace.Algo.SplitExtendedRunSpec
import Workspace.Algo.ChainBuild

/-!
# The number of versions of the Split-or-Johnson routines

These counts go in parallel with the validity proofs of `Algo.upccSplitBranch_valid`,
`Algo.upccSplitVersion_valid` and `Algo.extendedSplitBranch_valid`, with the same
representation facts, and with the count of `Explicit.Sec9Outcomes` in place of validity.
Every count is in the degree (the number of points), not in the encoded size.

* Theorem 9.2.2 (`Algo.bipInputRun`): at most `B m = 2^{45(log₂ m+2)^3}` outcomes on a
  represented bipartite input on `m` points (`Explicit.bipInputRun_length_le`).
* Theorem 9.2.1 (`Algo.upccSplitFamily`): at most `m · (B m + 1)`.
* Theorem 9.2.3 (`Algo.extendedSplitFamily`): at most
  `(n+1)^k · n · (B n + 1)` where `k` is the length of the arity witness (the Design Lemma
  lists one version per tuple of `k` points, then each version returns one partition or one
  UPCC family on at most `n` points).
-/

namespace Explicit

open Algo RAM Babai

/-- `B m = 2^{45(log₂ m+2)^3}`, the count of `Explicit.sbipValue_length_le_zero`. -/
def outBound (m : ℕ) : ℕ := 2 ^ (45 * (Nat.log 2 m + 2) ^ 3)

theorem outBound_mono {m m' : ℕ} (h : m ≤ m') : outBound m ≤ outBound m' := by
  unfold outBound
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) h; omega) 3

/-- The exactness of the run at `c = 0` (the conclusion of `Explicit.exists_sbipRun_exact_three`). -/
def SbipExact (t d : ℕ) : Prop :=
  ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
    sbipRun 0 t d I = some ((sbipRound 0).value f I)

theorem sbipRun_length_le {t d : ℕ} (he : SbipExact t d) {m : ℕ} {I : RawSbipNode}
    (hI : SbipNodeValid m I) : ((sbipRun 0 t d I).getD []).length ≤ outBound m := by
  rw [he m I hI (sbipNodeMeasure I + 1) (Nat.lt_succ_self _), Option.getD_some]
  exact sbipValue_length_le_zero hI _

/-- **Theorem 9.2.2 on the RAM: the number of outcomes.** -/
theorem bipInputRun_length_le {t d : ℕ} (he : SbipExact t d) {m : ℕ} {r : RawBipInput}
    {X : Pt (BipInputs (Fin m))} (h : BipInputRep m r X) :
    ((bipInputRun 0 t d r).getD []).length ≤ outBound m :=
  sbipRun_length_le he ⟨bipToBlkObj X, h.node⟩

/-- One branch of Theorem 9.2.1. -/
theorem upccSplitBranch_length_le {t d m : ℕ} (he : SbipExact t d)
    {r : RawUpcc} {C : (UPCCs (Fin m)).Obj Set.univ} (h : UpccInputRep m r C)
    {q : RawUpccOutcome} {Z : Pt (Cat.sum (ColoredPartitions (Fin m) ℕ) (BipInputs (Fin m)))}
    (hr : UpccOutcomeRep (Equiv.Set.univ (Fin m)) q Z) :
    (upccSplitBranch 0 t d (r, q)).length ≤ outBound m + 1 := by
  have hd : r.1.1.length = m := card_eq_length_dom h.table
  rcases q with ⟨q, qb⟩
  rcases Z with ⟨s, P | Y⟩
  · cases qb with
    | some bg => simp [UpccOutcomeRep] at hr
    | none => simp [upccSplitBranch]
  · cases qb with
    | none => simp [UpccOutcomeRep] at hr
    | some bg =>
      rcases bg with ⟨ab, g⟩
      let I := upccSplitBipInput ((ab, g), (r, (q, some (ab, g))))
      have hI : BipInputRep m I ⟨s, Y⟩ := upccSplitBipInput_rep hd hr
      have hc := bipInputRun_length_le he hI
      simp only [upccSplitBranch, Option.elim_some, upccSplitBipAnswers, List.length_map]
      change ((bipInputRun 0 t d I).getD []).length ≤ _
      omega

/-- **Theorem 9.2.1 on the RAM: the number of outcomes**, `≤ m · (B m + 1)`. -/
theorem upccSplitFamily_length_le {t d m : ℕ} (he : SbipExact t d)
    {r : RawUpcc} {C : (UPCCs (Fin m)).Obj Set.univ} (h : UpccInputRep m r C) :
    (upccSplitFamily 0 t d r).length ≤ m * (outBound m + 1) := by
  have hd : r.1.1.length = m := card_eq_length_dom h.table
  unfold upccSplitFamily
  rw [List.length_flatMap]
  have hle : ∀ x ∈ List.range r.1.1.length,
      (upccSplitVersion 0 t d (r, x)).length ≤ outBound m + 1 := by
    intro i hi
    have him : i < m := by simpa only [List.mem_range, hd] using hi
    have hi' : i < Upcc.widthF r := by
      simpa only [Upcc.widthF, card_eq_length_dom h.table] using him
    obtain ⟨Z, hr, -⟩ := Upcc.versionF_spec_index (⟨Set.univ, C⟩ : Pt (UPCCs (Fin m)))
      h.table (Equiv.Set.univ (Fin m)) h.names h.denominator h.lower hi'
    exact upccSplitBranch_length_le he h hr
  have := List.sum_le_card_nsmul ((List.range r.1.1.length).map
    (fun x => (upccSplitVersion 0 t d (r, x)).length)) (outBound m + 1)
    (by intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv; exact hle x hx)
  simp only [List.length_map, List.length_range, smul_eq_mul] at this
  rw [hd] at this ⊢
  exact this

/-- The number of versions the Design Lemma reads, `≤ (n+1)^k` with `k` the arity. -/
theorem length_ambientDesignReadFamily_le (a : ℕ) (g : AmbientGIn) :
    (ambientDesignReadFamily a g).length ≤ (g.1.1.2.2.length + 1) ^ g.1.1.1.length := by
  unfold ambientDesignReadFamily ambientDesignVersions
  rw [List.length_map]
  cases hp : ambientDesignProcedure a g with
  | none => simp
  | some xs =>
    simp only [Option.elim_some]
    unfold ambientDesignVersionsAt ambientDesignVersionRows
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_map]
    refine (length_aggTable_le a _).trans ?_
    simp only [List.length_take]
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (min_le_right _ _)

/-- One branch of Theorem 9.2.3. -/
theorem extendedSplitBranch_length_le {a t d n : ℕ} (he : SbipExact t d)
    {g : AmbientGIn} (h : ExtendedInputRep a n g) {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs, o) ∈ ambientDesignReadFamily a g) :
    (extendedSplitBranch 0 t d (g, o)).length ≤ n * (outBound n + 1) + 1 := by
  cases hp : o.1 with
  | some P => simp [extendedSplitBranch, hp]
  | none =>
    cases hq : o.2.2 with
    | none => simp [extendedSplitBranch, hp, hq]
    | some q =>
      obtain ⟨C, hC, -, -⟩ := h.upcc_admissible ho hq
      obtain ⟨hnd, hlt, -⟩ := h.upcc_storage ho hq
      have hm : o.2.1.length ≤ n := length_le_of_nodup_lt hnd hlt
      have hc := upccSplitFamily_length_le he hC
      simp only [extendedSplitBranch, hp, Option.elim_none, hq, Option.elim_some,
        extendedUpccAnswers, List.length_map]
      have h2 : o.2.1.length * (outBound o.2.1.length + 1) ≤ n * (outBound n + 1) :=
        Nat.mul_le_mul hm (Nat.add_le_add_right (outBound_mono hm) 1)
      omega

/-- **Theorem 9.2.3 on the RAM: the number of outcomes**,
`≤ (n+1)^k · (n (B n + 1) + 1)`. -/
theorem extendedSplitFamily_length_le {a t d n : ℕ} (he : SbipExact t d)
    {g : AmbientGIn} (h : ExtendedInputRep a n g) :
    (extendedSplitFamily a 0 t d g).length ≤
      (n + 1) ^ g.1.1.1.length * (n * (outBound n + 1) + 1) := by
  unfold extendedSplitFamily
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul ((ambientDesignReadFamily a g).map
    (fun o => (extendedSplitBranch 0 t d (g, o.2)).length)) (n * (outBound n + 1) + 1)
    (by
      intro v hv
      obtain ⟨⟨xs, o⟩, hx, rfl⟩ := List.mem_map.1 hv
      exact extendedSplitBranch_length_le he h hx)
  simp only [List.length_map, smul_eq_mul] at this
  refine this.trans (Nat.mul_le_mul_right _ ?_)
  have hr := length_ambientDesignReadFamily_le a g
  rw [h.domain_length] at hr
  exact hr

end Explicit
