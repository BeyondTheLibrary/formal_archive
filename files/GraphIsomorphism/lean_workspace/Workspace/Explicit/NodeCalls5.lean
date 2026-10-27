/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the calls of the
run at a good node of route 5 (Sec. 15, lines 5–7). Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeCalls4
import Workspace.Explicit.Top.Recursion

/-!
# The calls of lines 5–7 at a good node

The width of route 5 holds the reserve `2^{(log₂|Δ|+2)^E}` of the Chain Rule of line 5, whose
exponent `E` is a `Classical.choose`. So the calls of the run are counted here from the
tree the round walks (`Algo.exists_l57Tree`), not from the width:

* `Explicit.LoopMatchS.calls_le_of_inv`: a run with an invariant under which every call has
  index `< Q` makes at most `Q - j` calls from index `j`;
* `Explicit.LoopMatchK.calls_le_split`: a run that starts with a phase (`Algo.LoopMatchK`)
  makes at most `N - j` calls when every run from every end state of the phase does;
* `Explicit.l57Tree_calls_le`: the tree of lines 5–7 makes at most `W + X` calls, where `W`
  is the width of the two phases of AggregateCertificates and `X` bounds, at every state the
  phases end in, the calls of stretch 3 (`Algo.l57Calls`) and of the giant branch
  (`Algo.aggnL57GW`).
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv

section Generic
variable {ι ω α β Ω A : Type} [Fintype Ω] [DecidableEq Ω] {R : Round ι ω α}
  {C : ℕ → ω → ι → Prop} {decI : ι → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)} {I : ι}

/-- **Counting calls with an invariant.** If every call made from a state with `Inv` has
index `< Q`, and `Inv` survives each call, then a run from index `j` makes at most
`max j Q - j` calls. -/
theorem LoopMatchS.calls_le_of_inv (Inv : ℕ → ω → Prop) (Q : ℕ)
    (hstep : ∀ j s J a, Inv j s → R.child (I, j, s) = some J →
      Inv (j + 1) (R.combine (I, j, s, a)))
    (hQ : ∀ j s J, Inv j s → R.child (I, j, s) = some J → j < Q) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatchS R C decI decA I w j s T → Inv j s →
        (∀ K ∈ T.calls, ∃ a : α, decA a = K.answer) → j + T.calls.length ≤ max j Q := by
  intro w j s T h
  induction h with
  | done => intro _ _; simp
  | call w j s J k hc hC hnext ih =>
    intro hinv hrec
    rw [SIReduction.calls_call] at hrec
    obtain ⟨a, ha⟩ := hrec _ List.mem_cons_self
    have h1 := ih a ha (hstep j s J a hinv hc) fun K hK => hrec K (List.mem_cons_of_mem _ hK)
    have h2 := hQ j s J hinv hc
    rw [SIReduction.calls_call, List.length_cons]
    have : max (j + 1) Q = Q := max_eq_right h2
    rw [this] at h1
    exact (show j + ((k (decI J).answer).calls.length + 1) ≤ Q by omega).trans (le_max_right _ _)

/-- **Counting calls through a first phase.** If a phase `Tp` is walked from `(j, s)` and
every run from an end state of the phase makes calls up to index `N`, so does every run from
`(j, s)`. -/
theorem LoopMatchK.calls_le_split (N : ℕ) :
    ∀ {w j : ℕ} {s : ω} {Tp : SIReduction Ω A β} {Qk : β → ℕ → ℕ → ω → Prop},
      LoopMatchK R decI decA I w j s Tp Qk →
      (∀ b w' j' s', Qk b w' j' s' → ∀ w'' (T' : SIReduction Ω A (Set (Equiv.Perm Ω))),
        LoopMatchS R C decI decA I w'' j' s' T' →
        (∀ K ∈ T'.calls, ∃ a : α, decA a = K.answer) → j' + T'.calls.length ≤ N) →
      ∀ {w''} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
        LoopMatchS R C decI decA I w'' j s T →
        (∀ K ∈ T.calls, ∃ a : α, decA a = K.answer) → j + T.calls.length ≤ N := by
  intro w j s Tp Qk h
  induction h with
  | done w j s b Q hq => intro hQ w'' T hT hans; exact hQ b w j s hq w'' T hT hans
  | call w j s J k Q hc hnext ih =>
    intro hQ w'' T hT hans
    cases hT with
    | done _ _ _ _ hc' => rw [hc] at hc'; cases hc'
    | call w₀ _ _ J' k' hc' hC hnext' =>
      have hJ : J' = J := Option.some.inj (hc'.symm.trans hc)
      subst hJ
      rw [SIReduction.calls_call] at hans
      obtain ⟨a, ha⟩ := hans _ List.mem_cons_self
      have h1 := ih a ha hQ (hnext' a ha) fun K hK => hans K (List.mem_cons_of_mem _ hK)
      rw [SIReduction.calls_call, List.length_cons]
      omega

end Generic

section L57
variable {c b t d dc dp u v e f n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- After the two phases, the stores stay put: every combine of the round keeps the
aggregate state `sR` the phases ended in. -/
theorem l57G_combine_keep {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR)
    (j : ℕ) (s : AggnL57GState) (hs : s.1.1 = sR) (a : RawCoset) :
    ((aggnL57GRound c b t d dc dp u v e f).combine ((C, none), j, s, a)).1.1 = sR := by
  show (aggnL57GCombine c b t d dc dp u v e f ((C, none), j, s, a)).1.1 = sR
  unfold aggnL57GCombine
  split
  · show aggnAggregatePack c dc dp C s.1.1 = sR
    rw [hs]; exact hpost.1
  · show (aggnL57Combine c b t d dc dp ((C, none), j, s.1, a)).1 = sR
    unfold aggnL57Combine
    have h0 : aggnAggregateChild c (((C, none) : AggnPhaseNode), j, s.1.1) = none := by
      rw [hs]; exact aggnL57_agg_done hpost j
    rw [h0]
    show aggnAggregatePack c dc dp C s.1.1 = sR
    rw [hs]; exact hpost.1

/-- After the two phases, a call has index below the width of the phases plus the calls of
stretch 3 or of the giant branch at the final stores. -/
theorem l57G_child_lt {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR)
    (j : ℕ) (s : AggnL57GState) (hs : s.1.1 = sR) (J : AggnPhaseNode)
    (hJ : (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J) :
    j < aggnAggregateWidth c C +
      max (l57Calls (aggnL57Hdr c b t d dc dp (C, sR))) (aggnL57GW c b t d dc dp u v e f (C, sR)) := by
  change aggnL57GChild c b t d dc dp u v e f ((C, none), j, s) = some J at hJ
  unfold aggnL57GChild at hJ
  split at hJ
  next ha =>
    unfold aggnL57GTopChild at hJ
    split at hJ
    next hlt =>
      have hon : aggnL57GOn c b t d dc dp u v e f (C, s.1.1) = true := by
        unfold aggnL57GActive at ha
        simp only [Bool.and_eq_true] at ha
        exact ha.2
      have hw : aggnL57GW c b t d dc dp u v e f (C, s.1.1) =
          l57gW4 (aggnL57GNode c dc dp (C, s.1.1)) := by
        unfold aggnL57GW; rw [if_pos hon]
      change j < aggnAggregateWidth c C + l57gW4 (aggnL57GNode c dc dp (C, s.1.1)) at hlt
      rw [← hw, hs] at hlt
      have := le_max_right (l57Calls (aggnL57Hdr c b t d dc dp (C, sR)))
        (aggnL57GW c b t d dc dp u v e f (C, sR))
      omega
    next => cases hJ
  next =>
    unfold aggnL57Child at hJ
    have h0 : aggnAggregateChild c (((C, none) : AggnPhaseNode), j, s.1.1) = none := by
      rw [hs]; exact aggnL57_agg_done hpost j
    rw [h0] at hJ
    change (if j < aggnAggregateWidth c C + l57Calls (aggnL57Hdr c b t d dc dp (C, s.1.1)) then
      _ else none) = some J at hJ
    split at hJ
    next hlt =>
      rw [hs] at hlt
      have := le_max_left (l57Calls (aggnL57Hdr c b t d dc dp (C, sR)))
        (aggnL57GW c b t d dc dp u v e f (C, sR))
      omega
    next => cases hJ

/-- **The calls of lines 5–7.** On a context with the hypotheses of Layer A, every tree the
round walks from `(C, none)` (with any condition at the steps, and calls that are coset
instances) makes at most `W + X` calls: `W` is the width of the two phases of
AggregateCertificates, and `X` bounds the calls of stretch 3 and of the giant branch at every
state the phases end in. -/
theorem l57Tree_calls_le [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hS : L57Setting c b t d dc dp u v e f n m C ϕ) {CM : ℕ → AggnL57GState → AggnPhaseNode → Prop}
    {w : ℕ} {T₀ : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatchS (aggnL57GRound c b t d dc dp u v e f) CM (aggnPhaseDecode n) (decCoset n)
      (C, none) w 0 ((aggnL57GRound c b t d dc dp u v e f).init (C, none)) T₀)
    (hans : ∀ K ∈ T₀.calls, ∃ a : RawCoset, decCoset n a = K.answer) (X : ℕ)
    (hX : ∀ sR, AggnL57Post c dc dp C ϕ sR →
      l57Calls (aggnL57Hdr c b t d dc dp (C, sR)) ≤ X ∧
        aggnL57GW c b t d dc dp u v e f (C, sR) ≤ X) :
    T₀.calls.length ≤ aggnAggregateWidth c C + X := by
  have hP := aggnL57G_stretch1 hS.ok hS.wf hS.ctx hS.set hS.large hS.tm hS.x hS.y 0
  have := LoopMatchK.calls_le_split (C := CM) (aggnAggregateWidth c C + X) hP ?_ hm hans
  · omega
  rintro - w' j' s' ⟨-, hj', -, hpost⟩ w'' T' hT' hans'
  have h := LoopMatchS.calls_le_of_inv (fun _ s => s.1.1 = s'.1.1)
    (aggnAggregateWidth c C + X)
    (fun j s J a hs _ => l57G_combine_keep hpost j s hs a)
    (fun j s J hs hJ => by
      have h1 := l57G_child_lt hpost j s hs J hJ
      obtain ⟨h2, h3⟩ := hX _ hpost
      have := max_le h2 h3
      omega) hT' rfl hans'
  rw [max_eq_right (by omega)] at h
  exact h


/-! ## The versions of `X(y)` after the two phases -/

/-- The count of Theorem 9.2.3 at arity `k` on at most `m` points. -/
def famBound (k m : ℕ) : ℕ := (m + 1) ^ k * (m * (outBound m + 1) + 1)

theorem famBound_mono {k m m' : ℕ} (h : m ≤ m') : famBound k m ≤ famBound k m' := by
  unfold famBound
  refine Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) k) ?_
  exact Nat.add_le_add_right (Nat.mul_le_mul h (Nat.add_le_add_right (outBound_mono h) 1)) 1

/-- **The versions of one restored design entry** (Theorem 9.2.3 on the entry, then the names
restored): at most `famBound k m` for arity `k` and at most `m` points. -/
theorem restoredEntryFamily_length_le {c t d m k : ℕ} (he : SbipExact t d) {dom : List ℕ}
    {a : AggnDesignEntry} (hrep : ExtendedInputRep (c + 1) a.1.length (a.2, (3, 4)))
    (hk : a.2.1.1.length = k) (hm : a.1.length ≤ m) :
    (aggnRestoredEntryFamily c 0 t d (dom, a)).length ≤ famBound k m := by
  unfold aggnRestoredEntryFamily aggnRestoreFamily aggnEntrySplitFamily
  rw [List.length_map]
  refine (extendedSplitFamily_length_le he hrep).trans ?_
  change famBound a.2.1.1.length a.1.length ≤ _
  rw [hk]
  exact famBound_mono hm

variable [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- **The versions of `X(y)` at a state the two phases end in**: one at outcome (1); at most
`m^5` restored entries of arity `2` at outcome (2b); one restored entry of arity `|C.2.2.2|`
(the test-set size) at outcome (3); none at the other exits. -/
theorem l57Versions_le (hS : L57Setting c 0 t d dc dp u v e f n m C ϕ) (he : SbipExact t d)
    {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR) :
    ((aggnContinuation c 0 t d (C, sR)).2.2).length ≤
      m ^ 5 * famBound 2 m + famBound C.2.2.2.length m + 1 := by
  have hC := hS.ctx
  have hm := hS.m217
  rcases aggnAggregateDispatch_cases (C, sR) with h | h | h
  · rw [aggnContinuation_of_one h]
    simp [aggnContCaseOne]
  · cases hg : aggnAggregateGiantBranch (C, sR)
    · cases hr : aggnRejectCase (C, sR)
      · rw [aggnContinuation_of_case2b h hg hr]
        change (aggnCase2bSplitFamily c 0 t d ((C, sR), true)).length ≤ _
        have hx : aggnSideCase2b ((C, sR), false) = true :=
          (aggnSideCase2b_false_iff C sR).mpr ⟨h, hg⟩
        have hy : aggnSideCase2b ((C, sR), true) = true := by
          simp only [aggnRejectCase, hx, Bool.true_and, Bool.not_eq_false'] at hr
          exact hr
        unfold aggnCase2bSplitFamily
        rw [List.length_flatMap]
        dsimp only
        have hle := List.sum_le_card_nsmul ((aggnCase2bEntries ((C, sR), true)).map
          (fun a => (aggnRestoredEntryFamily c 0 t d (C.1.2.1, a)).length))
          (famBound 2 m) (by
            intro v hv
            obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
            obtain ⟨hnd, hlt, -, hdata, -⟩ := aggnCase2bEntries_side_admissible hC hm hy ha
            refine restoredEntryFamily_length_le he
              (aggnCase2bEntries_side_split_input hC hm hy ha) ?_
              (length_le_of_nodup_lt hnd hlt)
            rw [hdata]; rfl)
        simp only [List.length_map, smul_eq_mul] at hle
        have hlen : (aggnCase2bEntries ((C, sR), true)).length ≤ m ^ 5 := by
          unfold aggnCase2bEntries
          rw [List.length_map]
          exact (aggnAggregateCase2b_side_facts hC hm hy).2.2
        have := Nat.mul_le_mul_right (famBound 2 m) hlen
        omega
      · rw [aggnContinuation_of_rejectCase h hg hr]; simp
    · rw [aggnContinuation_of_giant h hg]; simp
  · cases hr : aggnRejectDefect (C, sR)
    · rw [aggnContinuation_of_case3 h hr]
      unfold aggnContCase3
      cases hA : aggnGuideSplitFamilies c 0 t d (C, sR) with
      | none => simp
      | some A =>
        simp only
        unfold aggnGuideSplitFamilies aggnGuideEntries at hA
        cases hout : aggnAggregateGuide c (C, sR) with
        | none => rw [hout] at hA; simp at hA
        | some out =>
          rw [hout] at hA
          simp only [Option.map_some, Option.some.injEq] at hA
          subst hA
          haveI : Nonempty (Fin n) := hS.set.transitive.nonempty
          have hs := hpost.2.2.1
          have htbl := hpost.2.2.2.2
          set a := (aggnGuideEntryPair ((C, sR), out)).2 with ha
          obtain ⟨hnd, hlt, -, hdata, -⟩ :
              a.1.Nodup ∧ (∀ u ∈ a.1, u < m) ∧ 11 * m ≤ 15 * a.1.length ∧
                a.2.1 = (C.2.2.2, C.2.1, List.range a.1.length) ∧ _ :=
            aggnGuideEntries_admissible hC hs htbl hS.set hS.large hS.tm hout h true
          have hrep : ExtendedInputRep (c + 1) a.1.length (a.2, (3, 4)) :=
            aggnGuideEntries_split_input hC hs htbl hS.set hS.large hS.tm hout h true
          have hk : a.2.1.1.length = C.2.2.2.length := by rw [hdata]
          have := restoredEntryFamily_length_le (c := c) (dom := C.1.2.1) he hrep hk
            (length_le_of_nodup_lt hnd hlt)
          change (aggnRestoredEntryFamily c 0 t d (C.1.2.1, a)).length ≤ _
          omega
    · rw [aggnContinuation_of_rejectDefect h hr]; simp

/-- **The calls of stretch 3 at a state the two phases end in**: versions times
`Explicit.l4Factor n` (windows, or right cosets times orbits in case 1 of the repair). -/
theorem l57Calls_post_le (hS : L57Setting c 0 t d dc dp u v e f n m C ϕ) (he : SbipExact t d)
    {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR) :
    l57Calls (aggnL57Hdr c 0 t d dc dp (C, sR)) ≤
      (m ^ 5 * famBound 2 m + famBound C.2.2.2.length m + 1) * l4Factor n := by
  have hv := l57Versions_le hS he hpost
  have hN : C.1.1.1.length = n := hS.ctx.action.1
  have hh : aggnL57Hdr c 0 t d dc dp (C, sR) = aggnL57HdrCore c 0 t d (C, sR) := by
    unfold aggnL57Hdr; rw [hpost.1]
  rw [hh]
  set h := aggnL57HdrCore c 0 t d (C, sR) with hdef
  have h1 : h.1.1.1.length = n := hN
  have hw : h.2.2.2.1.length ≤ 2 * h.1.1.1.length + 1 :=
    length_alignL57Windows_le (C.1, aggnL57Fixed (aggnL57Cont c 0 t d (C, sR)))
  have hver : h.2.2.1.length ≤ m ^ 5 * famBound 2 m + famBound C.2.2.2.length m + 1 := hv
  rw [← h1]
  unfold l57Calls
  split
  · exact (adCalls_le_of h hw).trans (Nat.mul_le_mul_right _ hver)
  · exact (avCalls_le_of h hw).trans (Nat.mul_le_mul_right _ hver)

end L57


/-! ## Arithmetic -/

theorem famBound_le {x n k K : ℕ} (hx : x ≤ n) (hk : k ≤ K * lg n) :
    famBound k x ≤ 2 ^ ((K + 47) * lg n ^ 3) := by
  set L := lg n with hL
  have hL2 : 2 ≤ L := two_le_lg n
  have hn1 : n + 1 ≤ 2 ^ L := succ_le_two_pow_lg n
  have h1 : (x + 1) ^ k ≤ 2 ^ (L * (K * L)) :=
    (pow_le_two_pow_mul (by omega : x + 1 ≤ 2 ^ L) k).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk))
  have hB : outBound x + 1 ≤ 2 ^ (45 * L ^ 3 + 1) := by
    have := outBound_mono hx
    have e : outBound n = 2 ^ (45 * L ^ 3) := rfl
    rw [pow_succ]
    have : 1 ≤ 2 ^ (45 * L ^ 3) := Nat.one_le_two_pow
    omega
  have h2 : x * (outBound x + 1) + 1 ≤ 2 ^ (L + 45 * L ^ 3 + 1) := by
    have hm1 : x + 1 ≤ 2 ^ L := by omega
    calc x * (outBound x + 1) + 1 ≤ (x + 1) * (outBound x + 1) := by nlinarith
      _ ≤ 2 ^ L * 2 ^ (45 * L ^ 3 + 1) := Nat.mul_le_mul hm1 hB
      _ = 2 ^ (L + 45 * L ^ 3 + 1) := by rw [← pow_add]; ring_nf
  have hLL : L * (K * L) ≤ K * L ^ 3 := by
    have : L ^ 2 ≤ L ^ 3 := lg_pow_le_lg_pow (by norm_num) n
    calc L * (K * L) = K * L ^ 2 := by ring
      _ ≤ K * L ^ 3 := Nat.mul_le_mul_left _ this
  have hL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := lg_pow_le_lg_pow (by norm_num) n
  have h13 : 1 ≤ L ^ 3 := one_le_lg_pow n 3
  unfold famBound
  calc (x + 1) ^ k * (x * (outBound x + 1) + 1) ≤ 2 ^ (L * (K * L)) * 2 ^ (L + 45 * L ^ 3 + 1) :=
        Nat.mul_le_mul h1 h2
    _ = 2 ^ (L * (K * L) + (L + 45 * L ^ 3 + 1)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((K + 47) * L ^ 3) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem pow_le_two_pow_lg_cube {x n : ℕ} (hx : x ≤ n) (k : ℕ) :
    x ^ k ≤ 2 ^ (k * lg n ^ 3) := by
  have h := succ_le_two_pow_lg n
  have hL : lg n ≤ lg n ^ 3 := by
    calc lg n = lg n ^ 1 := (pow_one _).symm
      _ ≤ lg n ^ 3 := lg_pow_le_lg_pow (by norm_num) n
  calc x ^ k ≤ (2 ^ lg n) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ (lg n * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (k * lg n ^ 3) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-! ## The width of the two phases -/

theorem length_aggnPhaseRows_le (c : ℕ) (C : AggnPhaseCtx) :
    (aggnPhaseRows c C).length ≤ (C.1.2.1.length + 1) ^ C.2.2.2.length := by
  unfold aggnPhaseRows aggTestSetsOn
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_map]
  refine (length_aggTable_le c _).trans ?_
  simp only [List.length_range]
  exact le_rfl

theorem aggnAggregateWidth_eq (c : ℕ) (C : AggnPhaseCtx) :
    aggnAggregateWidth c C = 2 * (aggnPhaseRows c C).length * aggnJobWidth C +
      2 * ((aggnPhaseRows c C).length * (aggnPhaseRows c C).length) * (2 * aggnJobWidth C) := by
  unfold aggnAggregateWidth aggnPhaseWidth aggnCompareWidth aggnCompareJobWidth aggnPhaseJobs
    aggnCompareJobs aggnJobWidth
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_map, List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- **The width of the two phases of AggregateCertificates**, `2^{20 L²}`, for a context on
`N` points with `m ≤ N` points of the second domain and test sets of size `k ≤ min N (5L)`,
where `N + 1 ≤ 2^L`. -/
theorem aggnAggregateWidth_le_arith {c N m k L : ℕ} (C : AggnPhaseCtx) (hN : N + 1 ≤ 2 ^ L)
    (hm : m ≤ N) (hk : k ≤ N) (hkL : k ≤ 5 * L) (hL : 2 ≤ L)
    (h1 : C.2.1.length = N) (h2 : C.1.2.1.length = m) (h3 : C.2.2.2.length = k) :
    aggnAggregateWidth c C ≤ 2 ^ (20 * L ^ 2) := by
  have hR : (aggnPhaseRows c C).length ≤ 2 ^ (L * k) := by
    refine (length_aggnPhaseRows_le c C).trans ?_
    rw [h2, h3]
    exact pow_le_two_pow_mul (by omega) k
  have hfac : k.factorial ≤ 2 ^ (L * k) :=
    (Nat.factorial_le_pow k).trans (pow_le_two_pow_mul (by omega) k)
  have hJ : aggnJobWidth C ≤ 2 ^ (L * k + 2 * L) := by
    unfold aggnJobWidth
    rw [h1, h3]
    have hN' : N ≤ 2 ^ L := by omega
    calc N * (k.factorial * N) ≤ 2 ^ L * (2 ^ (L * k) * 2 ^ L) :=
          Nat.mul_le_mul hN' (Nat.mul_le_mul hfac hN')
      _ = 2 ^ (L * k + 2 * L) := by rw [← pow_add, ← pow_add]; ring_nf
  rw [aggnAggregateWidth_eq]
  set R := (aggnPhaseRows c C).length
  set J := aggnJobWidth C
  have hRR : R * R ≤ 2 ^ (L * k) * 2 ^ (L * k) := Nat.mul_le_mul hR hR
  have hR1 : R ≤ R * R ∨ R = 0 := by
    rcases Nat.eq_zero_or_pos R with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_right _ h)
  have hsum : 2 * R * J + 2 * (R * R) * (2 * J) ≤ 6 * (R * R) * J := by
    rcases hR1 with h | h
    · nlinarith
    · rw [h]; simp
  refine hsum.trans ?_
  have hX : 6 * (R * R) * J ≤ 2 ^ 3 * (2 ^ (L * k) * 2 ^ (L * k)) * 2 ^ (L * k + 2 * L) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hRR) hJ
  refine hX.trans ?_
  rw [← pow_add, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hk' : L * k ≤ L * (5 * L) := Nat.mul_le_mul_left _ hkL
  nlinarith


end Explicit

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv

theorem route5_arith {L Z a1 a2 a3 a4 a5 a6 : ℕ} (hL : 1 ≤ L ^ 3)
    (h1 : a1 ≤ 2 ^ (20 * L ^ 3)) (h2 : a2 ≤ 2 ^ (5 * L ^ 3)) (h3 : a3 ≤ 2 ^ (48 * L ^ 3))
    (h4 : a4 ≤ 2 ^ (52 * L ^ 3)) (h5 : a5 ≤ 2 ^ (5 * L ^ 3)) (h6 : a6 ≤ 2 ^ (Z * L ^ 3)) :
    a1 + ((a2 * a3 + a4 + 1) * a5 + a6) ≤ 2 ^ ((62 + Z) * L ^ 3) := by
  have e23 : 2 ^ (5 * L ^ 3) * 2 ^ (48 * L ^ 3) = 2 ^ (53 * L ^ 3) := by
    rw [← pow_add]; ring_nf
  have i23 : a2 * a3 ≤ 2 ^ (53 * L ^ 3) := e23 ▸ Nat.mul_le_mul h2 h3
  have i4 : a4 ≤ 2 ^ (53 * L ^ 3) := h4.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have i1 : 1 ≤ 2 ^ (53 * L ^ 3) := Nat.one_le_two_pow
  have iS : a2 * a3 + a4 + 1 ≤ 4 * 2 ^ (53 * L ^ 3) := by omega
  have eF : 2 ^ (53 * L ^ 3) * 2 ^ (5 * L ^ 3) = 2 ^ (58 * L ^ 3) := by rw [← pow_add]; ring_nf
  have iP : (a2 * a3 + a4 + 1) * a5 ≤ 4 * 2 ^ (58 * L ^ 3) := by
    rw [← eF, ← mul_assoc]; exact Nat.mul_le_mul iS h5
  have iA : a1 ≤ 2 ^ (58 * L ^ 3) :=
    h1.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have iFG : 2 ^ (58 * L ^ 3) ≤ 2 ^ ((58 + Z) * L ^ 3) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have i6 : a6 ≤ 2 ^ ((58 + Z) * L ^ 3) :=
    h6.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hsum : a1 + ((a2 * a3 + a4 + 1) * a5 + a6) ≤ 8 * 2 ^ ((58 + Z) * L ^ 3) := by omega
  refine hsum.trans ?_
  have e8 : 8 * 2 ^ ((58 + Z) * L ^ 3) = 2 ^ (3 + (58 + Z) * L ^ 3) := by rw [pow_add]; norm_num
  rw [e8]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

variable {cam : RawGens × List ℕ → Option RawCameron}

set_option maxHeartbeats 4000000 in
/-- **The calls of the run at a good node of route 5** (lines 5–7): at most
`2^{A (log₂ n+2)^3}`, from the tree the round of lines 5–7 walks (`Algo.exists_l57Tree`, through
`Algo.masterL57SupplyH_masterL57Hint`) and its count `Explicit.l57Tree_calls_le`: the two
phases of AggregateCertificates (`2^{O(log² n)}`), the versions of Theorem 9.2.3 times the
windows or cosets of stretch 3 (`2^{O(log³ n)}`), and the polynomial width of the giant branch. -/
theorem exists_calls_route5_le {p : Params} (ok : ParamsOK p) (he : SbipExact p.t p.d)
    (hc : PolyFun cam) (hs : CameronSpec cam) :
    ∃ A, ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 →
      masterRoute P = 5 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (A * lg n ^ 3) := by
  obtain ⟨B, C₀, a, b, e, f', u, v, u', v', tt, dd, t, d, dc, dp, E⟩ := p
  obtain ⟨⟨hB, hC₀⟩, htopwp, htop4w, ⟨hu', hv'⟩, hcap, hl4c, hentry, hbip, hphases, hreserve⟩ :=
    id ok
  dsimp only at hB hC₀ hu' hv' htopwp htop4w hcap hl4c hentry hbip hphases hreserve he ⊢
  subst hB hC₀ hu' hv'
  obtain ⟨q, hq, hT⟩ := exists_treesE ok hc hs
  obtain ⟨Y, hY⟩ := exists_size_le_of_wf a b
  obtain ⟨S, hSp, hSm, hSs⟩ := polyFun_masterL57Ctx.size.exists_polyBound
  obtain ⟨K, hKp, hKm, hKs⟩ := aggnL57GW_bdd 2 0 t d dc dp (l57UV e f').1 (l57UV e f').2 e f'
  obtain ⟨c₀, d₀, hc₀⟩ := hKp.comp hSp
  obtain ⟨Wc, -, -, hcw⟩ := aggnChecked_width_bound 2
  obtain ⟨Wp, -, -, hpw⟩ := aggnCompareChecked_width_bound 2
  refine ⟨62 + (c₀ + d₀ * (Y + 1)), fun n P f hG hWF hf hr => ?_⟩
  obtain ⟨W, o⟩ := P
  cases o with
  | none => simp [masterRoute] at hr
  | some h =>
  have hr' : masterHintRoute (W, h) = 5 := hr
  obtain ⟨⟨hdeg, hWW, hinv⟩, hgoodAll⟩ := id hG
  have hgood : MasterHintGood (W, h) := hgoodAll h rfl
  -- the tree of lines 5–7 and the tree of the node
  obtain ⟨T₀, hm, hK, hcos, hrun, hlet, -⟩ := masterL57SupplyH_masterL57Hint (E := E) hphases
    htopwp hentry hbip le_rfl hreserve hcw hpw n W h hG hr'
  have hmatch : ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam)
        (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
        ((masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam).width (W, some h)) 0
        ((masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam).init (W, some h)) T ∧
      T.run = (decWinSI n W).answer ∧ T.calls.length = T₀.calls.length :=
    masterNodeH_hint_line57_matchGood hWW hinv (hcap n) hreserve hr' hgood T₀ hm hK hcos hrun
      hlet
  obtain ⟨T, hmT, -, hlenT⟩ := hmatch
  set R := (masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v, (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam) with hRdef
  obtain ⟨-, h2, -⟩ := R.loopAux_eqG
    (rec := R.value f)
    (C := fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
    (Good := fun J => (masterRecE hq n (hT n)).Good J ∧ R.WF J ∧ R.measure J < R.measure (W, some h))
    (fun j s J hc hC => ⟨hC.1, R.child_wf _ j s J hWF hc, R.child_measure _ j s J hWF hc⟩)
    (fun J hJ => roundValue_eqG R (masterRecE hq n (hT n)).impl
      (masterRecE hq n (hT n)).progress.good_child (masterRecE hq n (hT n)).correct f J
      hJ.1 hJ.2.1 (lt_of_lt_of_le hJ.2.2 (Nat.lt_succ_iff.mp hf)))
    _ _ _ _ hmT
  have hlen : (R.roundCalls f (W, some h)).length = T₀.calls.length := by
    rw [← hlenT, ← h2, List.length_map]
    rfl
  rw [hlen]
  -- Layer A on the context
  obtain ⟨m, ϕ, -, -, hA, hGt, hϕ, -, -, -, -, hmn, h64⟩ := masterL57Ctx_hintFacts hgood
  have hmh : h.1.1.length = m := by
    have e := hA.2.1
    change (List.range h.1.1.length).length = m at e
    rwa [List.length_range] at e
  have hell : ellOf W.1.length < m := by
    rw [← hmh]
    exact ((masterHintRoute_aggregate (W, h)).1 hr').1
  obtain ⟨inst, hcat⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  have hts : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length = testSetSize W.1.length := by
    change (List.range (min (10 + Nat.log 2 W.1.length) W.1.length)).length = _
    rw [List.length_range]
    exact min_eq_left (testSetSize_le_self h64)
  have hS := l57Setting_of_normal (b := 0) (t := t) (d := d) (e := e) (f := f') hphases htopwp
    hentry hbip le_rfl (masterL57Ctx_normal hgood) hA (masterL57Ctx_strWF_x _)
    (masterL57Ctx_strWF_y _) hts hGt hϕ hmn h64 hell hcat
  have hans : ∀ K ∈ T₀.calls, ∃ a : RawCoset, decCoset W.1.length a = K.answer :=
    fun K hK => exists_rawCoset_answer (hcos K hK)
  set X := (m ^ 5 * famBound 2 m + famBound (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length m + 1) * l4Factor W.1.length +
    K (S (Enc.size ((W, some h) : RawMasterSI))) with hX
  have hcount := l57Tree_calls_le hS hm hans X (fun sR hpost =>
    ⟨(l57Calls_post_le hS he hpost).trans (Nat.le_add_right _ _),
      ((hKs (masterL57Ctx ((W, some h) : RawMasterSI)) sR).trans (hKm (hSs _))).trans (Nat.le_add_left _ _)⟩)
  refine hcount.trans ?_
  -- the arithmetic
  have hNn : W.1.length ≤ n := by
    exact length_le_of_nodup_lt hWW.1 hWW.2.1
  have hLN : lg W.1.length ≤ lg n := lg_mono hNn
  have hL2 : 2 ≤ lg n := two_le_lg n
  have hL3 : 1 ≤ lg n ^ 3 := one_le_lg_pow n 3
  have hk5 : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length ≤ 5 * lg W.1.length := by
    rw [hts]; unfold testSetSize lg; omega
  have hkN : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length ≤ W.1.length := by rw [hts]; exact testSetSize_le_self h64
  have i1 : aggnAggregateWidth 2 (masterL57Ctx ((W, some h) : RawMasterSI)) ≤ 2 ^ (20 * lg n ^ 3) := by
    refine (aggnAggregateWidth_le_arith (masterL57Ctx ((W, some h) : RawMasterSI)) (succ_le_two_pow_lg W.1.length) hmn hkN hk5 (two_le_lg W.1.length)
      (masterL57Ctx_length _) hA.2.1 rfl).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    exact Nat.mul_le_mul_left _ (lg_pow_mono hNn (by norm_num))
  have i2 : m ^ 5 ≤ 2 ^ (5 * lg n ^ 3) := pow_le_two_pow_lg_cube (hmn.trans hNn) 5
  have i3 : famBound 2 m ≤ 2 ^ (48 * lg n ^ 3) :=
    famBound_le (K := 1) (hmn.trans hNn) (by omega)
  have i4 : famBound (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length m ≤ 2 ^ (52 * lg n ^ 3) :=
    famBound_le (K := 5) (hmn.trans hNn) (hk5.trans (Nat.mul_le_mul_left _ hLN))
  have i5 : l4Factor W.1.length ≤ 2 ^ (5 * lg n ^ 3) :=
    (l4Factor_le W.1.length).trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (lg_pow_mono hNn le_rfl)))
  have i6 : K (S (Enc.size ((W, some h) : RawMasterSI))) ≤
      2 ^ ((c₀ + d₀ * (Y + 1)) * lg n ^ 3) := by
    have hsz : Enc.size ((W, some h) : RawMasterSI) ≤ 2 ^ (Y * lg n) := by
      have := hY _ hWF
      rwa [show masterDegree ((W, some h) : RawMasterSI) = n from hdeg] at this
    refine ((hc₀ _).trans (poly_comp_two_pow_lg hsz c₀ d₀)).trans ?_
    have h13 : lg n ≤ lg n ^ 3 := by
      calc lg n = lg n ^ 1 := (pow_one _).symm
        _ ≤ lg n ^ 3 := lg_pow_le_lg_pow (by norm_num) n
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h13)
  exact route5_arith hL3 i1 i2 i3 i4 i5 i6


/-- **The calls of the run at a good node, every route** (interface change R3): at most
`2^{6 (log₂ n+2)^4}` at route 1 (line 2, through the width), and `2^{Ap (log₂ n+2)^3}` at
every other route (routes 0, 2, 3, 4 through the width; route 5 through the tree of lines
5–7). -/
theorem exists_calls_bounds {p : Params} (ok : ParamsOK p) (he4 : SbipExact p.tt p.dd)
    (he5 : SbipExact p.t p.d) (hc : PolyFun cam) (hs : CameronSpec cam) :
    (∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P = 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (6 * (Nat.log 2 n + 2) ^ 4)) ∧
    ∃ Ap, ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P ≠ 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Ap * (Nat.log 2 n + 2) ^ 3) := by
  obtain ⟨A₀, h₀⟩ := exists_widthE_low_le p cam
  obtain ⟨A₅, h₅⟩ := exists_calls_route5_le ok he5 hc hs
  refine ⟨fun n P f hG hW _ hr => ?_, ⟨A₀ + 53 + A₅, fun n P f hG hW hf hr => ?_⟩⟩
  · have hdeg : masterDegree P = n := hG.1.1
    refine (length_roundCalls_le_width _ f P).trans ?_
    have := widthE_route1_le (cam := cam) hW hr
    rw [hdeg] at this
    exact this
  · have hdeg : masterDegree P = n := hG.1.1
    have hL3 : lg n ^ 2 ≤ lg n ^ 3 := lg_pow_le_lg_pow (by norm_num) n
    change _ ≤ 2 ^ ((A₀ + 53 + A₅) * lg n ^ 3)
    have hroute : masterRoute P = 0 ∨ masterRoute P = 2 ∨ masterRoute P = 3 ∨
        masterRoute P = 4 ∨ masterRoute P = 5 := by
      obtain ⟨W, o⟩ := P
      cases o with
      | none => exact Or.inl rfl
      | some h =>
        change masterHintRoute (W, h) ≠ 1 at hr
        change masterHintRoute (W, h) = 0 ∨ masterHintRoute (W, h) = 2 ∨
          masterHintRoute (W, h) = 3 ∨ masterHintRoute (W, h) = 4 ∨ masterHintRoute (W, h) = 5
        rcases masterHintRoute_mem (W, h) with h1 | h1 | h1 | h1 | h1 <;> omega
    rcases hroute with h4 | h4 | h4 | h4 | h4
    rotate_left 3
    · refine (length_roundCalls_le_width _ f P).trans ?_
      have := widthE_route4_le (cam := cam) he4 hG hW h4
      rw [hdeg] at this
      exact this.trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    · exact (h₅ n P f hG hW hf h4).trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    all_goals
      refine (length_roundCalls_le_width _ f P).trans ?_
      have := h₀ P hW (by omega)
      rw [hdeg] at this
      refine this.trans (Nat.pow_le_pow_right (by norm_num) ?_)
      calc A₀ * lg n ^ 2 ≤ A₀ * lg n ^ 3 := Nat.mul_le_mul_left _ hL3
        _ ≤ (A₀ + 53 + A₅) * lg n ^ 3 := Nat.mul_le_mul_right _ (by omega)

end Explicit
