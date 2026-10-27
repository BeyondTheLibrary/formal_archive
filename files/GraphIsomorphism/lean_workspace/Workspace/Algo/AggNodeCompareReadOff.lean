import Workspace.Algo.AggNodeCompareBoundedMatch

/-! # Reading the stored comparison table

The phase retains cosets in reverse execution order. Reverse them once and
attach the fixed ordered-pair keys. The table gives the exact comparison
isomorphism set from Proposition 13.1.11 at every key.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- A matched phase's final value is the value of its exact reduction tree. -/
theorem aggnLoopMatchK_with_value {ι ω α Ω Λ β : Type*} {R : Round ι ω α}
    {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)} {I : ι}
    {w j : ℕ} {s : ω} {S : SIReduction Ω Λ β} {Q : β → ℕ → ℕ → ω → Prop}
    (h : LoopMatchK R decI decA I w j s S Q) :
    LoopMatchK R decI decA I w j s S (fun b w' j' s' => Q b w' j' s' ∧ b = S.run) := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b _ ⟨hQ, rfl⟩
  | call w j s J k Q hc hn ih =>
    exact .call w j s J k _ hc (fun a ha => ih a ha)

theorem aggnPhaseMatch_with_value {ι ω α Ω Λ β : Type*} {R : Round ι ω α}
    {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)} {I : ι}
    {fuel j : ℕ} {s : ω} {S : SIReduction Ω Λ β} {Q : β → ℕ → ω → Prop}
    (h : PhaseMatch R decI decA I fuel j s S Q) :
    PhaseMatch R decI decA I fuel j s S (fun b j' s' => Q b j' s' ∧ b = S.run) := by
  intro r
  exact loopMatchK_mono_Q (fun b w j s hb => ⟨hb.1.1, hb.1.2, hb.2⟩)
    (aggnLoopMatchK_with_value (h r))

abbrev RawAggCompareTable := List (AggnCompareJob × RawCoset)

def aggnCompareTable (c : ℕ) (z : AggnPhaseCtx × List RawCoset) : RawAggCompareTable :=
  (aggnCompareJobs c z.1).zip z.2.reverse

theorem aggnQuasiFun_compareTable (c : ℕ) : QuasiFun (aggnCompareTable c) :=
  ((polyFun_fst.comp_quasiFun (aggnQuasiFun_compareJobs c)).pair
    (polyFun_snd.comp polyFun_reverse).quasiFun).comp_poly polyFun_zip

noncomputable def aggnCompareValue {n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) (a : AggnCompareJob) : Set (Perm (Fin n)) :=
  compareIso ϕ (decStrN n C.2.1) (cond a.1 (decStrN n C.2.2.1) (decStrN n C.2.1))
    (winSet m a.2.1) (winSet m a.2.2)

def AggnCompareTableFor (c : ℕ) {n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) (tbl : RawAggCompareTable) : Prop :=
  tbl.map Prod.fst = aggnCompareJobs c C ∧
    ∀ e ∈ tbl, decCoset n e.2 = aggnCompareValue ϕ e.1

theorem aggnFullEnum_spec {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ) :
    (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      ((aggnPhaseRows c C).map (winSet m))).Spec ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        C.2.2.2.length := by
  refine ⟨aggnFullEnum_cover _ _ _ _, aggnFullEnum_bound _ _ _ ?_⟩
  exact (aggnRawCertEnum_spec c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
    hC.guard hC.action.2.1 (by rw [hC.source]; exact hC.degree)).toBound.tests

/-- The mathematical value at each ordered-pair key uses the paper's hypotheses. -/
theorem aggnComparePhase_run {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] :
    (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        ((aggnPhaseRows c C).map (winSet m)))).run =
      (aggnCompareJobs c C).map (aggnCompareValue ϕ) := by
  rw [run_comparePhaseStrong _ (aggnFullEnum_spec hC) hset ht
    (by simpa only [Nat.card_fin] using htm)]
  unfold aggnCompareJobs aggnFullEnum aggnCertEnum
  rw [List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  rw [List.flatMap_map, List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row hr
  rw [List.map_map, List.map_map]
  rfl

private theorem zip_decode {n : ℕ} (f : AggnCompareJob → Set (Perm (Fin n))) :
    ∀ (jobs : List AggnCompareJob) (qs : List RawCoset), qs.map (decCoset n) = jobs.map f →
      (jobs.zip qs).map Prod.fst = jobs ∧
        ∀ e ∈ jobs.zip qs, decCoset n e.2 = f e.1 := by
  intro jobs
  induction jobs with
  | nil => intro qs h; exact ⟨rfl, by simp⟩
  | cons a rest ih =>
    intro qs h
    cases qs with
    | nil => simp at h
    | cons q qs =>
      obtain ⟨hq, hqs⟩ := List.cons.inj h
      obtain ⟨hk, he⟩ := ih qs hqs
      refine ⟨by simp [hk], ?_⟩
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hq
      · exact he e he'

theorem aggnCompareTable_for {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} {answers : List RawCoset}
    (h : answers.reverse.map (decCoset n) = (aggnCompareJobs c C).map (aggnCompareValue ϕ)) :
    AggnCompareTableFor c ϕ (aggnCompareTable c (C, answers)) :=
  zip_decode (aggnCompareValue ϕ) _ _ h

/-- Completeness does not confuse an absent key with a stored empty comparison. -/
theorem AggnCompareTableFor.complete {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} {tbl : RawAggCompareTable}
    (h : AggnCompareTableFor c ϕ tbl) {a : AggnCompareJob} (ha : a ∈ aggnCompareJobs c C) :
    ∃ q, (a, q) ∈ tbl ∧ decCoset n q = aggnCompareValue ϕ a := by
  rw [← h.1] at ha
  obtain ⟨e, he, hkey⟩ := List.mem_map.mp ha
  exact ⟨e.2, by simpa only [← hkey, Prod.eta] using he, by simpa only [hkey] using h.2 e he⟩


/-- The runnable comparison phase produces a complete table of the paper's
comparison isomorphism sets, including correctly stored empty cosets. -/
theorem aggnCompareBounded_tables (c : ℕ) : ∃ d : ℕ,
    Nonempty (Round.RunCostQ (aggnCompareBoundedRound c d)) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnCompareCheckedRound c).WF (C, none) → AggnPhaseCtxWF c n m C ϕ →
      LocalCertSetting (decGroup n C.1.1.2) ϕ →
      LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      PhaseMatch (aggnCompareBoundedRound c d) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnCompareWidth c C) 0 ((aggnCompareBoundedRound c d).init (C, none))
        (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))))
        (fun _ _ v => v.1 = [] ∧ AggnCompareTableFor c ϕ (aggnCompareTable c (C, v.2.1))) := by
  obtain ⟨d, hcost, hm⟩ := aggnCompareBounded_comparisons c
  refine ⟨d, hcost, ?_⟩
  intro n m C ϕ hI hC hset ht htm hx hy
  have hk : 8 < C.2.2.2.length := by
    have hr : (8 : ℝ) < C.2.2.2.length := (le_max_left _ _).trans_lt ht
    exact_mod_cast hr
  letI : Nonempty (Fin n) := ⟨⟨0, by have := hC.arity; omega⟩⟩
  have hmatch := hm n m C ϕ hI hC hset.giant (by omega) hx hy
  apply phaseMatch_weaken (aggnPhaseMatch_with_value hmatch)
  rintro result j v ⟨⟨hempty, hdecode⟩, hrun⟩
  refine ⟨hempty, aggnCompareTable_for ?_⟩
  rw [hdecode, hrun, aggnComparePhase_run hC hset ht htm]

end Algo
