import Workspace.Algo.AggNodeCertPhase

/-! # Both completed certificate stores

The proof records the entries in execution order. Each entry is justified by
the completed local run. The two final stores keep their entries in reverse
order, since the raw update adds an entry at the front.
-/
namespace Algo
open Babai Equiv
open scoped Classical

abbrev AggnWrite := AggnJob × RawAggCert

def aggnStoreEntry (a : AggnJob) (e : RawAggCert) (stores : AggnStores) : AggnStores :=
  if a.1 then (stores.1, e :: stores.2) else (e :: stores.1, stores.2)

def aggnApplyEntries : List AggnWrite → AggnStores → AggnStores
  | [], stores => stores
  | w :: rest, stores => aggnApplyEntries rest (aggnStoreEntry w.1 w.2 stores)

noncomputable def AggnEntryFor {n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) (w : AggnWrite) : Prop :=
  w.2.1 = w.1.2 ∧ AggCertFor ϕ (decStrN n (aggnJobLoop C w.1).1.1) C.2.2.2.length w.2

section Match
variable {c n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- Theorem 13.1.3 supplies the fullness equivalence used by the raw store. -/
theorem aggnEntryFor_outStage (hC : AggnPhaseCtxWF c n m C ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    {a : AggnJob} (ha : a ∈ aggnPhaseJobs c C) {st : RawLCSt}
    (hs : StateFor (aggnJobCtx hC ha)
      (outStage ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2)) st) :
    AggnEntryFor ϕ (a, aggPack ((aggnJobLoop C a).1.1, a.2,
      lcOutOf ((aggnJobLoop C a).1, st))) := by
  have hd := aggnJob_data hC ha
  have hc : (winSet m a.2).ncard = C.2.2.2.length :=
    (ncard_winSet a.2 hd.1 hd.2.1).trans hd.2.2.1
  have hfull := (theorem_13_1_3 (ϕ := ϕ)
    (x := decStrN n (aggnJobLoop C a).1.1) (T := winSet m a.2)
    (hc ▸ ht) (by simpa only [hc, Nat.card_fin] using htm)).1
  refine ⟨rfl, ?_⟩
  have hp := aggPack_outStage hs hfull
  rwa [hd.2.2.1] at hp

/-- Sequence all the jobs in a supplied suffix of the fixed table. -/
theorem aggnPhase_sequence (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m) :
    ∀ (todo : List AggnJob), todo ⊆ aggnPhaseJobs c C → ∀ stores start,
      start + todo.length * aggnJobWidth C ≤ aggnPhaseWidth c C →
    PhaseMatch (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (todo.length * aggnJobWidth C) start (aggnPhaseScan c C todo stores)
      (SIReduction.sequence (todo.map (aggnJobTree ϕ)))
      (fun _ j v => ∃ writes, writes.map Prod.fst = todo ∧
        (∀ w ∈ writes, AggnEntryFor ϕ w) ∧
        v = aggnPhaseScan c C [] (aggnApplyEntries writes stores) ∧
        j ≤ start + todo.length * aggnJobWidth C) := by
  intro todo
  induction todo with
  | nil =>
    intro hsub stores start hb
    simp only [List.length_nil, Nat.zero_mul, List.map_nil, SIReduction.sequence]
    exact phaseMatch_done ⟨[], rfl, by simp, rfl, by omega⟩
  | cons a rest ih =>
    intro hsub stores start hb
    have ha := hsub List.mem_cons_self
    have hr : rest ⊆ aggnPhaseJobs c C := fun b hb => hsub (List.mem_cons_of_mem a hb)
    have hwidth : start + aggnJobWidth C ≤ aggnPhaseWidth c C := by
      simp only [List.length_cons, Nat.succ_mul] at hb
      omega
    have hm := aggnPhase_job hC hgiant ha rest stores start hwidth
    rw [List.map_cons, SIReduction.sequence, List.length_cons, Nat.succ_mul, Nat.add_comm]
    apply phaseMatch_bind hm
    rintro B j v ⟨st, hs, rfl, hB, hj⟩
    let e := aggPack ((aggnJobLoop C a).1.1, a.2, lcOutOf ((aggnJobLoop C a).1, st))
    have he : AggnEntryFor ϕ (a, e) := aggnEntryFor_outStage hC ht htm ha hs
    have hstore : aggnStoreJob a (aggnCertOpen c ((aggnJobLoop C a).1, st)) stores =
        aggnStoreEntry a e stores := rfl
    rw [hstore]
    have hjb : j + rest.length * aggnJobWidth C ≤ aggnPhaseWidth c C := by
      simp only [List.length_cons, Nat.succ_mul] at hb
      omega
    have htail := ih hr (aggnStoreEntry a e stores) j hjb
    have hend := phaseMatch_bind
      (P' := fun _ j' v' => ∃ writes : List AggnWrite,
        writes.map Prod.fst = a :: rest ∧ (∀ w ∈ writes, AggnEntryFor ϕ w) ∧
        v' = aggnPhaseScan c C [] (aggnApplyEntries writes stores) ∧
        j' ≤ start + (a :: rest).length * aggnJobWidth C)
      (k := fun bs => .done (B :: bs)) htail (by
        rintro bs j' v' ⟨ws, hw, hws, hv, hj'⟩
        apply phaseMatch_done
        refine ⟨(a, e) :: ws, by simp [hw], ?_, hv, ?_⟩
        · intro w hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact he
          · exact hws w hmem
        · simp only [List.length_cons, Nat.succ_mul]
          omega)
    simpa only [Nat.add_zero, List.length_cons, Nat.succ_mul, Nat.add_comm] using hend

end Match

/-- Select the store of one of the two strings. -/
def aggnStoreAt (stores : AggnStores) (b : Bool) : RawAggStore := cond b stores.2 stores.1

def aggnWritesAt (writes : List AggnWrite) (b : Bool) : RawAggStore :=
  (writes.filter (fun w => w.1.1 == b)).map Prod.snd

theorem aggnApplyEntries_at (writes : List AggnWrite) (stores : AggnStores) (b : Bool) :
    aggnStoreAt (aggnApplyEntries writes stores) b =
      (aggnWritesAt writes b).reverse ++ aggnStoreAt stores b := by
  induction writes generalizing stores with
  | nil => simp [aggnApplyEntries, aggnWritesAt]
  | cons w rest ih =>
    rw [aggnApplyEntries, ih]
    cases hb : b <;> cases hw : w.1.1 <;>
      simp [aggnStoreEntry, aggnStoreAt, aggnWritesAt, hb, hw, List.append_assoc]

theorem aggnWritesAt_keys {writes : List AggnWrite} {jobs : List AggnJob}
    (hkeys : writes.map Prod.fst = jobs) (he : ∀ w ∈ writes, w.2.1 = w.1.2) (b : Bool) :
    (aggnWritesAt writes b).map Prod.fst =
      (jobs.filter (fun a => a.1 == b)).map Prod.snd := by
  rw [← hkeys, List.filter_map, List.map_map, aggnWritesAt, List.map_map]
  apply List.map_congr_left
  intro w hw
  exact he w (List.mem_filter.mp hw).1

theorem aggnPhaseJobs_at (c : ℕ) (C : AggnPhaseCtx) (b : Bool) :
    ((aggnPhaseJobs c C).filter (fun a => a.1 == b)).map Prod.snd = aggnPhaseRows c C := by
  cases b <;> simp [aggnPhaseJobs, List.filter_map, List.map_map, Function.comp_def]

/-- The raw job order and the mathematical phase have exactly the same trees. -/
theorem aggnPhase_tree_eq {c n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) :
    SIReduction.sequence ((aggnPhaseJobs c C).map (aggnJobTree ϕ)) =
      certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          C.2.2.2 C.2.1 C.1.2.1) := by
  unfold certPhaseStrong certRunsStrong aggnPhaseJobs aggnRawCertEnum aggnCertEnum
  rw [List.map_flatMap]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro row hr
  cases b <;> rfl

/-- Correct, complete stores for both strings. -/
def AggnStoresComplete (c : ℕ) {n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) (stores : AggnStores) : Prop :=
  ∀ b, AggStoreFor ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length
      (aggnStoreAt stores b) ∧ AggComplete m C.2.2.2.length (aggnStoreAt stores b) ∧
    (aggnStoreAt stores b).map Prod.fst = (aggnPhaseRows c C).reverse

/-- Complete execution of the certificate phase, with the stores in the final state. -/
theorem aggnPhase_certificates {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m) :
    PhaseMatch (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnPhaseWidth c C) 0 ((aggnPhaseRound c n).init (C, none))
      (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          C.2.2.2 C.2.1 C.1.2.1))
      (fun _ _ v => v.1 = [] ∧ AggnStoresComplete c ϕ v.2.1) := by
  have hm := aggnPhase_sequence hC hgiant ht htm (aggnPhaseJobs c C)
    (List.Subset.refl _) ([], []) 0 (by simp [aggnPhaseWidth, aggnJobWidth])
  rw [aggnPhase_tree_eq] at hm
  apply phaseMatch_weaken hm
  rintro B j v ⟨writes, hkeys, hw, rfl, hj⟩
  refine ⟨rfl, ?_⟩
  intro b
  change AggStoreFor _ _ _ (aggnStoreAt (aggnApplyEntries writes ([], [])) b) ∧
    AggComplete _ _ (aggnStoreAt (aggnApplyEntries writes ([], [])) b) ∧
    (aggnStoreAt (aggnApplyEntries writes ([], [])) b).map Prod.fst = (aggnPhaseRows c C).reverse
  have hname : (aggnStoreAt (aggnApplyEntries writes ([], [])) b).map Prod.fst =
      (aggnPhaseRows c C).reverse := by
    rw [aggnApplyEntries_at]
    simp only [aggnStoreAt, Bool.cond_self, List.append_nil, List.map_reverse]
    rw [aggnWritesAt_keys hkeys (fun w h => (hw w h).1), aggnPhaseJobs_at]
  have hentries : ∀ e ∈ aggnStoreAt (aggnApplyEntries writes ([], [])) b,
      AggCertFor ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length e := by
    intro e he
    rw [aggnApplyEntries_at] at he
    simp only [aggnStoreAt, Bool.cond_self, List.append_nil, List.mem_reverse] at he
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp he
    obtain ⟨hmem, hb⟩ := List.mem_filter.mp hw'
    have hc := (hw w hmem).2
    have hb' : w.1.1 = b := beq_iff_eq.mp hb
    cases b <;> simpa only [aggnJobLoop, hb', Bool.cond_false, Bool.cond_true] using hc
  refine ⟨⟨?_, hentries⟩, ?_, hname⟩
  · rw [hname]
    exact List.nodup_reverse.mpr (aggNodup_testSetsOn (gdom := C.1.2.1) hC.guard)
  · intro T hT
    have hm : C.1.2.1.length ≤ C.2.1.length := by
      rw [hC.action.2.1, hC.source]; exact hC.degree
    have hr : aggName T ∈ aggnPhaseRows c C := by
      apply (aggMem_testSetsOn hC.guard hm).mpr
      exact ⟨(aggName_length T).trans hT, aggName_normal T C.1.2.1 hC.action.2.1⟩
    have hr' : aggName T ∈ (aggnStoreAt (aggnApplyEntries writes ([], [])) b).map Prod.fst := by
      rw [hname]; exact List.mem_reverse.mpr hr
    obtain ⟨e, he, hrow⟩ := List.mem_map.mp hr'
    exact ⟨e, he, hrow ▸ aggName_spec T⟩

end Algo
