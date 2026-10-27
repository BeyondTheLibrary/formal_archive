import Workspace.Algo.AggNodeRecursiveEntries
import Workspace.Algo.SplitExtendedRunSpec

/-! The aggregate cases call the same Extended Design Lemma family at
threshold three quarters. The original degree controls the arity guard;
the giant-domain witness controls restoration to the input of Align. -/
namespace Algo
open Babai RAM RAM.Targets Equiv
open scoped Classical

def aggnEntrySplitFamily (c b t d : ℕ) (a : AggnDesignEntry) : List RawAlignOutcome :=
  extendedSplitFamily (c+1) b t d (a.2,(3,4))

def aggnRestoredEntryFamily (c b t d : ℕ) (p : List ℕ × AggnDesignEntry) :
    List RawAlignOutcome :=
  aggnRestoreFamily ((p.1,p.2.1),aggnEntrySplitFamily c b t d p.2)

theorem aggnQuasiFun_entrySplitFamily (c b t d : ℕ) : QuasiFun (aggnEntrySplitFamily c b t d) :=
  (polyFun_snd.pair (polyFun_const (3,4))).comp_quasiFun
    (quasiFun_extendedSplitFamily (c+1) b t d)

theorem aggnQuasiFun_restoredEntryFamily (c b t d : ℕ) : QuasiFun (aggnRestoredEntryFamily c b t d) :=
  (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).quasiFun).pair
    (polyFun_snd.comp_quasiFun (aggnQuasiFun_entrySplitFamily c b t d))).comp_poly
      aggnPolyFun_restoreFamily

theorem aggnGuard_succ (c n : ℕ) : guardBound c n ≤ guardBound (c+1) n := by
  unfold guardBound
  exact Nat.pow_le_pow_right (by omega) (Nat.le_succ c)

theorem aggnGuard_two {c n : ℕ} (hn : 2 ≤ n) : 2 ≤ guardBound (c+1) n := by
  have hlog : 1 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by omega) (by omega)).2 (by simpa using hn)
  have hh := Nat.pow_le_pow_right (n := Nat.log 2 n+1) (by omega) (show 1 ≤ c+1 by omega)
  simp only [pow_one] at hh
  exact (show 2 ≤ Nat.log 2 n+1 by omega).trans hh

theorem aggnCase2bEntries_split_input {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false)
    {a : AggnDesignEntry} (ha : a ∈ aggnCase2bEntries ((C,s),false)) :
    ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) := by
  obtain ⟨_,_,_,hdata,hsize,hdef⟩ := aggnCase2bEntries_admissible hC hm hcase hgiant ha
  have hk : a.2.1.1 = [0,1] := congrArg Prod.fst hdata
  refine ⟨?_,?_,?_,by norm_num,by norm_num [sbipAlphaValue],by norm_num [sbipAlphaValue],?_,?_,?_⟩
  · rw [hdata]; exact List.nodup_range
  · intro i; rw [hdata]; exact List.mem_range
  · rw [hdata]
    apply aggnGuard_two
    rw [hC.source]
    have hh := hC.degree
    omega
  · simpa only [hk,List.length_cons,List.length_nil] using (le_refl 2)
  · simpa only [hk,List.length_cons,List.length_nil] using hsize
  · change 1-sbipAlphaValue (3,4) < (defect (decRel a.1.length a.2.1.1.length a.2.2).Aut : ℝ)
    rw [hk]
    norm_num only [List.length_cons,List.length_nil,sbipAlphaValue,Nat.cast_ofNat]
    exact hdef

theorem aggnGuideEntries_split_input {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (hcase : aggnAggregateDispatch (C,s) = 3)
    (b : Bool) :
    let a := cond b (aggnGuideEntryPair ((C,s),out)).2 (aggnGuideEntryPair ((C,s),out)).1
    ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) := by
  dsimp only
  let a := cond b (aggnGuideEntryPair ((C,s),out)).2 (aggnGuideEntryPair ((C,s),out)).1
  obtain ⟨_,_,_,hdata,hsize,hkn,hdef⟩ :=
    aggnGuideEntries_admissible hC hs htbl hset ht htm hout hcase b
  change a.2.1 = _ at hdata
  have hk : a.2.1.1 = C.2.2.2 := congrArg Prod.fst hdata
  change ExtendedInputRep (c+1) a.1.length (a.2,(3,4))
  refine ⟨?_,?_,?_,by norm_num,by norm_num [sbipAlphaValue],by norm_num [sbipAlphaValue],?_,?_,?_⟩
  · rw [hdata]; exact List.nodup_range
  · intro i; rw [hdata]; exact List.mem_range
  · rw [hdata]; exact hC.guard.trans (aggnGuard_succ c C.2.1.length)
  · simpa only [hk] using hsize
  · simpa only [hk] using hkn
  · have hd : (1/2 : ℝ) < (defect (decRel a.1.length C.2.2.2.length a.2.2).Aut : ℝ) := by
      change (1/2 : ℚ) < defect (decRel a.1.length C.2.2.2.length a.2.2).Aut at hdef
      have hh := (Rat.cast_lt (K := ℝ)).2 hdef
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
      exact hh
    change 1-sbipAlphaValue (3,4) < (defect (decRel a.1.length a.2.1.1.length a.2.2).Aut : ℝ)
    rw [hk]
    simp only [sbipAlphaValue]
    norm_num only [Nat.cast_ofNat]
    linarith

/-- One computed restored family supplies actual Align outcomes at the
partition threshold 3/4 or Johnson threshold 11/20. -/
theorem exists_aggnRestoredEntryFamily_valid (c b : ℕ) :
    ∃ t d,QuasiFun (aggnRestoredEntryFamily c b t d) ∧
      ∀ m dom (a : AggnDesignEntry),dom.length = m →
        a.1.Nodup → (∀ u ∈ a.1,u < m) → 11*m ≤ 15*a.1.length →
        ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) →
        (∃ o,o ∈ aggnRestoredEntryFamily c b t d (dom,a)) ∧
        ∀ o ∈ aggnRestoredEntryFamily c b t d (dom,a),∃ β Z,
          decAlignOutcome m o = some Z ∧ 1/2 < β ∧ 0 ≤ β ∧ 5*β ≤ 4 ∧
            IsSplitOutcome β Set.univ Z := by
  obtain ⟨t,d,_,hsolver⟩ := exists_extendedSplitFamily_valid (c+1) b
  refine ⟨t,d,aggnQuasiFun_restoredEntryFamily c b t d,?_⟩
  intro m dom a hdom hnd hlt hlarge hI
  obtain ⟨hne,hgood⟩ := hsolver a.1.length (a.2,(3,4)) hI
  constructor
  · obtain ⟨o,ho⟩ := hne
    exact ⟨_,List.mem_map_of_mem ho⟩
  · intro o ho
    obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
    obtain ⟨Z,hdec,hZ⟩ := hgood p hp
    exact aggnRestoreOutcome_valid hnd hlt hlarge dom hdom hdec hZ

end Algo
