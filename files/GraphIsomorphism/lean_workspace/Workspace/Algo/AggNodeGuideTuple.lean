import Workspace.Algo.AggNodeCosetTuple

/-! # Reading the Case 3 tuple relation from completed comparisons

The comparison phase fixes the source string and compares it with itself
and with the target. Normalize the supports of the two tuples to look up
the corresponding entry. Its induced coset and the prescribed-map test
then decide exactly the morphism relation used in Section 13.2.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

abbrev AggnGuideTupleInput := (RawAction × RawAggCompareTable) × AggnCompareJob

def aggnGuideTupleKey (p : AggnGuideTupleInput) : AggnCompareJob :=
  (p.2.1,aggNormalizeRow (p.1.1.2.1,p.2.2.1),aggNormalizeRow (p.1.1.2.1,p.2.2.2))

def aggnGuideTuple (p : AggnGuideTupleInput) : Bool :=
  aggnCosetTuple ((p.1.1.2.1,p.2.2),aggnCosetImage
    (p.1.1,(aggnCompareLookup (p.1.2,aggnGuideTupleKey p)).getD none))

private theorem fstP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem sndP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_guideTupleKey : PolyFun aggnGuideTupleKey := by
  have hi : PolyFun (fun p : AggnGuideTupleInput => p) := polyFun_id
  have hd := fstP (sndP (fstP (fstP hi)))
  exact (fstP (sndP hi)).pair
    (((hd.pair (fstP (sndP (sndP hi)))).comp aggPolyFun_normalizeRow).pair
      ((hd.pair (sndP (sndP (sndP hi)))).comp aggPolyFun_normalizeRow))

theorem aggnPolyFun_guideTuple : PolyFun aggnGuideTuple := by
  have hi : PolyFun (fun p : AggnGuideTupleInput => p) := polyFun_id
  have ha := fstP (fstP hi)
  have hq := ((sndP (fstP hi)).pair aggnPolyFun_guideTupleKey).comp aggnPolyFun_compareLookup
  have hget : PolyFun (fun q : Option RawCoset => q.getD none) :=
    (polyFun_id.pair (polyFun_const none)).comp polyFun_optionGetD
  exact (((fstP (sndP ha)).pair (sndP (sndP hi))).pair
    ((ha.pair (hq.comp hget)).comp aggnPolyFun_cosetImage)).comp aggnPolyFun_cosetTuple

theorem aggnNormalizeRow_name {m : ℕ} {dom row : List ℕ} (hd : dom.length = m) :
    aggNormalizeRow (dom,row) = aggName (winSet m row) := by
  unfold aggNormalizeRow aggName
  rw [hd]
  apply List.filter_congr
  intro a ha
  simp only [winSet,Set.mem_setOf_eq,dif_pos (List.mem_range.mp ha)]
  congr 1

theorem aggnName_phaseRow {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (T : Set (Fin m)) (hT : T.ncard = C.2.2.2.length) :
    aggName T ∈ aggnPhaseRows c C := by
  apply (aggMem_testSetsOn hC.guard (by rw [hC.action.2.1,hC.source]; exact hC.degree)).mpr
  exact ⟨(aggName_length T).trans hT,aggName_normal T C.1.2.1 hC.action.2.1⟩

/-- The executable test has no unproved local-map or lookup premise. -/
theorem aggnGuideTuple_spec {c n m : ℕ} {C : AggnPhaseCtx} {tbl : RawAggCompareTable}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (htbl : AggnCompareTableFor c ϕ tbl)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] (b : Bool) {u v : List ℕ}
    (hu : u.Nodup) (hv : v.Nodup) (hult : ∀ a ∈ u,a < m) (hvlt : ∀ a ∈ v,a < m)
    (hul : u.length = C.2.2.2.length) (hvl : v.length = C.2.2.2.length) :
    aggnGuideTuple ((C.1,tbl),(b,u,v)) = true ↔
      ∃ σ : decGroup n C.1.1.2,
        σ.val ∈ compareIso ϕ (decStrN n C.2.1)
          (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) (winSet m u) (winSet m v) ∧
        ∀ i : Fin u.length,ϕ σ (winPt m u hult i).val =
          (winPt m v hvlt (i.cast (hul.trans hvl.symm))).val := by
  have huc := (ncard_winSet u hu hult).trans hul
  have hvc := (ncard_winSet v hv hvlt).trans hvl
  have hkey : aggnGuideTupleKey ((C.1,tbl),(b,u,v)) =
      (b,aggName (winSet m u),aggName (winSet m v)) := by
    simp only [aggnGuideTupleKey,aggnNormalizeRow_name hC.action.2.1]
  have hj : aggnGuideTupleKey ((C.1,tbl),(b,u,v)) ∈ aggnCompareJobs c C := by
    rw [hkey,aggnCompareJob_mem]
    exact ⟨aggnName_phaseRow hC _ huc,aggnName_phaseRow hC _ hvc⟩
  obtain ⟨q,hq,hdec⟩ := aggnCompareLookup_spec htbl hj
  rw [hkey] at hdec
  simp only [aggnCompareValue,aggName_spec] at hdec
  have hsub : decCoset n q ⊆ (decGroup n C.1.1.2 : Set (Perm (Fin n))) := by
    rw [hdec]
    exact fun _ h => h.1
  have himage := aggnCosetImage_spec hC.action hsub
  have hmap : ∀ π ∈ decCoset m (aggnCosetImage (C.1,q)),π '' winSet m u = winSet m v := by
    rw [himage]
    rintro π ⟨σ,hσ,rfl⟩
    rw [hdec] at hσ
    obtain ⟨hG,hT⟩ := compareIso_testImage ϕ _ _ _ _ hset
      (by rw [huc]; exact ht) (by simpa only [huc,Nat.card_fin] using htm) (hvc.trans huc.symm) hσ
    exact hT
  rw [aggnGuideTuple,hq,Option.getD_some,
    aggnCosetTuple_spec hC.action.2.1 hu hv hult hvlt (hul.trans hvl.symm) hmap,himage]
  constructor
  · rintro ⟨π,⟨σ,hσ,rfl⟩,hcoords⟩
    exact ⟨σ,hdec ▸ hσ,hcoords⟩
  · rintro ⟨σ,hσ,hcoords⟩
    exact ⟨ϕ σ,⟨σ,hdec.symm ▸ hσ,rfl⟩,hcoords⟩

end Algo
