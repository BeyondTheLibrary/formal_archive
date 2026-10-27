import Workspace.Algo.AggCanonSort
import Workspace.Algo.AggNodeEnum
import Workspace.Algo.AggregateTable

/-! # Materializing the canonical representative order

The guarded tuple table supplies enough entries for the image group. Its
construction uses `QuasiFun.iterateSetup`. Truncating that stored list bounds
the later scan even if the stored index is malformed.
-/

namespace Algo

open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

/-- A quasipolynomial list that bounds the binary representative index. -/
def aggkRepFuel (c : ℕ) (p : RawLCLoop) : List ℕ :=
  (List.range (aggTable c (p.1.2, p.1.1, p.1.2)).2.length).take (lcIdx p)

def aggkRepAt (p : RawLCLoop × ℕ) : RawPerm :=
  lcRep (lcInst p.1).1 (p.1.1.2, p.1.2.2.2) p.2

/-- Convert image ranks on `T` back to the names in the test-set witness. -/
def aggkRepKey (p : RawLCLoop × RawPerm) : List ℕ :=
  nbrCols p.1.1.2 (rawImgOf (lcAct p.1, p.2))

def aggkRepRow (p : RawLCLoop × ℕ) : AggkRow :=
  (aggkRepKey (p.1, aggkRepAt p), aggkRepAt p)

def aggkRepRows (c : ℕ) (p : RawLCLoop) : List AggkRow :=
  (aggkRepFuel c p).map (fun j => aggkRepRow (p, j))

/-- Sec. 13.1, lines 04c--04d, with a generator-independent coset order. -/
def aggkRawReps (c : ℕ) (p : RawLCLoop) : RawGens :=
  (aggkSortRows (aggkRepRows c p)).map Prod.snd

theorem aggkQuasiFun_repFuel (c : ℕ) : QuasiFun (aggkRepFuel c) := by
  have hinput : PolyFun (fun p : RawLCLoop => (p.1.2, p.1.1, p.1.2)) :=
    polyFun_lcTdom.pair (polyFun_lcStr.pair polyFun_lcTdom)
  have hrows := (hinput.quasiFun.comp (aggQuasiFun_table c)).comp_poly
    (polyFun_snd.comp polyFun_rangeLength)
  exact ((hrows.pair polyFun_lcIdx.quasiFun).comp_poly polyFun_take).of_eq (fun _ => rfl)

theorem aggkPolyFun_repAt : PolyFun aggkRepAt := by
  have htd : PolyFun (fun p : RawLCLoop × ℕ => (p.1.1.2, p.1.2.2.2)) :=
    (polyFun_fst.comp polyFun_lcTdom).pair (polyFun_fst.comp polyFun_lcImgsOf)
  exact ((htd.pair polyFun_snd).pair
    (polyFun_fst.comp (polyFun_lcInst.comp polyFun_fst))).comp polyFun_lcRep

theorem aggkPolyFun_repKey : PolyFun aggkRepKey :=
  ((polyFun_fst.comp polyFun_lcTdom).pair
    (((polyFun_fst.comp polyFun_lcAct).pair polyFun_snd).comp polyFun_rawImgOf)).comp
    polyFun_nbrCols

theorem aggkPolyFun_repRow : PolyFun aggkRepRow :=
  ((polyFun_fst.pair aggkPolyFun_repAt).comp aggkPolyFun_repKey).pair aggkPolyFun_repAt

theorem aggkQuasiFun_repRows (c : ℕ) : QuasiFun (aggkRepRows c) :=
  (polyFun_id.quasiFun.pair (aggkQuasiFun_repFuel c)).comp_poly
    (PolyFun.mapParam aggkPolyFun_repRow)

theorem aggkQuasiFun_rawReps (c : ℕ) : QuasiFun (aggkRawReps c) :=
  ((aggkQuasiFun_repRows c).comp_poly aggkPolyFun_sortRows).comp_poly
    (PolyFun.map polyFun_snd)

theorem aggkRepFuel_eq {c : ℕ} {p : RawLCLoop}
    (hg : p.1.2.length ≤ guardBound c p.1.1.length)
    (hi : lcIdx p ≤ Nat.factorial p.1.2.length) :
    aggkRepFuel c p = List.range (lcIdx p) := by
  rw [aggkRepFuel, aggTable_of_guard hg, tupleTable, List.length_map, length_tuplesOf]
  have h := hi.trans (Nat.factorial_le_pow _)
  simp only [List.take_range, Nat.min_eq_left h]

section ImageLists

variable {n m : ℕ} {Λ : Type*} {G : Subgroup (Perm (Fin n))}
  {ϕ : G →* Perm (Fin m)} {x : Fin n → Λ} {T : Set (Fin m)}

/-- A total image map. Its value outside the stage group is never used. -/
noncomputable def aggkImageOf (s : Stage ϕ x T) (σ : Perm (Fin n)) : imgOn ϕ T s.le :=
  if hσ : σ ∈ s.H then ⟨psiOn ϕ T s.le ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩⟩ else 1

theorem aggkImageOf_coe (s : Stage ϕ x T) {σ : Perm (Fin n)} (hσ : σ ∈ s.H) :
    (aggkImageOf s σ : Perm T) = psiOn ϕ T s.le ⟨σ, hσ⟩ := by
  rw [aggkImageOf, dif_pos hσ]

theorem aggkRep_mem_of_cover (s : Stage ϕ x T) (L : List (Perm (Fin n)))
    (hc : (s.H : Set (Perm (Fin n))) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm (Fin n))))
    {σ : Perm (Fin n)} (hσ : σ ∈ L) : σ ∈ s.H := by
  change σ ∈ (s.H : Set (Perm (Fin n)))
  rw [hc]
  exact Set.mem_iUnion₂.mpr ⟨σ, hσ, ⟨1, one_mem _, by simp⟩⟩

theorem aggkImagesOf_surjective (s : Stage ϕ x T) (L : List (Perm (Fin n)))
    (hc : (s.H : Set (Perm (Fin n))) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm (Fin n))))
    (b : imgOn ϕ T s.le) : b ∈ L.map (aggkImageOf s) := by
  obtain ⟨hb, heb⟩ := certLift_spec s b
  have hb' : certLift s b ∈ (s.H : Set (Perm (Fin n))) := hb
  rw [hc] at hb'
  obtain ⟨σ, hσ, hcos⟩ := Set.mem_iUnion₂.mp hb'
  have hσH := aggkRep_mem_of_cover s L hc hσ
  rw [aggkCoset_eq_fiber s σ hσH] at hcos
  obtain ⟨hb'', he⟩ := hcos
  refine List.mem_map.mpr ⟨σ, hσ, ?_⟩
  apply Subtype.ext
  rw [aggkImageOf_coe s hσH, ← he]
  exact heb

/-- Covering every image with exactly the image order leaves no repetitions. -/
theorem aggkImagesOf_perm (s : Stage ϕ x T) (L : List (Perm (Fin n)))
    (hc : (s.H : Set (Perm (Fin n))) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm (Fin n))))
    (hl : L.length = Nat.card (imgOn ϕ T s.le)) :
    (L.map (aggkImageOf s)).Perm (Finset.univ : Finset (imgOn ϕ T s.le)).toList := by
  have hp := List.subperm_of_subset (Finset.nodup_toList (Finset.univ : Finset (imgOn ϕ T s.le)))
    (fun b _ => aggkImagesOf_surjective s L hc b)
  exact (hp.perm_of_length_le (by simp [hl, Nat.card_eq_fintype_card])).symm

/-- A sorted image list determines the coset list, without fixing any lifts. -/
theorem aggkCosetList_eq (s : Stage ϕ x T) (tdom : List T) (ht : ∀ u, u ∈ tdom)
    (L : List (Perm (Fin n)))
    (hc : (s.H : Set (Perm (Fin n))) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm (Fin n))))
    (hl : L.length = Nat.card (imgOn ϕ T s.le))
    (hs : (L.map (fun σ => aggkImageKey tdom (aggkImageOf s σ))).SortedLE) :
    L.map (fun σ => σ • (kerN s : Set (Perm (Fin n)))) =
      (aggkCanonReps s tdom).map (fun σ => σ • (kerN s : Set (Perm (Fin n)))) := by
  have himages : L.map (aggkImageOf s) = aggkImages s tdom := by
    apply List.Perm.eq_of_pairwise
      (le := fun a b : imgOn ϕ T s.le => aggkImageKey tdom a ≤ aggkImageKey tdom b)
    · intro a b _ _ hab hba
      exact Subtype.ext (aggkImageKey_injective tdom ht (le_antisymm hab hba))
    · simpa only [List.map_map, List.pairwise_map] using hs.pairwise
    · exact List.pairwise_map.mp (aggkImages_sorted s tdom).pairwise
    · exact (aggkImagesOf_perm s L hc hl).trans (List.mergeSort_perm _ _).symm
  have hlifts : L.map (fun σ => σ • (kerN s : Set (Perm (Fin n)))) =
      (L.map (aggkImageOf s)).map (fun b => certLift s b • (kerN s : Set (Perm (Fin n)))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro σ hσ
    have hσH := aggkRep_mem_of_cover s L hc hσ
    obtain ⟨hb, he⟩ := certLift_spec s (aggkImageOf s σ)
    exact aggkCoset_eq_of_image_eq s hσH hb ((aggkImageOf_coe s hσH).symm.trans he.symm)
  rw [hlifts, himages, aggkCanonReps, List.map_map]
  rfl

end ImageLists

section Stage

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}

/-- The raw test-set witness, read as a list of points of the mathematical set. -/
noncomputable def aggkTypedT (hc : LCCtxWF n m xs tdom) : List (winSet m tdom) :=
  List.ofFn (tName m tdom hc.nodup hc.ltM)

theorem aggkTypedT_complete (hc : LCCtxWF n m xs tdom) (u : winSet m tdom) :
    u ∈ aggkTypedT hc := by
  obtain ⟨i, rfl⟩ := (tName m tdom hc.nodup hc.ltM).surjective u
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem aggkRepKey_eq (h : StateFor hc s st) {r : RawPerm}
    (hr : RawPerm.WF n r) (hmem : decPerm n r ∈ s.H) :
    aggkRepKey (((xs, tdom), st), r) =
      aggkImageKey (aggkTypedT hc) (aggkImageOf s (decPerm n r)) := by
  have hm : decPerm n r ∈ decGroup n st.2.1 := h.grp.symm ▸ hmem
  rw [aggkRepKey, rawImgOf_state h hr hm,
    psiFin_congr hc.nodup hc.ltM h.le s.le hm hmem,
    aggkImageOf_coe s hmem, aggkImageKey, aggkTypedT, nbrCols, encPerm,
    List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_def]
  rw [psiFin_apply, winEquiv_symm_val]

theorem aggkIdx_eq_card (h : StateFor hc s st) :
    lcIdx ((xs, tdom), st) = Nat.card (imgOn ϕ (winSet m tdom) s.le) := by
  have he : lcIdx ((xs, tdom), st) =
      Nat.card (psiFin ϕ tdom hc.nodup hc.ltM h.le).range :=
    lcWidth_eq_card_range (lcwf_lcInst h) rfl (h.himgs h.le)
  rw [range_psiFin (hH := h.le)] at he
  have hcard := Nat.card_congr
    (Subgroup.equivMapOfInjective (imgOn ϕ (winSet m tdom) h.le)
      (tName m tdom hc.nodup hc.ltM).symm.permCongrHom.toMonoidHom
      (tName m tdom hc.nodup hc.ltM).symm.permCongrHom.injective).toEquiv
  rw [← hcard, imgOn_congr h.grp h.le s.le] at he
  exact he

theorem aggkRepFuel_stage (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    aggkRepFuel c ((xs, tdom), st) = List.range (lcIdx ((xs, tdom), st)) :=
  aggkRepFuel_eq hg (lcWidth_le_factorial (lcwf_lcInst h) rfl (h.himgs h.le))

theorem aggkRepRows_decode (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    (aggkRepRows c ((xs, tdom), st)).map (fun r => decPerm n r.2) =
      aggrReps n (aggrInputOf ((xs, tdom), st)) := by
  rw [aggkRepRows, aggkRepFuel_stage c h hg, List.map_map]
  rfl

theorem aggkRepRows_key (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    ∀ r ∈ aggkRepRows c ((xs, tdom), st),
      r.1 = aggkImageKey (aggkTypedT hc) (aggkImageOf s (decPerm n r.2)) := by
  intro r hr
  have hmem : decPerm n r.2 ∈ aggrReps n (aggrInputOf ((xs, tdom), st)) := by
    rw [← aggkRepRows_decode c h hg]
    exact List.mem_map_of_mem hr
  have hm := aggkRep_mem_of_cover s _ (aggrStage_cover h).cosets hmem
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact aggkRepKey_eq h (wf_lcRep (lcwf_lcInst h) i) hm

theorem aggkRepRows_nodup (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    (aggkRepRows c ((xs, tdom), st)).Nodup := by
  have hp := aggkImagesOf_perm s _ (aggrStage_cover h).cosets
    (by rw [aggrReps, length_lcPerms]; exact aggkIdx_eq_card h)
  have hn := hp.nodup_iff.mpr (Finset.nodup_toList _)
  rw [← aggkRepRows_decode c h hg] at hn
  exact List.Nodup.of_map _ (List.Nodup.of_map _ hn)


theorem aggkRawReps_perm (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    ((aggkRawReps c ((xs, tdom), st)).map (decPerm n)).Perm
      (aggrReps n (aggrInputOf ((xs, tdom), st))) := by
  have hp := (aggkSortRows_perm (aggkRepRows_nodup c h hg)).map
    (fun r : AggkRow => decPerm n r.2)
  have he := aggkRepRows_decode c h hg
  have hp' := hp.trans (List.Perm.of_eq he)
  simpa only [aggkRawReps, List.map_map] using hp'

theorem aggkRawReps_sorted (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    (((aggkRawReps c ((xs, tdom), st)).map (decPerm n)).map
      (fun σ => aggkImageKey (aggkTypedT hc) (aggkImageOf s σ))).SortedLE := by
  let rows := aggkRepRows c ((xs, tdom), st)
  have hkey := aggkRepRows_key c h hg
  have hs := aggkSortRows_sorted (rows := rows) (k := tdom.length) (by
    intro r hr
    rw [hkey r hr]
    simp only [aggkImageKey, aggkTypedT, List.length_map, List.length_ofFn])
  have he : (aggkSortRows rows).map (fun r =>
      aggkImageKey (aggkTypedT hc) (aggkImageOf s (decPerm n r.2))) =
      (aggkSortRows rows).map Prod.fst :=
    List.map_congr_left fun r hr => (hkey r ((aggkMem_sortRows rows r).mp hr)).symm
  change (((aggkSortRows rows).map Prod.snd |>.map (decPerm n)).map _).SortedLE
  simpa only [List.map_map, Function.comp_def, he] using hs

/-- The raw routine and the mathematical list have exactly the same cosets, in order. -/
theorem aggkRawReps_cosets (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    ((aggkRawReps c ((xs, tdom), st)).map (decPerm n)).map
      (fun σ => σ • (kerN s : Set (Perm (Fin n)))) =
      (aggkCanonReps s (aggkTypedT hc)).map
        (fun σ => σ • (kerN s : Set (Perm (Fin n)))) := by
  let L := (aggkRawReps c ((xs, tdom), st)).map (decPerm n)
  have hp := aggkRawReps_perm c h hg
  have hcover : (s.H : Set (Perm (Fin n))) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm (Fin n))) := by
    calc
      _ = ⋃ σ ∈ aggrReps n (aggrInputOf ((xs, tdom), st)),
          σ • (kerN s : Set (Perm (Fin n))) := (aggrStage_cover h).cosets
      _ = _ := by
        ext σ
        simp only [Set.mem_iUnion, ← hp.mem_iff]
        rfl
  have hlen : L.length = Nat.card (imgOn ϕ (winSet m tdom) s.le) :=
    hp.length_eq.trans ((length_lcPerms _ _ _).trans (aggkIdx_eq_card h))
  exact aggkCosetList_eq s (aggkTypedT hc) (aggkTypedT_complete hc) L hcover hlen
    (aggkRawReps_sorted c h hg)

end Stage

end Algo
