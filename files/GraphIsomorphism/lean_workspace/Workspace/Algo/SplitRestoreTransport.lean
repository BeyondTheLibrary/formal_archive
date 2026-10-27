import Workspace.Algo.SplitOutcomeTransport
import Workspace.Algo.AggNodeRestorePartition

/-! Restoring names commutes with the original permutation. The two
stored lists may have different orders. Their local permutation is related
to the original permutation by the two name tables. -/
namespace Algo
open Babai RAM
open scoped Classical

noncomputable def splitNameEquiv {m k : ℕ} (D : List ℕ) (hn : D.Nodup)
    (hb : ∀ a ∈ D,a < m) (hd : D.length = k) : Fin k ≃ ↥(winSet m D) :=
  (finCongr hd.symm).trans (winEquiv m D hn hb)

theorem splitNameEquiv_val {m k : ℕ} (D : List ℕ) (hn : D.Nodup)
    (hb : ∀ a ∈ D,a < m) (hd : D.length = k) (i : Fin k) :
    (splitNameEquiv D hn hb hd i).val.val = rawGet (D,i.val) := by
  exact winPt_val D hb ((finCongr hd.symm) i)

theorem splitNameEquiv_partition_color {m k : ℕ} (D : List ℕ) (hn : D.Nodup)
    (hb : ∀ a ∈ D,a < m) (hd : D.length = k) (P : RawColPart) (i : Fin k) :
    (aggnLocalPartition m D hn hb P).color (splitNameEquiv D hn hb hd i) =
      labAt P.1 i.val := by
  change labAt P.1 ((winEquiv m D hn hb).symm
    (winEquiv m D hn hb ((finCongr hd.symm) i))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem splitNameEquiv_partition_part {m k : ℕ} (D : List ℕ) (hn : D.Nodup)
    (hb : ∀ a ∈ D,a < m) (hd : D.length = k) (P : RawColPart) (i j : Fin k) :
    (aggnLocalPartition m D hn hb P).part (splitNameEquiv D hn hb hd i)
      (splitNameEquiv D hn hb hd j) ↔ cellOf P i.val = cellOf P j.val := by
  change (cellOf P ((winEquiv m D hn hb).symm
    (winEquiv m D hn hb ((finCongr hd.symm) i))).val =
      cellOf P ((winEquiv m D hn hb).symm
        (winEquiv m D hn hb ((finCongr hd.symm) j))).val) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

theorem splitRestorePartition_iso {m k : ℕ} (D E : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (hn' : E.Nodup) (hb' : ∀ a ∈ E,a < m) (hd' : E.length = k)
    (π : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin k))
    (hf : ∀ i,(splitNameEquiv E hn' hb' hd' (f i)).val =
      π (splitNameEquiv D hn hb hd i).val)
    (dom dom' : List ℕ) (hm : dom.length = m) (hm' : dom'.length = m)
    (P Q : RawColPart) (hi : ColPartIso k P Q f) :
    RawSplitOutcomeIso m π (aggnRestoreOutcome ((dom,D),rawAlignPartition P))
      (aggnRestoreOutcome ((dom',E),rawAlignPartition Q)) := by
  let e := splitNameEquiv D hn hb hd
  let e' := splitNameEquiv E hn' hb' hd'
  have hiso : SplitOutcomeIso π
      ⟨winSet m D,Sum.inl (aggnLocalPartition m D hn hb P)⟩
      ⟨winSet m E,Sum.inl (aggnLocalPartition m E hn' hb' Q)⟩ := by
    refine ⟨e.symm.trans (f.trans e'),?_,?_,?_⟩
    · intro x
      change (e' (f (e.symm x))).val = π x.val
      have hh : (e' (f (e.symm x))).val = π (e (e.symm x)).val := hf (e.symm x)
      simpa only [Equiv.apply_symm_apply] using hh
    · intro x
      obtain ⟨i,rfl⟩ := e.surjective x
      change (aggnLocalPartition m E hn' hb' Q).color (e' (f (e.symm (e i)))) = _
      rw [Equiv.symm_apply_apply,splitNameEquiv_partition_color,splitNameEquiv_partition_color]
      exact hi.1 i
    · intro x y
      obtain ⟨i,rfl⟩ := e.surjective x
      obtain ⟨j,rfl⟩ := e.surjective y
      change (aggnLocalPartition m D hn hb P).part (e i) (e j) ↔
        (aggnLocalPartition m E hn' hb' Q).part
          (e' (f (e.symm (e i)))) (e' (f (e.symm (e j))))
      rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,
        splitNameEquiv_partition_part,splitNameEquiv_partition_part]
      exact hi.2 i j
  exact ⟨_,_,aggnRestorePartition_decode hn hb dom hm P,
    aggnRestorePartition_decode hn' hb' dom' hm' Q,hiso.extend⟩

noncomputable def splitNameJohnsonPoint {m k ms ts : ℕ} (D : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (J : RawJohnson) (hJ : J.WF k ms ts) (x : ↥(RawJohnson.carrier k J)) :
    ↥(RawJohnson.carrier m (aggnRestoreJohnson (D,J))) :=
  ⟨(splitNameEquiv D hn hb hd x.val).val,by
    apply List.mem_map.2
    exact ⟨x.val.val,x.property,(splitNameEquiv_val D hn hb hd x.val).symm⟩⟩

theorem splitNameJohnsonPoint_bijective {m k ms ts : ℕ} (D : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (J : RawJohnson) (hJ : J.WF k ms ts) :
    Function.Bijective (splitNameJohnsonPoint D hn hb hd J hJ) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (splitNameEquiv D hn hb hd).injective
    exact Subtype.ext (congrArg (fun z : ↥(RawJohnson.carrier m
      (aggnRestoreJohnson (D,J))) => z.val) h)
  · intro y
    obtain ⟨i,hi,hiy⟩ := List.mem_map.1 y.property
    refine ⟨⟨⟨i,hJ.wLt i hi⟩,hi⟩,Subtype.ext (Fin.ext ?_)⟩
    change (splitNameEquiv D hn hb hd ⟨i,hJ.wLt i hi⟩).val.val = y.val.val
    rw [splitNameEquiv_val]
    exact hiy

noncomputable def splitNameJohnsonEquiv {m k ms ts : ℕ} (D : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (J : RawJohnson) (hJ : J.WF k ms ts) :
    ↥(RawJohnson.carrier k J) ≃ ↥(RawJohnson.carrier m (aggnRestoreJohnson (D,J))) :=
  Equiv.ofBijective _ (splitNameJohnsonPoint_bijective D hn hb hd J hJ)

theorem splitNameJohnsonEquiv_val {m k ms ts : ℕ} (D : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (J : RawJohnson) (hJ : J.WF k ms ts) (x : ↥(RawJohnson.carrier k J)) :
    (splitNameJohnsonEquiv D hn hb hd J hJ x).val.val = rawGet (D,x.val.val) :=
  splitNameEquiv_val D hn hb hd x.val

theorem splitNameJohnsonEquiv_diff {m k ms ts : ℕ} (D : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (J : RawJohnson) (hJ : J.WF k ms ts) (x y : ↥(RawJohnson.carrier k J)) :
    rawJDiff (aggnRestoreJohnson (D,J),
      ((splitNameJohnsonEquiv D hn hb hd J hJ x).val.val,
       (splitNameJohnsonEquiv D hn hb hd J hJ y).val.val)) =
      rawJDiff (J,(x.val.val,y.val.val)) := by
  rw [splitNameJohnsonEquiv_val,splitNameJohnsonEquiv_val]
  exact aggnRestoreJohnson_diff hn hb (by simpa only [hd] using hJ) x.property y.property

theorem splitRestoreJohnson_iso {m k ms ts ms' ts' : ℕ} (D E : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (hn' : E.Nodup) (hb' : ∀ a ∈ E,a < m) (hd' : E.length = k)
    (π : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin k))
    (hf : ∀ i,(splitNameEquiv E hn' hb' hd' (f i)).val =
      π (splitNameEquiv D hn hb hd i).val)
    (dom dom' : List ℕ) (J J' : RawJohnson) (hJ : J.WF k ms ts)
    (hJ' : J'.WF k ms' ts')
    (hi : SplitOutcomeIso f (decAlignJohnson J hJ) (decAlignJohnson J' hJ')) :
    RawSplitOutcomeIso m π (aggnRestoreOutcome ((dom,D),rawAlignJohnson J))
      (aggnRestoreOutcome ((dom',E),rawAlignJohnson J')) := by
  have hw : J.WF D.length ms ts := by simpa only [hd] using hJ
  have hw' : J'.WF E.length ms' ts' := by simpa only [hd'] using hJ'
  refine ⟨_,_,aggnRestoreJohnson_decode hn hb hw dom,
    aggnRestoreJohnson_decode hn' hb' hw' dom',?_⟩
  obtain ⟨g,hg,hcol⟩ := hi
  let e := splitNameJohnsonEquiv D hn hb hd J hJ
  let e' := splitNameJohnsonEquiv E hn' hb' hd' J' hJ'
  refine ⟨e.symm.trans (g.trans e'),?_,?_⟩
  · intro x
    obtain ⟨i,rfl⟩ := e.surjective x
    change (e' (g (e.symm (e i)))).val = π (e i).val
    rw [Equiv.symm_apply_apply]
    change (splitNameEquiv E hn' hb' hd' (g i).val).val =
      π (splitNameEquiv D hn hb hd i.val).val
    rw [hg i]
    exact hf i.val
  · intro x y
    obtain ⟨i,rfl⟩ := e.surjective x
    obtain ⟨j,rfl⟩ := e.surjective y
    change rawJDiff (aggnRestoreJohnson (E,J'),
        ((e' (g (e.symm (e i)))).val.val,(e' (g (e.symm (e j)))).val.val)) =
      rawJDiff (aggnRestoreJohnson (D,J),((e i).val.val,(e j).val.val))
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,
      splitNameJohnsonEquiv_diff,splitNameJohnsonEquiv_diff]
    exact hcol i j

theorem splitRestoreOutcome_iso {m k : ℕ} (D E : List ℕ)
    (hn : D.Nodup) (hb : ∀ a ∈ D,a < m) (hd : D.length = k)
    (hn' : E.Nodup) (hb' : ∀ a ∈ E,a < m) (hd' : E.length = k)
    (π : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin k))
    (hf : ∀ i,(splitNameEquiv E hn' hb' hd' (f i)).val =
      π (splitNameEquiv D hn hb hd i).val)
    (dom dom' : List ℕ) (hm : dom.length = m) (hm' : dom'.length = m)
    {o o' : RawAlignOutcome} (hi : RawSplitOutcomeIso k f o o') :
    RawSplitOutcomeIso m π (aggnRestoreOutcome ((dom,D),o))
      (aggnRestoreOutcome ((dom',E),o')) := by
  obtain ⟨Z,Z',hz,hz',hi⟩ := hi
  rcases decAlignOutcome_cases hz with ⟨P,rfl,rfl⟩ | ⟨J,hJ,rfl,rfl⟩
  · rcases decAlignOutcome_cases hz' with ⟨Q,rfl,rfl⟩ | ⟨J',hJ',rfl,rfl⟩
    · exact splitRestorePartition_iso D E hn hb hd hn' hb' hd' π f hf dom dom' hm hm'
        P Q ((splitOutcomeIso_partition_iff f P Q).1 hi)
    · obtain ⟨e,_,he⟩ := hi
      exact he.elim
  · rcases decAlignOutcome_cases hz' with ⟨Q,rfl,rfl⟩ | ⟨J',hJ',rfl,rfl⟩
    · obtain ⟨e,_,he⟩ := hi
      exact he.elim
    · exact splitRestoreJohnson_iso D E hn hb hd hn' hb' hd' π f hf dom dom' J J' hJ hJ' hi

end Algo
