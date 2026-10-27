import Workspace.Algo.SplitBipDictionary

/-! A table vertex can be a singleton block outside the first part.
To restore all ambient point colors, we look up singleton rows in the
complete vertex dictionary. A point whose singleton is absent receives
the case's specified padding color. -/
namespace Algo
open Babai RAM

abbrev RawSbipColorRead := (List (List ℕ) × RawLab) × ℕ

def sbipDictColorRow (z : RawLab × (List ℕ × ℕ)) : List ℕ × ℕ :=
  (z.2.1,labAt z.1 z.2.2)

def sbipDictColorTable (z : List (List ℕ) × RawLab) : List (List ℕ × ℕ) :=
  z.1.zipIdx.map (fun p => sbipDictColorRow (z.2,p))

def sbipSingletonColor (z : RawSbipColorRead × ℕ) : ℕ :=
  ((sbipDictColorTable z.1.1).lookup [z.2]).getD z.1.2

def sbipPointColors (z : List ℕ × RawSbipColorRead) : RawLab :=
  (List.range z.1.length).map (fun u => sbipSingletonColor (z.2,u))

theorem polyFun_sbipDictColorRow : PolyFun sbipDictColorRow :=
  (polyFun_snd.comp polyFun_fst).pair
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_labAt)

theorem polyFun_sbipDictColorTable : PolyFun sbipDictColorTable :=
  (polyFun_snd.pair (polyFun_fst.comp polyFun_zipIdx)).comp
    (PolyFun.mapParam polyFun_sbipDictColorRow)

theorem polyFun_sbipSingletonColor : PolyFun sbipSingletonColor :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_sbipDictColorTable).pair
    (polyFun_snd.comp polyFun_singleton)).comp (polyFun_listLookup polyFun_listNatEq)).pair
      (polyFun_fst.comp polyFun_snd)).comp polyFun_optionGetD

theorem polyFun_sbipPointColors : PolyFun sbipPointColors :=
  (polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_sbipSingletonColor)

theorem sbipDictColorTable_mem (d : List (List ℕ)) (lab : RawLab) (p : List ℕ × ℕ) :
    p ∈ sbipDictColorTable (d,lab) ↔
      ∃ i : Fin d.length, p = (d[i.val],labAt lab i) := by
  simp only [sbipDictColorTable,List.mem_map]
  constructor
  · rintro ⟨⟨row,i⟩,hm,hp⟩
    obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hm)
    exact ⟨⟨i,hi⟩,by simpa [sbipDictColorRow,he] using hp.symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨(d[i.val],i),List.mk_mem_zipIdx_iff_getElem?.2 (by simp),rfl⟩

theorem sbipLookup_of_mem (l : List (List ℕ × ℕ)) (k : List ℕ) (v : ℕ)
    (hm : (k,v) ∈ l) (hc : ∀ p ∈ l, p.1 = k → p.2 = v) : l.lookup k = some v := by
  induction l with
  | nil => simp at hm
  | cons p l ih =>
    rcases p with ⟨key,value⟩
    by_cases hk : key = k
    · have hv := hc (key,value) (List.mem_cons_self ..) hk
      change value = v at hv
      simp [List.lookup_cons,hk,hv]
    · have hm' : (k,v) ∈ l := by
        rcases List.mem_cons.1 hm with he | he
        · exact False.elim (hk (congrArg Prod.fst he).symm)
        · exact he
      have hb : (k == key) = false := beq_eq_false_iff_ne.2 (Ne.symm hk)
      simpa only [List.lookup_cons,hb] using
        ih hm' (fun q hq => hc q (List.mem_cons_of_mem _ hq))

theorem sbipSingletonColor_hit (d : List (List ℕ)) (lab : RawLab) (pad u : ℕ)
    (i : Fin d.length) (hi : d[i.val] = [u])
    (hc : ∀ j : Fin d.length, d[j.val] = [u] → labAt lab j = labAt lab i) :
    sbipSingletonColor (((d,lab),pad),u) = labAt lab i := by
  have hm : ([u],labAt lab i) ∈ sbipDictColorTable (d,lab) :=
    (sbipDictColorTable_mem d lab _).2 ⟨i,by rw [hi]⟩
  have hh := sbipLookup_of_mem (sbipDictColorTable (d,lab)) [u] (labAt lab i) hm
    (by
      intro p hp hk
      obtain ⟨j,rfl⟩ := (sbipDictColorTable_mem d lab p).1 hp
      exact hc j hk)
  simp only [sbipSingletonColor,hh,Option.getD_some]

theorem sbipSingletonColor_hit_nodup (d : List (List ℕ)) (lab : RawLab) (pad u : ℕ)
    (hnd : d.Nodup) (i : Fin d.length) (hi : d[i.val] = [u]) :
    sbipSingletonColor (((d,lab),pad),u) = labAt lab i := by
  apply sbipSingletonColor_hit d lab pad u i hi
  intro j hj
  have he : j = i := Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 (hj.trans hi.symm))
  rw [he]

theorem sbipSingletonColor_miss (d : List (List ℕ)) (lab : RawLab) (pad u : ℕ)
    (hu : [u] ∉ d) : sbipSingletonColor (((d,lab),pad),u) = pad := by
  have hh : (sbipDictColorTable (d,lab)).lookup [u] = none := by
    apply List.lookup_eq_none_iff.2
    intro p hp
    obtain ⟨i,rfl⟩ := (sbipDictColorTable_mem d lab p).1 hp
    apply bne_iff_ne.2
    intro he
    exact hu (he.symm ▸ List.getElem_mem i.isLt)
  simp only [sbipSingletonColor,hh,Option.getD_none]

@[simp] theorem sbipPointColors_length (z : List ℕ × RawSbipColorRead) :
    (sbipPointColors z).length = z.1.length := by simp [sbipPointColors]

theorem sbipPointColors_get (z : List ℕ × RawSbipColorRead) (u : ℕ) (hu : u < z.1.length) :
    labAt (sbipPointColors z) u = sbipSingletonColor (z.2,u) := by
  simp [sbipPointColors,labAt,hu]

end Algo
