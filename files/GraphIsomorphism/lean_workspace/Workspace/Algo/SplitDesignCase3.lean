import Workspace.Algo.SplitDesignReadHint
import Workspace.Algo.SplitDesignCase12

/-! Section 9.7, Case 3 passes each returning Design Lemma version to
Reduce-Part2-by-Color. Selected vertices retain their old block names. -/
namespace Algo
open Babai RAM

def designReadNamedFirst (z : RawUpccCase × RawDesignReadOut) : List ℕ :=
  (designReadFirst z.2).map (fun i => labAt z.1.2.2 i)

def designReadNamedHintAt (z : (RawUpccCase × RawDesignReadOut) × (ℕ × ℕ)) : ℕ :=
  designReadHintAt (z.1.2,
    (designBlockIndex (z.1.1,z.2.1),designBlockIndex (z.1.1,z.2.2)))

def designReadNamedHintRow (z : (RawUpccCase × RawDesignReadOut) × List ℕ) : List ℕ × ℕ :=
  (z.2,designReadNamedHintAt (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def designReadNamedHint (z : RawUpccCase × RawDesignReadOut) : RawConfig :=
  (z.1.2.2,(tuplesOf z.1.2.2 2).map (fun t => designReadNamedHintRow (z,t)))

def designReadSelectFirst (z : RawUpccCase × RawDesignReadOut) : Bool :=
  bipCoverDefect (designRestricted (z.1,designReadNamedFirst z))

def designReadSelected (z : RawUpccCase × RawDesignReadOut) : List ℕ :=
  if designReadSelectFirst z then designReadNamedFirst z
  else z.1.2.2.filter (fun b => !decide (b ∈ designReadNamedFirst z))

def designCase3Graph (z : RawUpccCase × RawDesignReadOut) : RawDesignGraph :=
  ((z.1,designReadSelected z),designReadNamedHint z)

def designCase3GraphMap (z : RawUpccCase × List (List ℕ × RawDesignReadOut)) :
    List (List ℕ × RawDesignGraph) :=
  z.2.map (fun v => (v.1,designCase3Graph (z.1,v.2)))

def designCase3Graphs (r : RawUpccCase) : List (List ℕ × RawDesignGraph) :=
  designCase3GraphMap (r,designCallReadFamily r)

theorem polyFun_designReadNamedFirst : PolyFun designReadNamedFirst :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
    (polyFun_snd.comp polyFun_designReadFirst)).comp (PolyFun.mapParam polyFun_labAt)

theorem polyFun_designReadNamedHintAt : PolyFun designReadNamedHintAt := by
  have hr : PolyFun (fun z : (RawUpccCase × RawDesignReadOut) × (ℕ × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  exact ((polyFun_fst.comp polyFun_snd).pair
    (((hr.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_designBlockIndex).pair
      ((hr.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_designBlockIndex))).comp
        polyFun_designReadHintAt

theorem polyFun_designReadNamedHintRow : PolyFun designReadNamedHintRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_designReadNamedHintAt)

theorem polyFun_designReadNamedHint : PolyFun designReadNamedHint := by
  have hl : PolyFun (fun z : RawUpccCase × RawDesignReadOut => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  exact hl.pair ((polyFun_id.pair (hl.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam polyFun_designReadNamedHintRow))

theorem polyFun_designReadSelectFirst : PolyFun designReadSelectFirst :=
  ((polyFun_fst.pair polyFun_designReadNamedFirst).comp polyFun_designRestricted).comp polyFun_bipCoverDefect

theorem polyFun_designReadSelected : PolyFun designReadSelected := by
  have ht : PolyFun (fun z : List ℕ × ℕ => !decide (z.2 ∈ z.1)) :=
    polyFun_rawJNot ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
  exact PolyFun.ite polyFun_designReadSelectFirst polyFun_designReadNamedFirst
    ((polyFun_designReadNamedFirst.pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp (PolyFun.filterParam ht))

theorem polyFun_designCase3Graph : PolyFun designCase3Graph :=
  (polyFun_fst.pair polyFun_designReadSelected).pair polyFun_designReadNamedHint

theorem polyFun_designCase3GraphMap : PolyFun designCase3GraphMap := by
  have hf : PolyFun (fun z : RawUpccCase × (List ℕ × RawDesignReadOut) =>
      (z.2.1,designCase3Graph (z.1,z.2.2))) :=
    (polyFun_snd.comp polyFun_fst).pair
      ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_designCase3Graph)
  exact PolyFun.mapParam hf

theorem quasiFun_designCase3Graphs : QuasiFun designCase3Graphs := by
  have hi : QuasiFun (fun r : RawUpccCase => (r,designCallReadFamily r)) :=
    quasiFun_id.pair quasiFun_designCallReadFamily
  exact hi.comp_poly polyFun_designCase3GraphMap

theorem designCase3Graphs_length (r : RawUpccCase) :
    (designCase3Graphs r).length = (designCallReadFamily r).length := by
  simp [designCase3Graphs,designCase3GraphMap]

theorem designCase3GraphMap_mem (r : RawUpccCase) (L : List (List ℕ × RawDesignReadOut))
    (xs : List ℕ) (g : RawDesignGraph) :
    (xs,g) ∈ designCase3GraphMap (r,L) ↔ ∃ o, (xs,o) ∈ L ∧ g = designCase3Graph (r,o) := by
  rw [designCase3GraphMap,List.mem_map]
  constructor
  · rintro ⟨⟨ys,o⟩,ho,he⟩
    obtain ⟨hys,hg⟩ := Prod.mk.inj he
    change ys = xs at hys
    subst ys
    exact ⟨o,ho,hg.symm⟩
  · rintro ⟨o,ho,rfl⟩
    exact ⟨(xs,o),ho,rfl⟩

theorem designCase3Graphs_mem (r : RawUpccCase) (xs : List ℕ) (g : RawDesignGraph) :
    (xs,g) ∈ designCase3Graphs r ↔ ∃ o, (xs,o) ∈ designCallReadFamily r ∧ g = designCase3Graph (r,o) :=
  designCase3GraphMap_mem r (designCallReadFamily r) xs g

theorem designReadNamedHint_get (z : RawUpccCase × RawDesignReadOut) {a b : ℕ}
    (ha : a ∈ z.1.2.2) (hb : b ∈ z.1.2.2) :
    binColor (designReadNamedHint z,(a,b)) = designReadNamedHintAt (z,(a,b)) := by
  have ht : [a,b] ∈ tuplesOf z.1.2.2 2 := (mem_tuplesOf _ _ _).2
    ⟨rfl,by simpa using And.intro ha hb⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => designReadNamedHintAt (z,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [designReadNamedHint,designReadNamedHintRow,rawGet,binColor,tblGet] using hh

end Algo
