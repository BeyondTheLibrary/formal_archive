import Workspace.Algo.AggNodeAggregateCase2b
import Workspace.Algo.FunctorsAmbient

/-! # Numbering each computed constituent for the Extended Design Lemma

Local vertices are positions in the returned vertex list. `winEquiv`
identifies those positions with the actual subset of the giant domain.
Tuple membership is pulled back by the existing string restriction routine.
The original instance domain remains a separate witness for the arity guard.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- The single binary relation, read on consecutive positions. -/
def aggnConstituentRel (q : AggnRawConstituent) : RawRel :=
  (tuplesOf (List.range q.1.length) 2).filter fun row =>
    decide (rawRestrictStr (q.1,row) ∈ q.2)

/-- The arity witness, original domain, local domain, and single relation. -/
def aggnConstituentEnter (p : List ℕ × AggnRawConstituent) : AmbientPIn :=
  (([0,1],p.1,List.range p.2.1.length),[aggnConstituentRel p.2])

theorem aggnPolyFun_constituentRel : PolyFun aggnConstituentRel := by
  have hf : PolyFun (fun z : AggnRawConstituent × List ℕ =>
      decide (rawRestrictStr (z.1.1,z.2) ∈ z.1.2)) :=
    (((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawRestrictStr).pair
      (polyFun_fst.comp polyFun_snd)).comp (polyFun_listMem polyFun_listNatEq)).of_eq
        (fun _ => by congr 1)
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_rangeLength).comp
    ((polyFun_tuplesOf 2).comp polyFun_snd))).comp (PolyFun.filterParam hf)

theorem aggnPolyFun_constituentEnter : PolyFun aggnConstituentEnter :=
  ((polyFun_const [0,1]).pair (polyFun_fst.pair
    ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength))).pair
      ((polyFun_snd.comp aggnPolyFun_constituentRel).comp polyFun_singleton)

/-- Local rows have arity two and in-range coordinates, even on malformed inputs. -/
theorem aggnConstituentRel_rows (q : AggnRawConstituent) {row : List ℕ}
    (hr : row ∈ aggnConstituentRel q) :
    row.length = 2 ∧ ∀ u ∈ row,u < q.1.length := by
  have h := (mem_tuplesOf _ _ _).mp (List.mem_filter.mp hr).1
  exact ⟨h.1,fun u hu => List.mem_range.mp (h.2 u hu)⟩

theorem aggnConstituentRel_pair (q : AggnRawConstituent) (u v : Fin q.1.length) :
    [u.val,v.val] ∈ aggnConstituentRel q ↔ [q.1[u.val],q.1[v.val]] ∈ q.2 := by
  simp [aggnConstituentRel,mem_tuplesOf,rawRestrictStr,rawGet,u.isLt,v.isLt]

/-- The exact subset bijection preserves every relation tuple. -/
theorem aggnConstituentRel_spec {m : ℕ} (q : AggnRawConstituent)
    (hnd : q.1.Nodup) (hlt : ∀ u ∈ q.1,u < m) (x : Fin 2 → Fin q.1.length) :
    tupleOf x ∈ aggnConstituentRel q ↔
      (fun i => winEquiv m q.1 hnd hlt (x i)) ∈
        (binStruct (winSet m q.1) (aggnDecodePairRel m q.2)).rel ⟨0,by change 0 < 1; decide⟩ := by
  have he : tupleOf x = [(x 0).val,(x 1).val] := by simp [tupleOf,List.ofFn_succ]
  rw [he,aggnConstituentRel_pair]
  change _ ↔ [((winEquiv m q.1 hnd hlt (x 0)).val).val,
    ((winEquiv m q.1 hnd hlt (x 1)).val).val] ∈ q.2
  rw [winEquiv_coe q.1 hnd hlt (x 0).isLt,winEquiv_coe q.1 hnd hlt (x 1).isLt]

/-- The explicit one-relation decoder for the numbered constituent. -/
def aggnNumberedStruct (q : AggnRawConstituent) : RelStructure (Fin q.1.length) where
  numRel := 1
  arity _ := 2
  rel _ := {x | tupleOf x ∈ aggnConstituentRel q}

/-- Transporting the numbered structure by `winEquiv` gives exactly `binStruct`. -/
theorem aggnNumberedStruct_map {m : ℕ} (q : AggnRawConstituent)
    (hnd : q.1.Nodup) (hlt : ∀ u ∈ q.1,u < m) :
    (aggnNumberedStruct q).map (winEquiv m q.1 hnd hlt) =
      binStruct (winSet m q.1) (aggnDecodePairRel m q.2) := by
  have hr : mapRel (winEquiv m q.1 hnd hlt)
      {x : Fin 2 → Fin q.1.length | tupleOf x ∈ aggnConstituentRel q} =
      (binStruct (winSet m q.1) (aggnDecodePairRel m q.2)).rel ⟨0,by change 0 < 1; decide⟩ := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (aggnConstituentRel_spec q hnd hlt y).mp hy
    · intro hx
      let y := fun i => (winEquiv m q.1 hnd hlt).symm (x i)
      have he : (fun i => winEquiv m q.1 hnd hlt (y i)) = x := by funext i; simp [y]
      refine ⟨y,(aggnConstituentRel_spec q hnd hlt y).mpr ?_,he⟩
      rwa [he]
  change RelStructure.mk 1 (fun _ => 2) (fun _ => _) = RelStructure.mk 1 (fun _ => 2) (fun _ => _)
  simp only [RelStructure.mk.injEq,heq_eq_eq,true_and]
  funext i
  exact hr

/-- Every computed Case 2b carrier supplies the renumbering premises itself. -/
theorem aggnCase2bFamily_names {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) {q : AggnRawConstituent} (hq : q ∈ aggnCase2bFamily (dom,gs)) :
    q.1.Nodup ∧ (∀ u ∈ q.1,u < m) := by
  obtain ⟨S,_,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨R,_,rfl⟩ := List.mem_map.mp hq
  exact ⟨(aggnLargeOrbitPoints_nodup (dom,gs)).filter _,
    fun u hu => aggnLargeOrbitPoints_lt hd u (List.mem_filter.mp hu).1⟩

/-- The recursive input retains the original domain and uses the exact subset size. -/
theorem aggnConstituentEnter_fields (p : List ℕ × AggnRawConstituent) :
    (aggnConstituentEnter p).1.1 = [0,1] ∧
    (aggnConstituentEnter p).1.2.1 = p.1 ∧
    (aggnConstituentEnter p).1.2.2 = List.range p.2.1.length ∧
    (aggnConstituentEnter p).2 = [aggnConstituentRel p.2] := ⟨rfl,rfl,rfl,rfl⟩

theorem aggnConstituentEnter_spec {m : ℕ} (original : List ℕ) (q : AggnRawConstituent)
    (hnd : q.1.Nodup) (hlt : ∀ u ∈ q.1,u < m) (x : Fin 2 → Fin q.1.length) :
    x ∈ (decRel q.1.length 2 (aggnConstituentEnter (original,q)).2).rel 0 ↔
      (fun i => winEquiv m q.1 hnd hlt (x i)) ∈
        (binStruct (winSet m q.1) (aggnDecodePairRel m q.2)).rel ⟨0,by change 0 < 1; decide⟩ := by
  change tupleOf x ∈ aggnConstituentRel q ↔ _
  exact aggnConstituentRel_spec q hnd hlt x

end Algo
