import Workspace.Algo.DesignAmbient

/-! # The Design Lemma version family

The scan finds the first length at which its test returns. At that length
we keep every returning tuple. Each tuple supplies one version, with the
paper's canonicity relative to that tuple. Keeping the full family avoids
making its choice depend on the names of the vertices.
-/
namespace Algo
open Babai RAM

/-- The tuple table at the returning length, carrying the original degree guard. -/
def ambientDesignVersionRows (c : ℕ) (z : AmbientGIn × List ℕ) : List (List ℕ) :=
  (aggTable c (z.1.1.1.1.take z.2.length,z.1.1.1.2.1,z.1.1.1.2.2)).2.map Prod.fst

/-- All successful individualizations of that length. -/
def ambientDesignVersionsAt (c : ℕ) (z : AmbientGIn × List ℕ) : List (List ℕ) :=
  (ambientDesignVersionRows c z).filter
    (fun ys => returnsB (ambientDesignAt c z.1 ys))

def ambientDesignVersions (c : ℕ) (g : AmbientGIn) : List (List ℕ) :=
  (ambientDesignProcedure c g).elim [] (fun xs => ambientDesignVersionsAt c (g,xs))

/-- Retain the tuple alongside the object that is canonical relative to it. -/
def ambientDesignFamily (c : ℕ) (g : AmbientGIn) :
    List (List ℕ × (List ℕ × (List ℕ × ℕ))) :=
  (ambientDesignVersions c g).map (fun xs => (xs,designOutRaw (ambientDesignAt c g xs)))

theorem quasiFun_ambientDesignVersionRows (c : ℕ) : QuasiFun (ambientDesignVersionRows c) := by
  have hg : PolyFun (fun z : AmbientGIn × List ℕ => z.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)
  have hk := ((hg.comp polyFun_fst).pair (polyFun_snd.comp polyFun_length)).comp polyFun_take
  exact ((hk.pair (hg.comp polyFun_snd)).comp_quasiFun (aggQuasiFun_table c)).comp_poly
    (polyFun_snd.comp (PolyFun.map polyFun_fst))

theorem quasiFun_ambientDesignVersionsAt (c : ℕ) : QuasiFun (ambientDesignVersionsAt c) := by
  have hp : QuasiFun (fun z : AmbientGIn × List ℕ => ambientDesignAt c z.1 []) :=
    (polyFun_fst.comp_quasiFun (quasiFun_ambientDesignAt c))
  exact (hp.pair (quasiFun_ambientDesignVersionRows c)).comp_poly
    (PolyFun.filterParam (polyFun_withStr.comp polyFun_returnsB))

theorem quasiFun_ambientDesignVersions (c : ℕ) : QuasiFun (ambientDesignVersions c) := by
  have hh : QuasiFun (fun z : List ℕ × AmbientGIn => ambientDesignVersionsAt c (z.2,z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp_quasiFun (quasiFun_ambientDesignVersionsAt c)
  exact (((quasiFun_ambientDesignProcedure c).pair polyFun_id.quasiFun).comp
    (QuasiFun.optionElim (quasiFun_const []) hh)).of_eq (fun g => by
      unfold ambientDesignVersions
      cases ambientDesignProcedure c g <;> rfl)

theorem quasiFun_ambientDesignFamily (c : ℕ) : QuasiFun (ambientDesignFamily c) := by
  have hm : PolyFun (fun z : DIn × List ℕ => (z.2,designOutRaw (withStr z))) :=
    polyFun_snd.pair (polyFun_withStr.comp polyFun_designOutRaw)
  exact ((quasiFun_ambientDesignAt c).pair (quasiFun_ambientDesignVersions c)).comp_poly
    (PolyFun.mapParam hm)

section Specification
variable {n k a b c : ℕ} {ks base dom : List ℕ} {rels : RawRelStruct}
    (hnd : dom.Nodup) (hmem : ∀ i, i ∈ dom ↔ i < n) (hk : ks.length = k)
    (hg : ks.length ≤ guardBound c base.length)

local notation "g" => (((ks,base,dom),rels),(a,b))

include hk hg

/-- The guard does not change the tuple table at a legitimate returning length. -/
theorem ambientDesignVersionRows_spec (xs : List ℕ) (hl : xs.length ≤ k) :
    ambientDesignVersionRows c (g,xs) = tuplesOf dom xs.length := by
  unfold ambientDesignVersionRows
  rw [aggTable_of_guard (a := (ks.take xs.length,base,dom))
    (by rw [List.length_take]; exact (min_le_right _ _).trans hg),keys_tupleTable,List.length_take,
      min_eq_left (hk.symm ▸ hl)]

include hnd hmem

/-- Membership keeps precisely the returning tuples of the least returning length. -/
theorem ambientDesignVersions_spec {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
    {xs : List ℕ} (hs : ambientDesignProcedure c g = some xs) :
    ∃ l, ∃ hl : l < k,
      xs.length = l ∧
      (∀ v : Str (Fin n) l, tupleOf v ∈ ambientDesignVersions c g ↔
        KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le v) ∧
      (∀ ys ∈ ambientDesignVersions c g, ys.length = l ∧ ∀ i ∈ ys, i < n) ∧
      (∀ l' < l, ¬ KAryPartStruct.ReturnsAt α (decRel n k rels).F1.F2.F3 l') := by
  obtain ⟨l,hl,x,hx,hret,hmin⟩ := ambientDesignProcedure_some hnd hmem hk hb hab hg hs
  have hlen : xs.length = l := by rw [← hx,length_tupleOf]
  have he : ambientDesignVersions c g =
      (tuplesOf dom l).filter (fun ys => returnsB (ambientDesignAt c g ys)) := by
    rw [ambientDesignVersions,hs]
    change ambientDesignVersionsAt c (g,xs) = _
    rw [ambientDesignVersionsAt,ambientDesignVersionRows_spec hk hg xs (by omega),hlen]
  have hw : RawWL.WF n k (ambientPipeline321 c ((ks,base,dom),rels)) := by
    subst k; exact ambientPipeline321_wf (a := ((ks,base,dom),rels)) hnd hmem hg
  have hcl : ∀ u v : Str (Fin n) k,
      (decWL n k (ambientPipeline321 c ((ks,base,dom),rels))).color u =
        (decWL n k (ambientPipeline321 c ((ks,base,dom),rels))).color v ↔
      (decRel n k rels).F1.F2.F3.color u = (decRel n k rels).F1.F2.F3.color v := by
    subst k; exact ambientPipeline321_spec (a := ((ks,base,dom),rels)) hnd hmem hg
  refine ⟨l,hl,hlen,?_,?_,?_⟩
  · intro v
    rw [he,List.mem_filter]
    have hv : tupleOf v ∈ tuplesOf dom l := (mem_tuplesOf _ _ _).2
      ⟨length_tupleOf v,fun i hi => (hmem _).2 (tupleOf_lt v hi)⟩
    rw [and_iff_right hv]
    change returnsB (((ks,tupleOf v),ambientPipeline321 c ((ks,base,dom),rels)),(a,b)) = true ↔ _
    rw [returnsB_spec hw hk hl.le v hb hab]
    exact returns_congr hcl hl.le v
  · intro ys hy
    have hy' := (mem_tuplesOf _ _ _).1 (List.mem_of_mem_filter (he ▸ hy))
    exact ⟨hy'.1,fun i hi => (hmem _).1 (hy'.2 i hi)⟩
  · intro l' hl' ⟨hlk,v,hv⟩
    exact hmin l' hl' v hv

/-- A successful scan contributes at least its own tuple to the family. -/
theorem ambientDesignVersions_nonempty {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
    {xs : List ℕ} (hs : ambientDesignProcedure c g = some xs) :
    xs ∈ ambientDesignVersions c g := by
  obtain ⟨l,hl,x,hx,hret,_⟩ := ambientDesignProcedure_some hnd hmem hk hb hab hg hs
  obtain ⟨l',hl',hlen,hall,_,_⟩ := ambientDesignVersions_spec hnd hmem hk hg hb hab hs
  have he : l' = l := by rw [← hx,length_tupleOf] at hlen; exact hlen.symm
  cases he
  rw [← hx]
  exact (hall x).2 hret

/-- The family pays at most one version per tuple of the returning length. -/
theorem ambientDesignVersions_length {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
    {xs : List ℕ} (hs : ambientDesignProcedure c g = some xs) :
    (ambientDesignVersions c g).length ≤ dom.length ^ xs.length := by
  obtain ⟨l,hl,x,hx,_,_⟩ := ambientDesignProcedure_some hnd hmem hk hb hab hg hs
  have hlen : xs.length = l := by rw [← hx,length_tupleOf]
  rw [ambientDesignVersions,hs]
  change (ambientDesignVersionsAt c (g,xs)).length ≤ _
  rw [ambientDesignVersionsAt,ambientDesignVersionRows_spec hk hg xs (by omega)]
  exact (List.length_filter_le _ _).trans (le_of_eq (length_tuplesOf dom xs.length))

end Specification
end Algo
