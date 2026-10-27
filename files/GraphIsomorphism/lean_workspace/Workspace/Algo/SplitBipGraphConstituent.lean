import Workspace.Algo.SplitBipGraphLink
import Workspace.Algo.SplitBipRefine

/-! Steps 7 and 8 keep a color class of blocks and replace adjacency by
the first constituent on its link. The full decoration arrays remain
with this graph, including colors of ambient points outside its first part. -/
namespace Algo
open Babai RAM

def sbipGraphRetainedLink (z : RawSbipGraph × (ℕ × ℕ)) : RawUpccCase :=
  let r := sbipLinkInput (sbipGraphPrepared z)
  (r.1,(r.2.1,sbipStep7Right r))

def sbipConstituentRow (z : RawUpccCase × List ℕ) : List ℕ × ℕ :=
  (z.2,sbipStep8Edge (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def sbipConstituentEdges (r : RawUpccCase) : RawConfig :=
  (r.2.1 ++ r.2.2,(tuplesOf (r.2.1 ++ r.2.2) 2).map (fun t => sbipConstituentRow (r,t)))

def sbipGraphConstituent (z : RawSbipGraph × (ℕ × ℕ)) : RawSbipGraph :=
  let r := sbipGraphRetainedLink z
  (sbipMatrix (sbipConstituentEdges r,r.2),z.1.2)

theorem polyFun_sbipGraphRetainedLink : PolyFun sbipGraphRetainedLink := by
  have hr := polyFun_sbipGraphPrepared.comp sbipPoly_linkInput
  exact (hr.comp polyFun_fst).pair
    (((hr.comp polyFun_snd).comp polyFun_fst).pair (hr.comp sbipPoly_step7Right))

theorem polyFun_sbipConstituentRow : PolyFun sbipConstituentRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp sbipPoly_step8Edge)

theorem polyFun_sbipConstituentEdges : PolyFun sbipConstituentEdges := by
  have hl : PolyFun (fun r : RawUpccCase => r.2.1 ++ r.2.2) := polyFun_snd.comp polyFun_append
  exact hl.pair ((polyFun_id.pair (hl.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam polyFun_sbipConstituentRow))

theorem polyFun_sbipGraphConstituent : PolyFun sbipGraphConstituent :=
  ((polyFun_sbipGraphRetainedLink.comp
    ((polyFun_sbipConstituentEdges.pair polyFun_snd).comp sbipPoly_matrix)).pair
      (polyFun_fst.comp polyFun_snd))

theorem sbipConstituentEdges_get (r : RawUpccCase) {u v : ℕ}
    (hu : u ∈ r.2.1 ++ r.2.2) (hv : v ∈ r.2.1 ++ r.2.2) :
    binColor (sbipConstituentEdges r,(u,v)) = sbipStep8Edge (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf (r.2.1 ++ r.2.2) 2 :=
    (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => sbipStep8Edge (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [sbipConstituentEdges,sbipConstituentRow,rawGet,binColor,tblGet] using hh

theorem sbipGraphConstituent_edge (z : RawSbipGraph × (ℕ × ℕ))
    (hl : (sbipGraphRetainedLink z).2.1.Nodup)
    (hr : (sbipGraphRetainedLink z).2.2.Nodup) (u v : ℕ) :
    sbipGraphEdge (sbipGraphConstituent z,(u,v)) =
      sbipStep8Edge (sbipGraphRetainedLink z,(u,v)) := by
  let r := sbipGraphRetainedLink z
  by_cases hu : u ∈ r.2.1
  · by_cases hv : v ∈ r.2.2
    · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hv
      have hh := sbipGraphEdge_get (sbipGraphConstituent z) hl hr ⟨i,hi⟩ ⟨j,hj⟩
      change sbipGraphEdge (sbipGraphConstituent z,(r.2.1[i],r.2.2[j])) = _ at hh
      rw [hh]
      have hm := sbipMatrix_spec (sbipConstituentEdges r) r.2.1 r.2.2 ⟨i,hi⟩ ⟨j,hj⟩
      change sbipMatrixEntry ((sbipGraphConstituent z).1,(i,j)) = _ at hm
      rw [hm]
      change (if binColor (sbipConstituentEdges r,(r.2.1[i],r.2.2[j])) = 0 then 0 else 1) =
        sbipStep8Edge (r,(r.2.1[i],r.2.2[j]))
      rw [sbipConstituentEdges_get r (List.mem_append_left _ hu) (List.mem_append_right _ hv)]
      unfold sbipStep8Edge
      split <;> rfl
    · rw [sbipGraphEdge_off _ _ _ (Or.inr hv)]
      change 0 = sbipStep8Edge (r,(u,v))
      simp [sbipStep8Edge,sbipStep8EdgeTest,hv]
  · rw [sbipGraphEdge_off _ _ _ (Or.inl hu)]
    change 0 = sbipStep8Edge (r,(u,v))
    simp [sbipStep8Edge,sbipStep8EdgeTest,hu]

end Algo
