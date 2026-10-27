import Workspace.Algo.SplitBipGraphRead

/-! The shared graph enters steps 3--5 with its original names. Refinement
supplies the class colors. The adjacency and all decorations stay with the
restriction, so the next case sees the same graph fields. -/
namespace Algo
open Babai RAM

def sbipGraphEdgeRow (z : RawSbipGraph × List ℕ) : List ℕ × ℕ :=
  (z.2,sbipGraphEdge (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def sbipGraphEdges (r : RawSbipGraph) : RawConfig :=
  (sbipGraphVertices r,(tuplesOf (sbipGraphVertices r) 2).map (fun t => sbipGraphEdgeRow (r,t)))

def sbipGraphClasses (z : RawSbipGraph × (ℕ × ℕ)) : RawSbipClasses :=
  ((sbipGraphRefine z.1,z.1.1.1),z.2)

def sbipGraphPrepared (z : RawSbipGraph × (ℕ × ℕ)) : RawSbipStep5Input :=
  ((sbipGraphClasses z,z.1.1.2.1),(sbipGraphEdges z.1,z.1.2))

def sbipGraphSteps35 (z : RawSbipGraph × (ℕ × ℕ)) :
    (List ℕ × RawColPart) × Option RawSbipStep5Output :=
  let q := sbipGraphPrepared z
  ((q.1.1.1.2,sbipStep4 q.1.1),
    if sbipNoDominant q.1.1 then none else some (sbipStep5 q))

theorem polyFun_sbipGraphEdgeRow : PolyFun sbipGraphEdgeRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_sbipGraphEdge)

theorem polyFun_sbipGraphEdges : PolyFun sbipGraphEdges :=
  polyFun_sbipGraphVertices.pair ((polyFun_id.pair
    (polyFun_sbipGraphVertices.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
      (PolyFun.mapParam polyFun_sbipGraphEdgeRow))

theorem polyFun_sbipGraphClasses : PolyFun sbipGraphClasses :=
  ((polyFun_fst.comp polyFun_sbipGraphRefine).pair
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair polyFun_snd

theorem polyFun_sbipGraphPrepared : PolyFun sbipGraphPrepared :=
  (polyFun_sbipGraphClasses.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)).pair
    ((polyFun_fst.comp polyFun_sbipGraphEdges).pair (polyFun_fst.comp polyFun_snd))

theorem polyFun_sbipGraphSteps35 : PolyFun sbipGraphSteps35 := by
  have hc := polyFun_sbipGraphClasses
  have ho := PolyFun.ite (hc.comp sbipPoly_noDominant) (polyFun_const none)
    ((polyFun_sbipGraphPrepared.comp sbipPoly_step5).comp polyFun_some)
  exact ((hc.comp (polyFun_fst.comp polyFun_snd)).pair (hc.comp sbipPoly_step4)).pair ho

theorem sbipGraphEdges_get (r : RawSbipGraph) {u v : ℕ}
    (hu : u ∈ sbipGraphVertices r) (hv : v ∈ sbipGraphVertices r) :
    binColor (sbipGraphEdges r,(u,v)) = sbipGraphEdge (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf (sbipGraphVertices r) 2 := (mem_tuplesOf _ _ _).2
    ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => sbipGraphEdge (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [sbipGraphEdges,sbipGraphEdgeRow,rawGet,binColor,tblGet] using hh

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (z : RawSbipGraph × (ℕ × ℕ))
    (name : X.obj.1.1.Vtx → ℕ)
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)

def sbipGraphPointName (x : ↥X.obj.1.1.V₁) : ℕ :=
  name ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩

include h hnd he in
theorem sbipGraphClasses_names
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X) :
    SbipClassNames X (sbipGraphPointName X name) (sbipGraphClasses z) := by
  refine ⟨?_,hp,?_,ha⟩
  · intro x y hh
    have hs := congrArg (fun A : X.obj.1.1.Vtx => A.val) (h.injective hh)
    exact Subtype.ext (Set.singleton_injective hs)
  · intro x
    have hh := sbipGraphRefine_spec X.obj.1.1 z.1 name h hnd e he
      ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩
    change binColor (sbipGraphRefine z.1,
      (name ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩,
       name ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩)) + 1 = _
    rw [hh,VColBipBlk.wlDiag,VColBipBlk.wlColor,
      dif_pos ⟨Or.inl ⟨x.val,x.property,rfl⟩,Or.inl ⟨x.val,x.property,rfl⟩⟩]

include h hnd he in
theorem sbipGraphSteps35_exit_iff
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) :
    (sbipGraphSteps35 z).2 = none ↔ AllClassesSmall X := by
  have hh := sbipNoDominant_iff (sbipGraphClasses_names X z name h hnd e he hp ha) hl hb
  change (if sbipNoDominant (sbipGraphClasses z) then none else some _) = none ↔ _
  cases hc : sbipNoDominant (sbipGraphClasses z) <;> simp_all

end
end Algo
