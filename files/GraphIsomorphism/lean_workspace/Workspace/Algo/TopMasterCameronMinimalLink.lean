import Workspace.Algo.TopMasterCameronRowsLink

/-! # The computed minimal-block action supplies the retained labels
The action equation is discharged for `camMinimalAction`, using the
stored block numbering. Thus neither the action nor its label relation
is a premise supplied by the caller of the Cameron descent.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section Minimal
variable {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : IsTransitive (decGroup n gs)) (hn : 2 ≤ n)

 theorem camMinimalAction_row (g : decGroup n gs) :
    (blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs)).permCongrHom
      (camMinimalHom hw hd htr hn g) =
      blockHom (decGroup n gs) (blockSets n (rawMinBlocks (gs, dom)))
        (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes g := by
  apply Equiv.ext
  intro U
  let e := blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs)
  change e (e.symm (blockHom _ _
    (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes g (e (e.symm U)))) = _
  simp only [Equiv.apply_symm_apply]

variable {c : RawCameron} (h : c.WF (rawMinBlocks (gs, dom)).length)
    (hhi : (decGroup (rawMinBlocks (gs, dom)).length (camMinimalAction (gs, dom)).2.2).map
      (permCongrHom (decCameron c h)).toMonoidHom ≤ wreathProduct (JohnsonS c.k c.t) c.s)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup (rawMinBlocks (gs, dom)).length (camMinimalAction (gs, dom)).2.2).map
        (permCongrHom (decCameron c h)).toMonoidHom)

noncomputable def camMinimalUnionSystem :=
  camLiftUnionSystem (camMinimalAction_wf hw hd htr hn) h hhi hlo
    (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).toIsSystemOfImprimitivity
    (blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs))
    (camBlockImgs_group (blocksWF_rawMinBlocks hd gs) hw
      (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes)
    (camMinimalAction_row hw hd htr hn)

noncomputable def camMinimalRowsHintLink :
    MasterHintBlockLink (t := c.t) (camMinimalUnionSystem hw hd htr hn h hhi hlo).permutes
      (camLiftGiantHom (camMinimalAction_wf hw hd htr hn) h hhi) :=
  camLiftRowsHintLink (camMinimalAction_wf hw hd htr hn) h hhi hlo
    (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).toIsSystemOfImprimitivity
    (blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs))
    (camBlockImgs_group (blocksWF_rawMinBlocks hd gs) hw
      (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes)
    (camMinimalAction_row hw hd htr hn)

/-- The same ordered raw action has both its machine specification and
its explicit equation on the union-block labels. -/
theorem camMinimalRows_spec :
    RawAction.WF n c.k (camLiftAction (c, camMinimalAction (gs, dom)))
      (camLiftGiantHom (camMinimalAction_wf hw hd htr hn) h hhi) ∧
    Nonempty (MasterHintBlockLink (t := c.t)
      (camMinimalUnionSystem hw hd htr hn h hhi hlo).permutes
      (camLiftGiantHom (camMinimalAction_wf hw hd htr hn) h hhi)) :=
  ⟨camLiftAction_wf (camMinimalAction_wf hw hd htr hn) h hhi,
    ⟨camMinimalRowsHintLink hw hd htr hn h hhi hlo⟩⟩
end Minimal
end Algo
