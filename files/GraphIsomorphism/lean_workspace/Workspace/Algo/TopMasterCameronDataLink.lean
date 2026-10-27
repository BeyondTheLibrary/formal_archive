import Workspace.Algo.TopMasterHintPullback
import Workspace.Algo.TopMasterCameronLink

/-! # The computed Cameron action in the live descent record
The block numbering transports the coordinate action. Taking preimages
then labels each union block by the same subset. Supplying this data in
the descent record makes its returned hint use that computed action.
-/
namespace Algo
open Babai Equiv
open scoped Classical

section Coordinate
variable {Ω : Type*} {n : ℕ} {c : RawCameron} (h : c.WF n) (e : Fin n ≃ Ω)

 noncomputable def camMappedPointHom :
    (camNbar c h).map e.permCongrHom.toMonoidHom →* Perm (Fin c.k) :=
  (camNbarPointHom h).comp (e.permCongrHom.subgroupMap (camNbar c h)).symm.toMonoidHom

 theorem camMappedPointHom_giant : IsGiantRep (camMappedPointHom h e) :=
  isGiantRep_comp_mulEquiv _ (camNbarPointHom_giant h)

 noncomputable def camMappedHintLink : MasterHintBlockLink (t := c.t)
    (isSystemOfImprimitivity_map_permCongrHom e (camBlocks_system h)).permutes
    (camMappedPointHom h e) :=
  (camNbarHintLink h).transport e
    (e.permCongrHom.subgroupMap (camNbar c h)).symm.toMonoidHom
    (fun g => congrArg Subtype.val ((e.permCongrHom.subgroupMap (camNbar c h)).apply_symm_apply g))
    (isSystemOfImprimitivity_map_permCongrHom e (camBlocks_system h)).permutes
end Coordinate

section Descent
variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}
    (b : Babai.BlockData I) {m : ℕ} (e : Fin m ≃ b.ℬ) {c : RawCameron} (h : c.WF m)
    (gs : RawGens)
    (hG : (decGroup m gs).map e.permCongrHom.toMonoidHom =
      onBlocks b.windowGroup b.ℬ b.system.permutes)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup m gs).map (permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup m gs).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s) (hwindow : 64 ≤ I.windowSize)

 noncomputable def camDescentRepresentation :
    let d := camDescentData b e h gs hG hlo hhi hwindow
    JohnsonActionData
      (isSystemOfImprimitivity_descentBlocks b.system d.N_normal.le d.𝒞_system).permutes c.k c.t := by
  let d := camDescentData b e h gs hG hlo hhi hwindow
  let L := (camMappedHintLink h e).pullback b.system d.N_normal.le d.𝒞_system
  exact {
    φ := (camMappedPointHom h e).comp (masterDescentBlockHom b.system)
    giant := by
      intro a ha
      obtain ⟨g, hg⟩ := camMappedPointHom_giant h e ha
      obtain ⟨q, hq⟩ := masterDescentBlockHom_surjective b.system d.N_normal.le g
      exact ⟨q, (congrArg (camMappedPointHom h e) hq).trans hg⟩
    label := L.label
    action := L.action }

 /-- The live Section 15 line-1 record retains the computed representation. -/
 noncomputable def camDescentDataLinked : DescentData I :=
  { camDescentData b e h gs hG hlo hhi hwindow with
    representation := camDescentRepresentation b e h gs hG hlo hhi hwindow }

 theorem camDescentDataLinked_cosetBranch :
    (camDescentDataLinked b e h gs hG hlo hhi hwindow).cosetBranch =
      (camDescentData b e h gs hG hlo hhi hwindow).cosetBranch := rfl

 theorem camDescentDataLinked_branch :
    (camDescentDataLinked b e h gs hG hlo hhi hwindow).branch =
      (camDescentData b e h gs hG hlo hhi hwindow).branch := rfl

 theorem camDescentDataLinked_action
    (htr : IsTransitive (camDescentDataLinked b e h gs hG hlo hhi hwindow).G₁) (y : Ω → A) :
    ((camDescentDataLinked b e h gs hG hlo hhi hwindow).johnsonCaseData htr y).ϕ =
      ((camMappedPointHom h e).comp (masterDescentBlockHom b.system)).comp
        (Subgroup.inclusion (le_of_eq
          (camDescentDataLinked b e h gs hG hlo hhi hwindow).restrictTo_K₁)) := rfl

end Descent
end Algo
