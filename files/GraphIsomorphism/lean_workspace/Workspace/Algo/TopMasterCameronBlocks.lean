import Workspace.Algo.TopMasterCameronRecognize
import Workspace.Algo.CameronDescentData

/-! # The Cameron hint from the actual minimal blocks
Line 4 of Reduce-to-Johnson computes the minimal blocks and their action.
The primitive-group hypothesis of recognition is discharged for that action.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem camBlock_map {α β : Type*} (e : α ≃ β) {G : Subgroup (Perm α)}
    {B : Set α} (hB : IsBlockOfImprimitivity G B) :
    IsBlockOfImprimitivity (G.map e.permCongrHom.toMonoidHom) (e '' B) := by
  refine ⟨hB.1.image e, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [image_permCongrHom_image_gen]
  rcases hB.2 g hg with he | hd
  · exact Or.inl (congrArg (fun S : Set α => e '' S) he)
  · right
    rw [← Set.image_inter e.injective, hd, Set.image_empty]

theorem camPrimitive_of_map {α β : Type*} (e : α ≃ β) {G : Subgroup (Perm α)}
    (hG : IsPrimitive (G.map e.permCongrHom.toMonoidHom)) : IsPrimitive G := by
  refine ⟨?_, fun B hB => ?_⟩
  · have he := Nat.card_congr (e.permCongrHom.subgroupMap G).toEquiv
    exact he ▸ hG.1
  · rcases hG.2 (e '' B) (camBlock_map e hB) with h | ⟨a, h⟩
    · left
      apply (Set.image_injective.mpr e.injective)
      simpa using h
    · right
      refine ⟨e.symm a, ?_⟩
      apply (Set.image_injective.mpr e.injective)
      simpa using h

def camMinimalAction (p : RawGens × List ℕ) : RawAction :=
  ((p.2, p.1), ((camBlockInput p).2, (camBlockInput p).1))

def camRecognizeMinimalLift (cameron : RawGens × List ℕ → Option RawCameron)
    (p : RawGens × List ℕ) : Option (RawCameron × RawAction) :=
  camRecognizeLift cameron (camMinimalAction p)

theorem polyFun_camMinimalAction : PolyFun camMinimalAction :=
  (polyFun_snd.pair polyFun_fst).pair
    ((camPoly_blockInput.comp polyFun_snd).pair (camPoly_blockInput.comp polyFun_fst))

theorem polyFun_camRecognizeMinimalLift
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron) :
    PolyFun (camRecognizeMinimalLift cameron) :=
  polyFun_camMinimalAction.comp (polyFun_camRecognizeLift hc)

section Minimal
variable {n : ℕ} {gs : RawGens} {dom : List ℕ}
  (hw : RawGens.WF n gs) (hd : dom.length = n)
  (htr : IsTransitive (decGroup n gs)) (hn : 2 ≤ n)

noncomputable def camMinimalHom : decGroup n gs →* Perm (Fin (rawMinBlocks (gs, dom)).length) :=
  blockPhi n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs)
    (gs.map (decPerm n)) (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes

theorem camMinimalAction_wf : RawAction.WF n (rawMinBlocks (gs, dom)).length
    (camMinimalAction (gs, dom)) (camMinimalHom hw hd htr hn) := by
  refine ⟨hd, length_blkDom _, hw, ?_, ?_⟩
  · simpa only [camBlockInput, length_blkDom] using camBlockInput_wf hw hd htr hn
  · have hi := imgsOf_blockPhi (blocksWF_rawMinBlocks hd gs)
      (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes
    simpa only [blockImgsOf, map_encPerm_decPerm hw] using hi

include hw hd htr hn in
/-- The group which is actually passed to recognition is primitive. -/
theorem camMinimalAction_primitive :
    IsPrimitive (decGroup (rawMinBlocks (gs, dom)).length (camMinimalAction (gs, dom)).2.2) := by
  apply camPrimitive_of_map (blockEquiv n (rawMinBlocks (gs, dom)) (blocksWF_rawMinBlocks hd gs))
  change IsPrimitive ((decGroup (rawMinBlocks (gs, dom)).length
    (rawBlockImgs (rawMinBlocks (gs, dom), gs))).map _)
  rw [camBlockImgs_group (blocksWF_rawMinBlocks hd gs) hw
    (isMinimalSystemOfImprimitivity_rawMinBlocks hw hd htr hn).permutes]
  exact isPrimitive_rawMinBlocks hw hd htr hn

/-- The recognition contract, with its input action and primitivity computed. -/
theorem camRecognizeMinimalLift_spec
    {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) (hs : CameronSpec cameron)
    (hm : max 25 camDescentThreshold ≤ (rawMinBlocks (gs, dom)).length)
    (hb : ((rawMinBlocks (gs, dom)).length : ℝ) ^
      (1 + Real.logb 2 (rawMinBlocks (gs, dom)).length) ≤
      Nat.card (decGroup (rawMinBlocks (gs, dom)).length (camMinimalAction (gs, dom)).2.2)) :
    ∃ (c : RawCameron) (h : c.WF (rawMinBlocks (gs, dom)).length) (A : RawAction)
        (ψ : decGroup n A.1.2 →* Perm (Fin c.k)),
      camRecognizeMinimalLift cameron (gs, dom) = some (c, A) ∧
      A = camLiftAction (c, camMinimalAction (gs, dom)) ∧
      RawAction.WF n c.k A ψ ∧ IsGiantRep ψ ∧
      decGroup n A.1.2 = camLiftSubgroup (p := camMinimalAction (gs, dom)) (ϕ := camMinimalHom hw hd htr hn) h ∧
      (decGroup n A.1.2).relIndex (decGroup n gs) ≤ (rawMinBlocks (gs, dom)).length ∧
      Real.logb 2 (rawMinBlocks (gs, dom)).length ≤ (c.k : ℝ) ∧ A.1.2.length ≤ n * n :=
  camRecognizeLift_spec hc hs n (rawMinBlocks (gs, dom)).length (camMinimalAction (gs, dom))
    (camMinimalHom hw hd htr hn) (camMinimalAction_wf hw hd htr hn) hm
    (camMinimalAction_primitive hw hd htr hn) hb

end Minimal
end Algo
