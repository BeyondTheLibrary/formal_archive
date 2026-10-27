import Workspace.Algo.TopMasterDescentCameron

/-! # The actual block action on an ambient window
Restrict the stored generators to the displayed window, compute its
minimal blocks, and keep the resulting block images in the original
generator order. The action is trivial on the pointwise window stabilizer.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterRestrictionAction (W : RawWinSI) : RawAction :=
  ((W.2.2.2.1, W.2.1), (W.1, (primitiveWindowInput W).1))

def masterWindowBlockAction (W : RawWinSI) : RawAction :=
  ((masterRestrictionAction W).1,
    (camMinimalAction ((primitiveWindowInput W).1, W.1)).2)

def masterWindowBlockInput (W : RawWinSI) : MasterDescInput := (W, (masterWindowBlockAction W).2)

theorem polyFun_masterRestrictionAction : PolyFun masterRestrictionAction :=
  (((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair
    (polyFun_snd.comp polyFun_fst))).pair
    (polyFun_fst.pair (polyFun_primitiveWindowInput.comp polyFun_fst))

theorem polyFun_masterWindowBlockAction : PolyFun masterWindowBlockAction :=
  (polyFun_masterRestrictionAction.comp polyFun_fst).pair
    ((((polyFun_primitiveWindowInput.comp polyFun_fst).pair polyFun_fst).comp
      polyFun_camMinimalAction).comp polyFun_snd)

theorem polyFun_masterWindowBlockInput : PolyFun masterWindowBlockInput :=
  polyFun_id.pair (polyFun_masterWindowBlockAction.comp polyFun_snd)

/-- Compose two successive encoded actions without reordering their rows. -/
theorem masterCompose_wf {n m k : ℕ} {p : RawAction} {z : List ℕ × RawGens}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    {ψ : decGroup m p.2.2 →* Perm (Fin k)} (hq : RawAction.WF m k (p.2, z) ψ) :
    RawAction.WF n k (p.1, z) (ψ.comp (camActionRange hp)) := by
  refine ⟨hp.1, hq.2.1, hp.2.2.1, hq.2.2.2.1, hp.2.2.2.2.1.trans hq.2.2.2.2.1, ?_⟩
  intro i hn hk
  have hm : i < (p.2.2.map (decPerm m)).length := by rw [← hp.2.2.2.2.1]; exact hn
  have h1 := hp.2.2.2.2.2 i hn hm
  have h2 := hq.2.2.2.2.2 i hm hk
  change (z.2.map (decPerm k))[i] = ψ (camActionRange hp _)
  change (z.2.map (decPerm k))[i] = ψ _ at h2
  rw [h2]
  exact congrArg ψ (Subtype.ext h1)

section Window
variable {n : ℕ} {W : RawWinSI}
  (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
  (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
  (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

noncomputable def masterRestrictionHom : decGroup n W.2.1 →* Perm (Fin W.1.length) :=
  winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv

include hx hw in
theorem masterRestrictionAction_wf : RawAction.WF n W.1.length (masterRestrictionAction W)
    (masterRestrictionHom hnd hlt hinv) := by
  refine ⟨hx, rfl, hw, rawRestrictGens_wf_of_raw hw hnd hlt hinv, ?_, ?_⟩
  · simp [masterRestrictionAction, primitiveWindowInput, rawRestrictGens]
  · intro i hi hj
    have hig : i < W.2.1.length := by simpa [masterRestrictionAction] using hi
    have hmem : decPerm n W.2.1[i] ∈ decGroup n W.2.1 :=
      Subgroup.subset_closure (List.mem_map_of_mem (List.getElem_mem hig))
    have he := rawRestrictPerm_spec hnd hlt hinv hmem
    rw [encPerm_decPerm (hw _ (List.getElem_mem hig))] at he
    simp only [masterRestrictionAction, primitiveWindowInput, rawRestrictGens, List.getElem_map,
      he, decPerm_encPerm]
    rfl

theorem masterRestrictionHom_pointwise (g : decGroup n W.2.1)
    (hg : g ∈ pointwiseStab (decGroup n W.2.1) (winSet n W.1)) :
    masterRestrictionHom hnd hlt hinv g = 1 :=
  (mem_ker_winRestrictHom hnd hlt hinv g).mpr (mem_pointwiseStab.mp hg)

variable (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)

noncomputable def masterWindowBlockHom : decGroup n W.2.1 →*
    Perm (Fin (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length) :=
  (camMinimalHom (gs := (primitiveWindowInput W).1) (dom := W.1)
    (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn).comp
    (camActionRange (p := masterRestrictionAction W) (masterRestrictionAction_wf hx hw hnd hlt hinv))

theorem masterWindowBlockAction_wf :
    RawAction.WF n (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length (masterWindowBlockAction W)
      (masterWindowBlockHom hx hw hnd hlt hinv htr hn) :=
  masterCompose_wf (masterRestrictionAction_wf hx hw hnd hlt hinv)
    (camMinimalAction_wf (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn)

theorem masterWindowBlockHom_pointwise (g : decGroup n W.2.1)
    (hg : g ∈ pointwiseStab (decGroup n W.2.1) (winSet n W.1)) :
    masterWindowBlockHom hx hw hnd hlt hinv htr hn g = 1 := by
  have he : camActionRange (masterRestrictionAction_wf hx hw hnd hlt hinv) g = 1 :=
    Subtype.ext (masterRestrictionHom_pointwise hnd hlt hinv g hg)
  change camMinimalHom (gs := (primitiveWindowInput W).1) (dom := W.1)
    (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn
    (camActionRange (p := masterRestrictionAction W) (masterRestrictionAction_wf hx hw hnd hlt hinv) g) = 1
  rw [he]
  exact (camMinimalHom (gs := (primitiveWindowInput W).1) (dom := W.1)
    (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn).map_one

include hw hnd hlt hinv htr hn in
theorem masterWindowBlockAction_primitive :
    IsPrimitive (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2) :=
  camMinimalAction_primitive (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn

include hnd hlt in
theorem masterWindowBlockAction_degree :
    (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ n :=
  (blocksWF_rawMinBlocks rfl (primitiveWindowInput W).1).length_le.trans
    (length_le_of_nodup_lt hnd hlt)
end Window
end Algo
