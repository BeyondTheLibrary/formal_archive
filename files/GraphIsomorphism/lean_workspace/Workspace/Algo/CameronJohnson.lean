import Workspace.Algo.CameronNbar

/-!
# The computed Johnson action in Theorem 11.2.1

The hint labels a coordinate block by its subset. Under these labels, the raw
block images of the computed alternating base group generate exactly the
Johnson group. The identification is the hint itself.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- The hint sends the numbered block action to the first local permutation. -/
theorem camHint_conjugates {n : ℕ} {c : RawCameron} (h : c.WF n)
    (gens : List (Perm (Fin n)))
    (hp : ∀ g ∈ genGroup gens, ∀ B ∈ blockSets n (camBlocks c),
      (g : Perm (Fin n)) '' B ∈ blockSets n (camBlocks c))
    (g : genGroup gens) (p : Fin c.s → Perm (Babai.binom (Fin c.k) c.t))
    (he : (Equiv.permCongrHom (decCameron c h)) g.val = Babai.wreathPerm p 1) :
    (Equiv.permCongrHom (camHintEquiv h))
      (blockPhi n (camBlocks c) (camBlocks_wf h) gens hp g) = p ⟨0, h.s_pos⟩ := by
  apply Equiv.ext
  intro S
  let i := (camHintEquiv h).symm S
  have hv : ∀ j : Fin (camBlocks c).length,
      Babai.coordFibre (decCameron c h) ⟨0, h.s_pos⟩ (camHintEquiv h j) =
        winSet n (camBlocks c)[j.val] := fun j => (camHintValue_fibre h j).symm
  have hb : winSet n (camBlocks c)[(blockPhi n (camBlocks c) (camBlocks_wf h) gens hp g i).val] =
      g.val '' winSet n (camBlocks c)[i.val] := by
    have hi : blockEquiv n (camBlocks c) (camBlocks_wf h)
        (blockPhi n (camBlocks c) (camBlocks_wf h) gens hp g i) =
        Babai.blockHom (genGroup gens) (blockSets n (camBlocks c)) hp g
          (blockEquiv n (camBlocks c) (camBlocks_wf h) i) := by
      rw [blockPhi_apply, Equiv.apply_symm_apply]
    exact congrArg Subtype.val hi
  change camHintEquiv h (blockPhi n (camBlocks c) (camBlocks_wf h) gens hp g i) = _
  apply Babai.coordFibre_injective (decCameron c h) ⟨0, h.s_pos⟩
  rw [hv, hb, ← hv, Babai.image_coordFibre (decCameron c h) ⟨0, h.s_pos⟩ he]
  simp [i]

/-- The range of the numbered block action becomes exactly the Johnson group under the hint. -/
theorem camHint_range {n : ℕ} {c : RawCameron} (h : c.WF n)
    (gens : List (Perm (Fin n))) (hN : genGroup gens = camNbar c h)
    (hp : ∀ g ∈ genGroup gens, ∀ B ∈ blockSets n (camBlocks c),
      (g : Perm (Fin n)) '' B ∈ blockSets n (camBlocks c)) :
    (blockPhi n (camBlocks c) (camBlocks_wf h) gens hp).range.map
      (Equiv.permCongrHom (camHintEquiv h)).toMonoidHom = Babai.JohnsonA c.k c.t := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.val ∈ camNbar c h := hN ▸ g.property
    obtain ⟨p, hmem, he⟩ := hg
    change (Equiv.permCongrHom (camHintEquiv h))
      (blockPhi n (camBlocks c) (camBlocks_wf h) gens hp g) ∈ Babai.JohnsonA c.k c.t
    rw [camHint_conjugates h gens hp g p he]
    exact hmem _
  · intro a ha
    let w := Babai.wreathPerm (fun _ : Fin c.s => a) 1
    let g := (Equiv.permCongrHom (decCameron c h)).symm w
    have he : (Equiv.permCongrHom (decCameron c h)) g = w :=
      (Equiv.permCongrHom (decCameron c h)).apply_symm_apply w
    have hg : g ∈ genGroup gens := by
      rw [hN]
      change (Equiv.permCongrHom (decCameron c h)) g ∈
        Babai.basePower (Babai.JohnsonA c.k c.t) c.s
      rw [he]
      exact ⟨fun _ => a, fun _ => ha, rfl⟩
    refine ⟨blockPhi n (camBlocks c) (camBlocks_wf h) gens hp ⟨g, hg⟩,
      ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    exact camHint_conjugates h gens hp ⟨g, hg⟩ (fun _ => a) he

/-- Computed form of `camBlocks_acts`, using the explicit hint identification. -/
theorem camBlockAction_hint {n : ℕ} {c : RawCameron} (h : c.WF n)
    (gs : RawGens) (hw : RawGens.WF n gs) (hN : decGroup n gs = camNbar c h) :
    (decGroup (camBlocks c).length (camBlockAction (c, gs))).map
      (Equiv.permCongrHom (camHintEquiv h)).toMonoidHom = Babai.JohnsonA c.k c.t := by
  have hp : ∀ g ∈ genGroup (gs.map (decPerm n)), ∀ B ∈ blockSets n (camBlocks c),
      (g : Perm (Fin n)) '' B ∈ blockSets n (camBlocks c) := by
    intro g hg B hB
    exact (camBlocks_system h).permutes g (hN ▸ hg) B hB
  have hI : ImgsOf (gs.map (decPerm n))
      ((camBlockAction (c, gs)).map (decPerm (camBlocks c).length))
      (blockPhi n (camBlocks c) (camBlocks_wf h) (gs.map (decPerm n)) hp) := by
    simpa only [blockImgsOf, map_encPerm_decPerm hw, camBlockAction] using
      imgsOf_blockPhi (camBlocks_wf h) hp
  rw [decGroup, ← hI.range_eq_genGroup]
  exact camHint_range h _ hN hp

/-- Feed the computed alternating-base generators to the block action. -/
def camJohnsonGens (p : RawCameron × RawGens) : RawGens :=
  camBlockAction (p.1, rawNbar p)

theorem camPoly_johnsonGens : PolyFun camJohnsonGens :=
  (polyFun_fst.pair camPoly_rawNbar).comp camPoly_blockAction

/-- Theorem 11.2.1: the computed images, read through the hint, are `A_k^(t)`. -/
theorem camJohnsonGens_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    {gs : RawGens} (hw : RawGens.WF n gs)
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    RawGens.WF (camBlocks c).length (camJohnsonGens (c, gs)) ∧
      (decGroup (camBlocks c).length (camJohnsonGens (c, gs))).map
        (Equiv.permCongrHom (camHintEquiv h)).toMonoidHom = Babai.JohnsonA c.k c.t :=
  ⟨(camBlockAction_spec h _ (rawNbar_wf h gs) (rawNbar_spec h hw hlo hhi)).1,
    camBlockAction_hint h _ (rawNbar_wf h gs) (rawNbar_spec h hw hlo hhi)⟩

end Algo

#print axioms Algo.camHint_conjugates
#print axioms Algo.camJohnsonGens_spec
