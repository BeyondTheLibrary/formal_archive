import Workspace.Algo.TopMasterHintLink

/-! # Cameron's coordinate hint retains its block-action equation
The raw coordinate blocks and their subset labels were already decoded.
The recovered point action moves each fiber by the same subset action,
so its kernel is precisely the kernel of that retained block action.
-/
namespace Algo
open Babai Equiv
open scoped Classical

 noncomputable def camHintBlockLabel {n : ℕ} {c : RawCameron} (h : c.WF n) :
    blockSets n (camBlocks c) ≃ binom (Fin c.k) c.t :=
  (blockEquiv n (camBlocks c) (camBlocks_wf h)).symm.trans (camHintEquiv h)

 theorem camHintBlockLabel_fibre {n : ℕ} {c : RawCameron} (h : c.WF n)
    (B : blockSets n (camBlocks c)) :
    coordFibre (decCameron c h) ⟨0, h.s_pos⟩ (camHintBlockLabel h B) = (B : Set (Fin n)) := by
  let i := (blockEquiv n (camBlocks c) (camBlocks_wf h)).symm B
  have he := camHintValue_fibre h i
  change _ = coordFibre _ _ (camHintBlockLabel h B) at he
  rw [← he]
  exact congrArg Subtype.val ((blockEquiv n (camBlocks c) (camBlocks_wf h)).apply_symm_apply B)

 theorem camNbarPointHom_image_fibre {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : camNbar c h) (T : binom (Fin c.k) c.t) :
    (g : Perm (Fin n)) '' coordFibre (decCameron c h) ⟨0, h.s_pos⟩ T =
      coordFibre (decCameron c h) ⟨0, h.s_pos⟩ (tAction c.t (camNbarPointHom h g) T) := by
  let w := camNbarIntoBase h g
  have he := camWreath_decomp (camBaseAsWreath w)
  rw [(camBase_parts h.t_pos (by have := h.k_gt; omega) w).1] at he
  exact image_coordFibre (decCameron c h) ⟨0, h.s_pos⟩ he T

 noncomputable def camNbarHintLink {n : ℕ} {c : RawCameron} (h : c.WF n) :
    MasterHintBlockLink (t := c.t) (camBlocks_system h).permutes (camNbarPointHom h) where
  label := camHintBlockLabel h
  action := by
    intro g
    apply Equiv.ext
    intro T
    apply coordFibre_injective (decCameron c h) ⟨0, h.s_pos⟩
    change coordFibre _ _ (camHintBlockLabel h
      (blockHom _ _ (camBlocks_system h).permutes g ((camHintBlockLabel h).symm T))) = _
    rw [camHintBlockLabel_fibre, blockHom_apply_coe,
      ← camHintBlockLabel_fibre h ((camHintBlockLabel h).symm T), Equiv.apply_symm_apply]
    exact camNbarPointHom_image_fibre h g T

 theorem camNbarPointHom_kernel {n : ℕ} {c : RawCameron} (h : c.WF n) :
    kerSubgroup (camNbarPointHom h) =
      blockKernel (camNbar c h) (blockSets n (camBlocks c)) (camBlocks_system h).permutes :=
  (camNbarHintLink h).kernel h.t_pos (by have := h.k_gt; omega)

end Algo
