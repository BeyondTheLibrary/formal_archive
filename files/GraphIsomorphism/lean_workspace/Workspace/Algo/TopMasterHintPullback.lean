import Workspace.Algo.TopMasterHintLinkTransport

/-! # Retaining the label when blocks are replaced by their unions
Theorem 11.2.1 labels blocks of the block action. Step 7 of
Reduce-to-Johnson replaces each such block by its union of original
points. The same label gives the same point action on the preimage group.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

section Pullback
variable {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {C : Set (Set B)} {N : Subgroup (Perm B)}
    (hs : IsSystemOfImprimitivity G Set.univ B)
    (hN : N ≤ onBlocks G B hs.permutes) (hC : IsSystemOfImprimitivity N Set.univ C)

 noncomputable def masterDescentBlockHom :
    preimSubgroup (blockHom G B hs.permutes) N →* N :=
  ((blockHom G B hs.permutes).comp (Subgroup.inclusion (preimSubgroup_le _ _))).codRestrict N
    (fun g => (mem_preimSubgroup.mp g.property).2)

 include hN in
 theorem masterDescentBlockHom_surjective : Function.Surjective (masterDescentBlockHom hs (N := N)) := by
  intro a
  obtain ⟨g, hg, he⟩ := exists_mem_preimSubgroup hs hN a.property
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

 noncomputable def MasterHintBlockLink.pullback {m t : ℕ} {φ : N →* Perm (Fin m)}
    (L : MasterHintBlockLink (t := t) hC.permutes φ) :
    MasterHintBlockLink (t := t)
      (isSystemOfImprimitivity_descentBlocks hs hN hC).permutes
      (φ.comp (masterDescentBlockHom hs)) where
  label := (blockUnionEquiv (blockUnion_injOn hs hC)).symm.trans L.label
  action g := by
    have hb := permCongr_blockHom_descentBlocks hs hN hC g.property
      (mem_preimSubgroup.mp g.property).2
    have hh := congrArg (fun p => L.label.permCongrHom p) hb
    exact hh.trans (L.action (masterDescentBlockHom hs g))

end Pullback
end Algo
