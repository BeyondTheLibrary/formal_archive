import Workspace.Algo.TopMasterCameronDataLink

/-! # The computed coordinate rows retain the descent block labels
The subgroup computed from the signed action is the preimage of the
Cameron subgroup through the numbered block action. The recovered first
coordinate therefore acts on the union blocks through their retained labels.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

noncomputable def MasterHintBlockLink.changeGroup {Ω : Type*}
    {G H : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hG : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {hH : ∀ g ∈ H, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} {φ : G →* Perm (Fin m)} {ψ : H →* Perm (Fin m)}
    (L : MasterHintBlockLink (t := t) hG φ) (h : H = G)
    (he : ∀ g : H, ψ g = φ (MulEquiv.subgroupCongr h g)) :
    MasterHintBlockLink (t := t) hH ψ := by
  subst H
  have he' : ψ = φ := MonoidHom.ext he
  subst ψ
  exact ⟨L.label, L.action⟩

section Blocks
variable {n m : ℕ} {p : RawAction} {c : RawCameron}
    {φ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom)
    {B : Set (Set (Fin n))} (hs : IsSystemOfImprimitivity (decGroup n p.1.2) Set.univ B)
    (e : Fin m ≃ B)
    (hG : (decGroup m p.2.2).map e.permCongrHom.toMonoidHom =
      onBlocks (decGroup n p.1.2) B hs.permutes)
    (hrow : ∀ g : decGroup n p.1.2,
      e.permCongrHom (φ g) = blockHom (decGroup n p.1.2) B hs.permutes g)

include hp hhi hrow in
 theorem camLiftGens_preim_blocks :
    decGroup n (camLiftGens (c, p)) =
      preimSubgroup (blockHom (decGroup n p.1.2) B hs.permutes)
        ((camNbar c h).map e.permCongrHom.toMonoidHom) := by
  rw [camLiftGens_spec hp h hhi]
  ext g
  rw [mem_camLiftSubgroup, mem_preimSubgroup]
  constructor
  · rintro ⟨hg, hφ⟩
    exact ⟨hg, ⟨φ ⟨g, hg⟩, hφ, hrow ⟨g, hg⟩⟩⟩
  · rintro ⟨hg, a, ha, he⟩
    refine ⟨hg, ?_⟩
    have he' : a = φ ⟨g, hg⟩ := e.permCongrHom.injective (he.trans (hrow ⟨g, hg⟩).symm)
    exact he' ▸ ha

include hG hlo hhi in
 theorem camMappedNbar_le_blocks :
    (camNbar c h).map e.permCongrHom.toMonoidHom ≤ onBlocks (decGroup n p.1.2) B hs.permutes := by
  rw [← hG]
  exact Subgroup.map_mono (camNbar_normal h (decGroup m p.2.2) hlo hhi).le

noncomputable def camLiftUnionSystem :
    IsSystemOfImprimitivity (decGroup n (camLiftGens (c, p))) Set.univ
      (descentBlocks (blockImage e (blockSets m (camBlocks c)))) := by
  rw [camLiftGens_preim_blocks hp h hhi hs e hrow]
  exact isSystemOfImprimitivity_descentBlocks hs (camMappedNbar_le_blocks h hhi hlo hs e hG)
    (isSystemOfImprimitivity_map_permCongrHom e (camBlocks_system h))

 theorem camLiftGiantHom_blocks (g : decGroup n (camLiftGens (c, p))) :
    camLiftGiantHom hp h hhi g =
      (camMappedPointHom h e).comp (masterDescentBlockHom hs)
        (MulEquiv.subgroupCongr (camLiftGens_preim_blocks hp h hhi hs e hrow) g) := by
  apply congrArg (camNbarPointHom h)
  apply Subtype.ext
  apply e.permCongrHom.injective
  change e.permCongrHom (φ (Subgroup.inclusion (camLiftGens_le hp h hhi) g)) =
    e.permCongrHom _
  rw [hrow]
  exact (congrArg Subtype.val ((e.permCongrHom.subgroupMap (camNbar c h)).apply_symm_apply
    (masterDescentBlockHom hs
      (MulEquiv.subgroupCongr (camLiftGens_preim_blocks hp h hhi hs e hrow) g)))).symm

noncomputable def camLiftRowsHintLink :
    MasterHintBlockLink (t := c.t) (camLiftUnionSystem hp h hhi hlo hs e hG hrow).permutes
      (camLiftGiantHom hp h hhi) :=
  ((camMappedHintLink h e).pullback hs (camMappedNbar_le_blocks h hhi hlo hs e hG)
    (isSystemOfImprimitivity_map_permCongrHom e (camBlocks_system h))).changeGroup
      (camLiftGens_preim_blocks hp h hhi hs e hrow) (camLiftGiantHom_blocks hp h hhi hs e hrow)
end Blocks
end Algo
