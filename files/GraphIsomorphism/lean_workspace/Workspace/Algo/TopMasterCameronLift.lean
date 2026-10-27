import Workspace.Algo.TopMasterCameron

/-! # The original-domain subgroup in the Cameron descent
Compose the block action with the signed coordinate action before computing
its kernel. Thus the returned generators act on the original domain, as in
Theorem 11.2.1. The first-coordinate images are then recovered for those very
generators, in their stored order.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Regard an encoded action as a surjection onto its stored image group. -/
noncomputable def camActionRange {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ) :
    decGroup n p.1.2 →* decGroup m p.2.2 :=
  ϕ.codRestrict _ (fun g => by
    change ϕ g ∈ genGroup (p.2.2.map (decPerm m))
    rw [← hp.2.2.2.2.range_eq_genGroup]
    exact ⟨g, rfl⟩)

theorem camActionRange_surjective {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ) :
    Function.Surjective (camActionRange hp) := by
  intro g
  have hg : g.val ∈ ϕ.range := hp.2.2.2.2.range_eq_genGroup.symm ▸ g.property
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, Subtype.ext ha⟩

/-- Compose the supplied action with the signed coordinate action. -/
def camLiftSign (q : RawCameron × RawAction) : RawAction :=
  (q.2.1, (camSignDom q.1, camSignImgs (q.1, q.2.2.2)))

def camLiftGens (q : RawCameron × RawAction) : RawGens := topKernel (camLiftSign q)

theorem polyFun_camLiftSign : PolyFun camLiftSign :=
  (polyFun_snd.comp polyFun_fst).pair
    ((polyFun_fst.comp camPoly_signDom).pair
      ((polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp camPoly_signImgs))

theorem polyFun_camLiftGens : PolyFun camLiftGens :=
  polyFun_camLiftSign.comp polyFun_topKernel

section Lift
variable {n m : ℕ} {p : RawAction} {c : RawCameron}
  {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
  (hp : RawAction.WF n m p ϕ) (h : c.WF m)
  (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
    wreathProduct (JohnsonS c.k c.t) c.s)

noncomputable def camLiftSignHom : decGroup n p.1.2 →* Perm (Fin (c.s * 2)) :=
  (camSignActionFin h (decGroup m p.2.2) hhi).comp (camActionRange hp)

theorem camLiftSign_wf : RawAction.WF n (c.s * 2) (camLiftSign (c, p))
    (camLiftSignHom (p := p) hp h hhi) := by
  obtain ⟨hw, hi⟩ := camSignImgs_spec h hp.2.2.2.1 hhi
  refine ⟨hp.1, camSignDom_length h, hp.2.2.1, hw, ?_, ?_⟩
  · exact hp.2.2.2.2.1.trans hi.1
  · intro i hn hs
    have hm : i < (p.2.2.map (decPerm m)).length := by
      rw [← hp.2.2.2.2.1]
      exact hn
    have he := hi.2 i hm hs
    have hf := hp.2.2.2.2.2 i hn hm
    change _ = camSignActionFin h (decGroup m p.2.2) hhi (camActionRange hp _)
    dsimp only [camLiftSign]
    rw [he]
    apply congrArg (camSignActionFin h (decGroup m p.2.2) hhi)
    exact Subtype.ext hf

/-- The subgroup selected in Theorem 11.2.1, before restricting the window. -/
noncomputable def camLiftSubgroup : Subgroup (Perm (Fin n)) :=
  ((camNbar c h).comap ϕ).map (decGroup n p.1.2).subtype

theorem mem_camLiftSubgroup {g : Perm (Fin n)} :
    g ∈ camLiftSubgroup (ϕ := ϕ) h ↔
      ∃ hg : g ∈ decGroup n p.1.2, ϕ ⟨g, hg⟩ ∈ camNbar c h := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨hg, ha⟩
    exact ⟨⟨g, hg⟩, ha, rfl⟩

include hp hhi in
theorem camLiftGens_spec : decGroup n (camLiftGens (c, p)) =
    camLiftSubgroup (ϕ := ϕ) h := by
  have hw := camLiftSign_wf hp h hhi
  have he := decGroup_topKernel hw.1 hw.2.1 hw.2.2.2.2
  rw [map_encPerm_decPerm hw.2.2.1, map_encPerm_decPerm hw.2.2.2.1] at he
  change decGroup n (camLiftGens (c, p)) = _ at he
  rw [he]
  ext g
  rw [mem_kerSubgroup, mem_camLiftSubgroup]
  constructor
  · rintro ⟨hg, he⟩
    exact ⟨hg, (camSignActionFin_eq_one h _ hhi (camActionRange hp ⟨g, hg⟩)).mp he⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, (camSignActionFin_eq_one h _ hhi (camActionRange hp ⟨g, hg⟩)).mpr he⟩

include hp h hhi in
theorem camLiftGens_le : decGroup n (camLiftGens (c, p)) ≤ decGroup n p.1.2 := by
  intro g hg
  exact ((mem_camLiftSubgroup h).mp ((camLiftGens_spec hp h hhi) ▸ hg)).choose

include hp in
theorem camLiftGens_wf : RawGens.WF n (camLiftGens (c, p)) := wf_tidyGens hp.1 _

include hp in
theorem camLiftGens_length : (camLiftGens (c, p)).length ≤ n * n := length_tidyGens hp.1 _

noncomputable def camLiftIntoNbar : decGroup n (camLiftGens (c, p)) →* camNbar c h :=
  (ϕ.comp (Subgroup.inclusion (camLiftGens_le hp h hhi))).codRestrict _ (fun g => by
    have hg : g.val ∈ camLiftSubgroup (ϕ := ϕ) h :=
      (camLiftGens_spec hp h hhi).le g.property
    obtain ⟨hg', he⟩ := (mem_camLiftSubgroup (ϕ := ϕ) h).mp hg
    exact he)

noncomputable def camLiftGiantHom : decGroup n (camLiftGens (c, p)) →* Perm (Fin c.k) :=
  (camNbarPointHom h).comp (camLiftIntoNbar hp h hhi)

theorem camLiftIntoNbar_surjective
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom) :
    Function.Surjective (camLiftIntoNbar hp h hhi) := by
  intro a
  have ham : a.val ∈ decGroup m p.2.2 := (camNbar_normal h _ hlo hhi).le a.property
  obtain ⟨g, hg⟩ := camActionRange_surjective hp ⟨a, ham⟩
  have he : ϕ g = a := congrArg Subtype.val hg
  have hg' : g.val ∈ decGroup n (camLiftGens (c, p)) := by
    rw [camLiftGens_spec hp h hhi]
    exact (mem_camLiftSubgroup h).mpr ⟨g.property, he.symm ▸ a.property⟩
  exact ⟨⟨g, hg'⟩, Subtype.ext he⟩

theorem camLiftGiantHom_giant
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom) :
    IsGiantRep (camLiftGiantHom hp h hhi) := by
  intro a ha
  obtain ⟨b, hb⟩ := camNbarPointHom_giant h ha
  obtain ⟨g, hg⟩ := camLiftIntoNbar_surjective hp h hhi hlo b
  refine ⟨g, ?_⟩
  change camNbarPointHom h (camLiftIntoNbar hp h hhi g) = a
  rw [hg, hb]

include hp hhi in
/-- Taking the preimage keeps the index used by Luks descent. -/
theorem camLiftGens_index : (decGroup n (camLiftGens (c, p))).relIndex (decGroup n p.1.2) =
    (camNbar c h).relIndex (decGroup m p.2.2) := by
  rw [camLiftGens_spec hp h hhi]
  let G := decGroup n p.1.2
  let H := (camNbar c h).comap ϕ
  change (H.map G.subtype).relIndex G = _
  calc
    (H.map G.subtype).relIndex G = (H.map G.subtype).relIndex
        ((⊤ : Subgroup G).map G.subtype) := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = H.relIndex ⊤ := Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective
    _ = (camNbar c h).relIndex (decGroup m p.2.2) := by
      change ((camNbar c h).comap ϕ).relIndex ⊤ = _
      rw [Subgroup.relIndex_comap, ← MonoidHom.range_eq_map]
      exact congrArg ((camNbar c h).relIndex) hp.2.2.2.2.range_eq_genGroup

end Lift
end Algo
