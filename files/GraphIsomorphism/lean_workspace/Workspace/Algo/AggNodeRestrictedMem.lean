import Workspace.Algo.AggNodeTupleTransport

/-! # Polynomial membership of a prescribed restriction

The candidate can lie outside the subgroup. It suffices that it preserves
the source set. Membership in the restricted subgroup then says exactly
that a group element agrees with the candidate on every source point.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev AggnRestrictedMemInput := (List ℕ × RawGens) × (List ℕ × RawPerm)

def aggnRestrictedMem (p : AggnRestrictedMemInput) : Bool :=
  rawMem ((p.2.1,rawRestrictGens (p.1,p.2.1)),rawRestrictPerm p.2)

theorem aggnPolyFun_restrictedMem : PolyFun aggnRestrictedMem := by
  have hu : PolyFun (fun p : AggnRestrictedMemInput => p.2.1) := polyFun_snd.comp polyFun_fst
  have hg : PolyFun (fun p : AggnRestrictedMemInput => rawRestrictGens (p.1,p.2.1)) :=
    (polyFun_fst.pair hu).comp polyFun_rawRestrictGens
  exact ((hu.pair hg).pair (polyFun_snd.comp polyFun_rawRestrictPerm)).comp polyFun_rawMem

theorem aggnRawMem_spec {m : ℕ} {dom : List ℕ} {gs : RawGens} {r : RawPerm}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hr : RawPerm.WF m r) :
    rawMem ((dom,gs),r) = true ↔ decPerm m r ∈ decGroup m gs := by
  have h := rawMem_spec dom hd (gs.map (decPerm m)) (decPerm m r)
  simpa only [map_encPerm_decPerm hw,encPerm_decPerm hr] using h

theorem aggnRestrictedGens_wf {m : ℕ} {dom u : List ℕ} {gs : RawGens}
    (hu : u.Nodup) (hlt : ∀ a ∈ u,a < m) (hw : RawGens.WF m gs)
    (hinv : IsInvariant (decGroup m gs) (winSet m u)) :
    RawGens.WF u.length (rawRestrictGens ((dom,gs),u)) := by
  intro r hr
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hr
  have hgH : decPerm m g ∈ decGroup m gs := Subgroup.subset_closure (List.mem_map.mpr ⟨g,hg,rfl⟩)
  rw [← encPerm_decPerm (hw g hg),rawRestrictPerm_spec hu hlt hinv hgH]
  exact wf_encPerm _ _

theorem aggnRestrictedMem_spec {m : ℕ} {dom u : List ℕ} {gs : RawGens} {r : RawPerm}
    (hu : u.Nodup) (hlt : ∀ a ∈ u,a < m) (hw : RawGens.WF m gs) (hr : RawPerm.WF m r)
    (hinv : IsInvariant (decGroup m gs) (winSet m u))
    (hmap : (decPerm m r) '' winSet m u = winSet m u) :
    aggnRestrictedMem ((dom,gs),(u,r)) = true ↔
      ∃ g ∈ decGroup m gs,∀ a ∈ winSet m u,g a = decPerm m r a := by
  let K := aggnSetStab (winSet m u)
  have hK := aggnSetStab_invariant (winSet m u)
  have hrK : decPerm m r ∈ K := hmap
  have he : rawRestrictPerm (u,r) =
      encPerm u.length (winRestrictHom m u hu hlt K hK ⟨decPerm m r,hrK⟩) := by
    simpa only [encPerm_decPerm hr] using rawRestrictPerm_spec hu hlt hK hrK
  have hgw := aggnRestrictedGens_wf (dom := dom) hu hlt hw hinv
  have hG := decGroup_rawRestrictGens hu hlt dom (gs.map (decPerm m)) hinv
  rw [map_encPerm_decPerm hw] at hG
  rw [aggnRestrictedMem,aggnRawMem_spec rfl hgw (he ▸ wf_encPerm _ _),he,decPerm_encPerm,hG]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g.val,g.property,(aggnRestrict_eq_iff hu hlt hinv hK g ⟨decPerm m r,hrK⟩).mp hg⟩
  · rintro ⟨g,hg,heq⟩
    exact ⟨⟨g,hg⟩,(aggnRestrict_eq_iff hu hlt hinv hK ⟨g,hg⟩ ⟨decPerm m r,hrK⟩).mpr heq⟩

end Algo
