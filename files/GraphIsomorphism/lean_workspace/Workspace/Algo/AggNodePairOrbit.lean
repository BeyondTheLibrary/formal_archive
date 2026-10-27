import Workspace.Algo.AggNodeTransitivityTransport
import Workspace.Machine.CIRaw

/-! # Polynomial computation of ordered-pair orbits

Case 2b uses orbits of the diagonal action on ordered pairs. The numbered
square action is the same polynomial construction used for Coset
Intersection, with the same permutation in both factors.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

def aggnPairAction (m : ℕ) : Perm (Fin m) →* Perm (Fin (m*m)) where
  toFun g := CIReduction.action m (g,g)
  map_one' := map_one (CIReduction.action m)
  map_mul' g h := (CIReduction.action m).map_mul (g,g) (h,h)

theorem aggnPairAction_apply {m : ℕ} (g : Perm (Fin m)) (a b : Fin m) :
    aggnPairAction m g (finProdFinEquiv (a,b)) = finProdFinEquiv (g a,g b) := by
  simp [aggnPairAction, CIReduction.action, Babai.CosetToString.productAction]

def aggnPairGens (p : List ℕ × RawGens) : RawGens :=
  p.2.map (fun g => CIReduction.rawAction (rawOne p.1,g,g))

def aggnPairName (p : ℕ × (ℕ × ℕ)) : ℕ := p.2.2 + p.1 * p.2.1

def aggnPairOrbit (p : (List ℕ × RawGens) × (ℕ × ℕ)) : List ℕ :=
  rawOrbit (aggnPairGens p.1, aggnPairName (p.1.1.length,p.2))

theorem aggnPolyFun_pairGens : PolyFun aggnPairGens := by
  have hf : PolyFun (fun p : List ℕ × RawPerm => CIReduction.rawAction (rawOne p.1,p.2,p.2)) :=
    ((polyFun_fst.comp polyFun_rawOne).pair (polyFun_snd.pair polyFun_snd)).comp CIReduction.polyFun_rawAction
  exact hf.mapParam

theorem aggnPolyFun_pairName : PolyFun aggnPairName :=
  (polyFun_snd.comp polyFun_snd).add (polyFun_fst.mul (polyFun_snd.comp polyFun_fst))

theorem aggnPolyFun_pairOrbit : PolyFun aggnPairOrbit :=
  ((polyFun_fst.comp aggnPolyFun_pairGens).pair
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_length).pair polyFun_snd).comp
      aggnPolyFun_pairName)).comp polyFun_rawOrbit

theorem aggnPairGens_enc {m : ℕ} {dom : List ℕ} (hd : dom.length = m)
    (gs : List (Perm (Fin m))) :
    aggnPairGens (dom,gs.map (encPerm m)) = (gs.map (aggnPairAction m)).map (encPerm (m*m)) := by
  have hone : rawOne dom = encPerm m 1 := by simp [rawOne, hd, encPerm_one]
  simp only [aggnPairGens, List.map_map, hone]
  apply List.map_congr_left
  intro g _
  exact CIReduction.rawAction_spec 1 g g

theorem aggnPairGens_wf {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    RawGens.WF (m*m) (aggnPairGens (dom,gs)) := by
  rw [← map_encPerm_decPerm hw, aggnPairGens_enc hd]
  exact wf_map_encPerm _ _

theorem aggnPairGens_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    decGroup (m*m) (aggnPairGens (dom,gs)) = (decGroup m gs).map (aggnPairAction m) := by
  have he := aggnPairGens_enc hd (gs.map (decPerm m))
  rw [map_encPerm_decPerm hw] at he
  rw [he, decGroup_map_encPerm]
  simp only [decGroup, genGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp

/-- Exact orbital membership; no transitivity assumption is required. -/
theorem aggnPairOrbit_mem {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (a b u v : Fin m) :
    aggnPairName (m,(u.val,v.val)) ∈ aggnPairOrbit ((dom,gs),(a.val,b.val)) ↔
      ∃ g ∈ decGroup m gs, g a = u ∧ g b = v := by
  let ab : Fin (m*m) := finProdFinEquiv (a,b)
  let uv : Fin (m*m) := finProdFinEquiv (u,v)
  change uv.val ∈ rawOrbit (aggnPairGens (dom,gs), aggnPairName (dom.length,(a.val,b.val))) ↔ _
  rw [hd]
  change uv.val ∈ rawOrbit (aggnPairGens (dom,gs), ab.val) ↔ _
  change uv ∈ winSet (m*m) (rawOrbit (aggnPairGens (dom,gs),ab.val)) ↔ _
  rw [winSet_rawOrbit (aggnPairGens_wf hd hw), aggnPairGens_spec hd hw]
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨k,hk,hkg⟩ := g.property
    have hh : aggnPairAction m k ab = uv := hkg ▸ hg
    change aggnPairAction m k (finProdFinEquiv (a,b)) = finProdFinEquiv (u,v) at hh
    rw [aggnPairAction_apply] at hh
    have he := finProdFinEquiv.injective hh
    exact ⟨k,hk,Prod.mk.inj he⟩
  · rintro ⟨g,hg,ha,hb⟩
    refine ⟨⟨aggnPairAction m g,⟨g,hg,rfl⟩⟩, ?_⟩
    change aggnPairAction m g (finProdFinEquiv (a,b)) = finProdFinEquiv (u,v)
    rw [aggnPairAction_apply,ha,hb]

end Algo
