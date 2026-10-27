import Workspace.Algo.AggNodeTransitivityDegree
import Workspace.Master.Case2bFamily

/-! # Transitivity under the numbering of an invariant set -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

private theorem multipleTransitive_map {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {G : Subgroup (Perm α)} {d : ℕ} (h : IsMultiplyTransitive G d) :
    IsMultiplyTransitive (G.map (permCongrHom e).toMonoidHom) d := by
  rw [isMultiplyTransitive_iff] at h ⊢
  refine ⟨by simpa only [Fintype.card_congr e] using h.1, ?_⟩
  letI := h.2
  constructor
  intro p q
  obtain ⟨g, hg⟩ := exists_smul_eq G (p.trans e.symm.toEmbedding) (q.trans e.symm.toEmbedding)
  refine ⟨⟨permCongrHom e g.val, ⟨g.val, g.property, rfl⟩⟩, ?_⟩
  ext i
  have hi := congrArg (fun f : Fin d ↪ α => f i) hg
  have hi' : g.val (e.symm (p i)) = e.symm (q i) := hi
  change e (g.val (e.symm (p i))) = q i
  rw [hi', e.apply_symm_apply]

theorem aggnDegtrans_map {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (G : Subgroup (Perm α)) :
    degtrans (G.map (permCongrHom e).toMonoidHom) = degtrans G := by
  have hback : (G.map (permCongrHom e).toMonoidHom).map
      (permCongrHom e.symm).toMonoidHom = G := by
    ext g
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      have he : permCongrHom e.symm (permCongrHom e b) = b := by ext x; simp
      change permCongrHom e.symm (permCongrHom e b) ∈ G
      rwa [he]
    · intro hg
      exact ⟨permCongrHom e g, ⟨g, hg, rfl⟩, by ext x; simp⟩
  apply le_antisymm
  · have h := multipleTransitive_map e.symm (degtrans_spec (G.map (permCongrHom e).toMonoidHom)).1
    rw [hback] at h
    exact le_csSup (bddAbove_multiplyTransitive G) h
  · exact le_csSup (bddAbove_multiplyTransitive _) (multipleTransitive_map e (degtrans_spec G).1)

def aggnMajorityDegree (p : List ℕ × RawGens) : ℕ :=
  aggnDegtrans (aggnLargeOrbitPoints p, aggnMajorityRestricted p)

theorem aggnPolyFun_majorityDegree : PolyFun aggnMajorityDegree :=
  (aggnPolyFun_largeOrbitPoints.pair aggnPolyFun_majorityRestricted).comp aggnPolyFun_degtrans

theorem aggnMajorityDegree_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnMajorityDegree (dom, gs) =
      degtransOn (decGroup m gs) (winSet m (aggnLargeOrbitPoints (dom, gs))) := by
  rw [aggnMajorityDegree, aggnDegtrans_spec rfl
    (show RawGens.WF _ (aggnMajorityRestricted (dom, gs)) from wf_tidyGens rfl _),
    aggnMajorityRestricted_spec hd hw, range_winRestrictHom, aggnDegtrans_map,
    degtransOn_eq_degtrans _ (aggnLargeOrbitPoints_invariant hd hw)]

/-- The paper's bound is used only after the giant branch has failed. -/
theorem aggnMajorityDegree_bounds {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom, gs) = true) (hg : aggnCase2a (dom, gs) = false) :
    1 ≤ aggnMajorityDegree (dom, gs) ∧ aggnMajorityDegree (dom, gs) ≤ 5 := by
  rw [aggnMajorityDegree_spec hd hw]
  constructor
  · obtain ⟨u, he, _⟩ := aggnLargeOrbitPoints_orbit hd hw hc
    rw [he]
    exact one_le_degtransOn_orbit _ _
  · rw [degtransOn_eq_degtrans _ (aggnLargeOrbitPoints_invariant hd hw)]
    apply degtrans_restrict_le_five _ (aggnLargeOrbitPoints_invariant hd hw)
    intro h
    have ht := (aggnCase2a_spec hd hw).mpr h
    rw [hg] at ht
    contradiction

end Algo
