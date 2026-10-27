import Workspace.Algo.AggCanonRecompute

/-! # Opening a test set

Claim C1 gives the set stabilizer. The action routine then finds each
new generator's image, and restricts that image to the named test set.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- The image of one generator in the labels of the test set. -/
def aggnInitialImg (p : (RawAction × List ℕ) × RawPerm) : RawPerm :=
  normPerm (p.1.2, rawRestrictPerm (p.1.2, rawImgOf (p.1.1, p.2)))

def aggnInitialState (p : RawAction × List ℕ) : RawLCSt :=
  ([], topStab p, (topStab p).map (fun g => aggnInitialImg (p, g)))

theorem aggnPolyFun_initialImg : PolyFun aggnInitialImg := by
  have hr : PolyFun (fun p : (RawAction × List ℕ) × RawPerm => p.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hi : PolyFun (fun p : (RawAction × List ℕ) × RawPerm => rawImgOf (p.1.1, p.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawImgOf
  exact (hr.pair ((hr.pair hi).comp polyFun_rawRestrictPerm)).comp polyFun_normPerm

theorem aggnPolyFun_initialState : PolyFun aggnInitialState :=
  (polyFun_const []).pair (polyFun_topStab.pair
    ((polyFun_id.pair polyFun_topStab).comp (PolyFun.mapParam aggnPolyFun_initialImg)))

section Spec
variable {n m : ℕ} {A : RawAction} {xs row : List ℕ}
  {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

theorem aggnRawImgOf_spec (hA : RawAction.WF n m A ϕ)
    {g : RawPerm} (hg : RawPerm.WF n g) (hmem : decPerm n g ∈ decGroup n A.1.2) :
    rawImgOf (A, g) = encPerm m (ϕ ⟨decPerm n g, hmem⟩) := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have h := rawImgOf_spec hd hm hi hmem
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hg] at h
  exact h

/-- Restricting the ambient image computes exactly the test-set action. -/
theorem aggnRestrict_phi {H : Subgroup (Perm (Fin n))}
    (hnd : row.Nodup) (hlt : ∀ u ∈ row, u < m)
    (hle : H ≤ bigGT ϕ (winSet m row)) (g : H) :
    rawRestrictPerm (row, encPerm m (ϕ ⟨g, stabIn_le_top (hle g.2)⟩)) =
      encPerm row.length (psiFin ϕ row hnd hlt hle g) := by
  apply List.ext_getElem
  · simp [rawRestrictPerm]
  · intro k hk hk'
    have hkrow : k < row.length := by simpa [rawRestrictPerm] using hk
    let j := psiFin ϕ row hnd hlt hle g ⟨k, hkrow⟩
    have hv := psiFin_val (ϕ := ϕ) (tdom := row) (hnd := hnd) (hlt := hlt)
      (hH := hle) g hkrow
    rw [List.getD_eq_getElem _ _ j.isLt] at hv
    simp only [rawRestrictPerm, List.getElem_map]
    rw [rawApply_encPerm m _ (hlt _ (List.getElem_mem hkrow)), ← hv,
      rawInvLookup_getElem hnd j.isLt, getElem_encPerm]

/-- Sec. 13.1, line 01: the machine state represents `W = ∅` and `H = G_T`. -/
theorem aggnInitialState_for (hc : LCCtxWF n m xs row)
    (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ) :
    StateFor hc (stages ϕ (decStrN n xs) (winSet m row) 0) (aggnInitialState (A, row)) := by
  have hG := topStab_bigGT_of_wf (A, row) ϕ hA hgiant
  have hw := topStab_wf (p := (A, row)) hA.1
  refine ⟨List.nodup_nil, by simp [aggnInitialState],
    by ext u; simp [aggnInitialState, winSet, stages, Stage.init],
    hw.1, hw.2, hG, ?_, ?_⟩
  · rintro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact wf_normPerm rfl _
  · intro hle
    refine ⟨by simp [aggnInitialState], ?_⟩
    intro i hi hi'
    have hiG : i < (topStab (A, row)).length := by simpa [aggnInitialState] using hi
    have hgmem := List.getElem_mem hiG
    have hgH : decPerm n ((topStab (A, row))[i]) ∈ decGroup n (topStab (A, row)) :=
      Subgroup.subset_closure (List.mem_map_of_mem hgmem)
    have hgG := stabIn_le_top (hle hgH)
    simp only [aggnInitialState, List.getElem_map, aggnInitialImg, decPerm_normPerm rfl]
    rw [aggnRawImgOf_spec hA (hw.1 _ hgmem) hgG,
      aggnRestrict_phi hc.nodup hc.ltM hle ⟨_, hgH⟩, decPerm_encPerm]
    rfl

end Spec
end Algo
