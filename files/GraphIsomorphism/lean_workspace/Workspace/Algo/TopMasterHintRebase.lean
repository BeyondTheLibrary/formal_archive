import Workspace.Algo.TopMasterCameronBlocks

/-! # Carrying a giant hint to the current window generators
Restriction and subgroup lifting can change a generating list. Recompute
the images in the new list's order by the proved image routine. This is
the representation step needed before entering the live master dispatcher.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterRebaseImages (p : RawAction × RawGens) : RawGens :=
  p.2.map (fun r => rawImgOf (p.1, r))

def masterRebaseAction (p : RawAction × RawGens) : RawAction :=
  ((p.1.1.1, p.2), (p.1.2.1, masterRebaseImages p))

def masterRebaseHint (p : RawAction × RawWinSI × ℕ) : RawMasterHint :=
  ((p.1.2.1, masterRebaseImages (p.1, (primitiveWindowInput p.2.1).1)), p.2.2)

def masterRebaseEnter (p : RawAction × RawWinSI × ℕ) : MasterHintInput :=
  (p.2.1, masterRebaseHint p)

theorem polyFun_masterRebaseImages : PolyFun masterRebaseImages := PolyFun.mapParam polyFun_rawImgOf

theorem polyFun_masterRebaseAction : PolyFun masterRebaseAction :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_masterRebaseImages)

theorem polyFun_masterRebaseHint : PolyFun masterRebaseHint :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_fst.pair (((polyFun_snd.comp polyFun_fst).comp polyFun_primitiveWindowInput).comp
      polyFun_fst)).comp polyFun_masterRebaseImages)).pair (polyFun_snd.comp polyFun_snd)

theorem polyFun_masterRebaseEnter : PolyFun masterRebaseEnter :=
  (polyFun_snd.comp polyFun_fst).pair polyFun_masterRebaseHint

section Rebase
variable {n m : ℕ} {p : RawAction} {gs : RawGens}
  {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
  (hw : RawGens.WF n gs) (hle : decGroup n gs ≤ decGroup n p.1.2)

noncomputable def masterRebaseHom : decGroup n gs →* Perm (Fin m) :=
  ϕ.comp (Subgroup.inclusion hle)

include hp hw in
theorem masterRebaseImages_row {r : RawPerm} (hr : r ∈ gs) :
    rawImgOf (p, r) = encPerm m (masterRebaseHom (ϕ := ϕ) hle
      ⟨decPerm n r, Subgroup.subset_closure (List.mem_map_of_mem hr)⟩) := by
  have hi := rawImgOf_spec hp.1 hp.2.1 hp.2.2.2.2
    (hle (Subgroup.subset_closure (List.mem_map_of_mem hr)))
  simpa only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1,
    encPerm_decPerm (hw r hr)] using hi

include hp hw in
theorem masterRebaseAction_wf : RawAction.WF n m (masterRebaseAction (p, gs))
    (masterRebaseHom (ϕ := ϕ) hle) := by
  refine ⟨hp.1, hp.2.1, hw, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    rw [masterRebaseImages_row hp hw hle hq]
    exact wf_encPerm _ _
  · simp [masterRebaseAction, masterRebaseImages]
  · intro i hi hj
    have hh : i < gs.length := by simpa [masterRebaseAction] using hi
    simp only [masterRebaseAction, masterRebaseImages, List.getElem_map,
      masterRebaseImages_row hp hw hle (List.getElem_mem hh), decPerm_encPerm]
    rfl

theorem masterRebaseHom_giant (hgiant : IsGiantRep ϕ) (he : decGroup n gs = decGroup n p.1.2) :
    IsGiantRep (masterRebaseHom (ϕ := ϕ) hle) := by
  intro a ha
  obtain ⟨g, hg⟩ := hgiant ha
  exact ⟨⟨g, he.ge g.property⟩, hg⟩
end Rebase

/-- The new images are in precisely the order computed by `masterHintTop`. -/
theorem masterRebaseEnter_wf {n m : ℕ} {A : RawAction} {W : RawWinSI} {t : ℕ}
    {ϕ : decGroup W.1.length A.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF W.1.length m A ϕ)
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hle : decGroup W.1.length (primitiveWindowInput W).1 ≤ decGroup W.1.length A.1.2) :
    RawAction.WF W.1.length m (masterHintTop (masterRebaseEnter (A, W, t))).1
      (masterRebaseHom (ϕ := ϕ) hle) := by
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have h := masterRebaseAction_wf hp hgs hle
  exact ⟨rfl, h.2⟩
end Algo
