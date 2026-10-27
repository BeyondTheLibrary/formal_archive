import Workspace.Algo.TopCosetChain
import Workspace.Algo.TopRound

/-! # Matching the supplied top-action lifting trees

The computation supplies the order of the kernel orbits. For an action into
a permutation subgroup, its ordinary permutation representation has the
same kernel and preimages. This connects the raw action routines to the
alternating-image lifting tests in `cosetGiantAWith`, the first phase of
`cosetTopAction3With` and of the window phase of top-action 4.
-/

namespace Algo

open RAM.Targets Babai Equiv

/-- The identity job precedes the supplied ordered generator list. -/
def topclJobs (p : RawTop1) : List TopCosetChainInput :=
  (top1Inputs p).map topclPrepare

section PermutationAction

variable {n m : ℕ} {dom gdom : List ℕ}
  {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {ϕ : genGroup gens →* Perm (Fin m)}

/-- The computed lift and orbit list match the checked chain itself. -/
theorem topclLoop_lift (solve : RawWinSI → RawCoset)
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (τ : Perm (Fin m)) (x y : Fin n → ℕ) :
    let p : RawTopLift :=
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y)
    LoopMatch (topclRound n solve) (topclDecode n) (decCoset n) (topclPrepare p, none)
      (topKernelWindows p.1).length 0 (topclInit (topclPrepare p, none))
      (Babai.cosetChain x y (topCosetOrbitEnum hd hg hI).windows (preimageSet ϕ τ)) := by
  dsimp only
  have h := topclLoop_chain (n := n) (P := topclPrepare
    (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y)) solve (by simp [topclPrepare])
  simpa only [topclPrepare, topCosetOrbitEnum, decStrN_encStrN,
    decCoset_topCosetStart hd hg hI] using h

/-- The phase has exactly the supplied orbit count as its available budget. -/
theorem topcl_width_lift (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ)
    (solve : RawWinSI → RawCoset) :
    (topclRound n solve).width (topclPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y), none) = orbCount ϕ := by
  change (topKernelWindows _).length = _
  have h := (perm_topKernelWindows hd hg hI).length_eq
  simpa only [List.length_map, length_orbitList, orbCount] using h

end PermutationAction

section SubgroupAction

variable {n m : ℕ} {dom gdom : List ℕ}
  {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {H : Subgroup (Perm (Fin m))} {ψ : genGroup gens →* H}

theorem topcl_preimage_subtype (ψ : genGroup gens →* H) (τ : H) :
    preimageSet (H.subtype.comp ψ) (τ : Perm (Fin m)) = preimageSet ψ τ := by
  ext σ
  simp only [preimageSet, Set.mem_setOf_eq, MonoidHom.comp_apply, Subgroup.subtype_apply]
  exact exists_congr (fun _ => Subtype.ext_iff.symm)

theorem topcl_kernel_subtype (ψ : genGroup gens →* H) :
    kerSubgroup (H.subtype.comp ψ) = kerSubgroup ψ := by
  apply SetLike.coe_injective
  rw [← preimageSet_one, ← preimageSet_one]
  exact topcl_preimage_subtype ψ 1

/-- The supplied orbit record for an action with subgroup codomain. -/
noncomputable def topclSubgroupOrbitEnum (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs (H.subtype.comp ψ)) : OrbitEnum (kerSubgroup ψ) where
  windows := (topKernelWindows
    ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))).map (winSet n)
  spec := by rw [← topcl_kernel_subtype ψ]; exact perm_topKernelWindows hd hg hI

/-- The prepared parent instances are exactly the checked lifting calls,
including their order and their original strings. -/
theorem topclJobs_decode (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs (H.subtype.comp ψ)) (S : List H) (x y : Fin n → ℕ) :
    let p : RawTop1 :=
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (fun τ => encPerm m τ), encStrN x, encStrN y)
    (topclJobs p).map (fun P => topclDecode n (P, none)) =
      (cosetTopAction1 ψ x y S).calls := by
  dsimp only
  have he : top1Inputs
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (fun τ => encPerm m τ), encStrN x, encStrN y) =
      (1 :: S).map (fun τ : H =>
        (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
          encPerm m τ, encStrN x, encStrN y)) := by
    simp [top1Inputs, rawOne, hg, encPerm_one]
  rw [calls_cosetTopAction1, topclJobs, he, List.map_map, List.map_map]
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp_apply, topclDecode, Option.elim_none, topclPrepare,
    decStrN_encStrN, decCoset_topCosetStart hd hg hI, topcl_preimage_subtype]

/-- This is the very expansion substituted for each requested generator
by `cosetGiantAWith`, specialized below to its alternating codomain. -/
theorem topclLoop_expanded_lift (solve : RawWinSI → RawCoset)
    (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs (H.subtype.comp ψ)) (τ : H) (x y : Fin n → ℕ) :
    let p : RawTopLift :=
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y)
    LoopMatch (topclRound n solve) (topclDecode n) (decCoset n) (topclPrepare p, none)
      (topKernelWindows p.1).length 0 (topclInit (topclPrepare p, none))
      ((cosetLift ψ x y τ).expand (fun J => Babai.cosetChain J.x J.y
        (topclSubgroupOrbitEnum hd hg hI).windows J.K)) := by
  dsimp only
  simp only [cosetLift, SIReduction.expand, SIReduction.bind_done]
  have h := topclLoop_lift solve hd hg hI (τ : Perm (Fin m)) x y
  rw [topcl_preimage_subtype] at h
  exact h

end SubgroupAction

/-- Every lifting job of the live supplied-generator phase has an exact raw
match, in its requested order. This includes the identity and either of the
two supplied generators. No equality with `altGens` is required. -/
theorem topclLoop_giantA_jobs {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ψ : genGroup gens →* alternatingGroup (Fin m)}
    (solve : RawWinSI → RawCoset) (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ((alternatingGroup (Fin m)).subtype.comp ψ))
    (S : List (alternatingGroup (Fin m))) (x y : Fin n → ℕ) :
    ∀ J ∈ (cosetTopAction1 ψ x y S).calls,
      ∃ p : RawTopLift,
        LoopMatch (topclRound n solve) (topclDecode n) (decCoset n) (topclPrepare p, none)
          (topKernelWindows p.1).length 0 (topclInit (topclPrepare p, none))
          (Babai.cosetChain J.x J.y (topclSubgroupOrbitEnum hd hg hI).windows J.K) := by
  intro J hJ
  rw [calls_cosetTopAction1, List.mem_map] at hJ
  obtain ⟨τ, _, rfl⟩ := hJ
  refine ⟨(((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
    encPerm m τ, encStrN x, encStrN y), ?_⟩
  have h := topclLoop_expanded_lift solve hd hg hI τ x y
  simpa only [cosetLift, SIReduction.expand, SIReduction.bind_done] using h

end Algo
