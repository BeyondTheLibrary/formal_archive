import Workspace.Algo.TopOrbits
import Workspace.TopAction.CosetRounds

/-! # The raw coset for a lifting test

Proposition 12.0.1 starts with the preimage of the requested top permutation.
The coset form keeps the original strings. A computed lift supplies its
representative, so no equality with the chosen `Babai.liftRep` is needed.
-/

namespace Algo

open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-- Compute the preimage coset, or the empty coset when the image is absent. -/
def topCosetStart (p : RawAction × RawPerm) : RawCoset :=
  (actPreimage p).map (fun r => (topKernel p.1, r))

theorem polyFun_topCosetStart : PolyFun topCosetStart := by
  have hs : PolyFun (fun p : RawPerm × RawGens => some (p.2, p.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_some
  refine ((polyFun_actPreimage.pair (polyFun_fst.comp polyFun_topKernel)).comp
    (PolyFun.optionElim (polyFun_const none) hs)).of_eq ?_
  intro p
  cases h : actPreimage p <;> simp [topCosetStart, h]

/-- Every supplied lift gives the same preimage coset. -/
theorem preimageSet_eq_smul_of_lift {Ω H : Type*} [Group H]
    {G : Subgroup (Perm Ω)} (ϕ : G →* H) (σ : G) :
    preimageSet ϕ (ϕ σ) = (σ : Perm Ω) • (kerSubgroup ϕ : Set (Perm Ω)) := by
  ext τ
  constructor
  · rintro ⟨hτ, he⟩
    refine ⟨(σ : Perm Ω)⁻¹ * τ, mem_kerSubgroup.2 ⟨mul_mem (inv_mem σ.2) hτ, ?_⟩,
      by change (σ : Perm Ω) * ((σ : Perm Ω)⁻¹ * τ) = τ; group⟩
    change ϕ (σ⁻¹ * ⟨τ, hτ⟩) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨hνG, hνϕ⟩ := mem_kerSubgroup.1 hν
    refine ⟨mul_mem σ.2 hνG, ?_⟩
    change ϕ (σ * ⟨ν, hνG⟩) = ϕ σ
    rw [map_mul, hνϕ, mul_one]

section Action

variable {n m : ℕ} {dom gdom : List ℕ}
  {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {ϕ : genGroup gens →* Perm (Fin m)}

/-- The raw initial state is exactly the candidate set in `cosetLift`.
Neither a chosen lifting representative nor an equality of returned values
is assumed. -/
theorem decCoset_topCosetStart (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) :
    decCoset n (topCosetStart
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm m τ)) =
        preimageSet ϕ τ := by
  cases hr : actPreimage
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm m τ) with
  | none =>
    have hn := (actPreimage_eq_none_iff hd hg hI τ).1 hr
    simp [topCosetStart, hr, preimageSet_eq_empty ϕ hn, decCoset]
  | some r =>
    obtain ⟨σ, hσ, rfl, he⟩ := actPreimage_eq_some hd hg hI τ hr
    simp only [topCosetStart, hr, Option.map_some, decCoset_some, decPerm_encPerm,
      decGroup_topKernel hd hg hI]
    rw [← he, preimageSet_eq_smul_of_lift]

/-- The computed list contains each kernel orbit once. Thus the checked
tree may read this order directly through its supplied `OrbitEnum`. -/
theorem perm_topKernelWindows (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) :
    ((topKernelWindows
      ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))).map (winSet n)).Perm
        (orbitList (kerSubgroup ϕ)) := by
  classical
  let p : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
  have hn : ((topKernelWindows p).map (winSet n)).Nodup :=
    nodup_decoded_winOrbits (wf_tidyGens hd _) hd
  have ho : (orbitList (kerSubgroup ϕ)).Nodup := by
    unfold orbitList
    exact List.Nodup.map orbitRel.Quotient.orbit_injective (Finset.nodup_toList _)
  have hf : (topKernelWindows p).map (winSet n) ⊆ orbitList (kerSubgroup ϕ) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact topKernelWindows_mem hd hg hI hv
  have hb : orbitList (kerSubgroup ϕ) ⊆ (topKernelWindows p).map (winSet n) := by
    intro w hw
    obtain ⟨u, rfl⟩ := mem_orbitList hw
    have hc : u ∈ ⋃ v ∈ (topKernelWindows p).map (winSet n), v := by
      change u ∈ ⋃ v ∈ (winOrbits (tidyGens (dom, actKerGens p), rawOne dom)).map (winSet n), v
      rw [iUnion_decoded_winOrbits (wf_tidyGens hd _) hd]
      trivial
    obtain ⟨v, hv, hu⟩ := Set.mem_iUnion₂.1 hc
    obtain ⟨a, ha⟩ := mem_orbitList (hf hv)
    rw [ha] at hu hv
    rwa [← (orbit_eq_iff (a := u) (b := a)).2 hu] at hv
  exact (hn.subperm hf).antisymm (ho.subperm hb)

/-- This record chooses no order: it records the output of `topKernelWindows`. -/
noncomputable def topCosetOrbitEnum (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) : OrbitEnum (kerSubgroup ϕ) :=
  ⟨_, perm_topKernelWindows hd hg hI⟩

end Action

end Algo
