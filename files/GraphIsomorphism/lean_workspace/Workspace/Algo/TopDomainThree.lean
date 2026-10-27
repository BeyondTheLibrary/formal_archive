import Workspace.Algo.TopDomain

/-! # Domain transport of the supplied top-action 3 tree
The proof compares the three ordered lifting chains, the kernel chain, and
the conditional odd chain. The test and odd choices are transported as data.
-/
namespace Algo
open Babai Equiv
open scoped Pointwise Classical

 theorem topd_smul {Ω Ω' : Type*} (e : Ω ≃ Ω') (r : Perm Ω) (C : Set (Perm Ω)) :
    e.permCongr '' (r • C) = e.permCongr r • (e.permCongr '' C) := by
  change e.permCongr '' ((fun g => r * g) '' C) = (fun g => e.permCongr r * g) '' (e.permCongr '' C)
  rw [Set.image_image, Set.image_image]
  congr 1
  funext g
  exact e.permCongrHom.map_mul r g

 theorem topdTop3_calls_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)}
    {m : ℕ} (ϕ : G →* Perm (Fin m)) (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → ℕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    (cosetTopAction3With ϕ S O E x y).calls =
      (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).calls ++
      (if MapsOntoGiant ϕ x then
        (Babai.cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).calls ++
          (if ϕ.range ≤ alternatingGroup (Fin m) then [] else
            (Babai.cosetChain x y E.windows (O.representative • (kerSubgroup ϕ : Set (Perm Ω)))).calls)
       else []) := by
  rw [cosetTopAction3With, SIReduction.calls_bind, run_cosetGiantAWith _ S hS]
  by_cases hg : MapsOntoGiant ϕ x
  · rw [if_pos ((mapsOnto_altHom_self_iff ϕ x).mpr hg), if_pos hg, if_neg (by simp)]
    by_cases he : ϕ.range ≤ alternatingGroup (Fin m)
    · simp only [SIReduction.calls_bind, if_pos he, SIReduction.calls_done]
    · simp only [SIReduction.calls_bind, if_neg he, SIReduction.calls_done, List.append_nil]
  · rw [if_neg (fun h => hg ((mapsOnto_altHom_self_iff ϕ x).mp h)), if_neg hg, if_pos rfl]
    rfl

section Congruence
variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω] [DecidableEq Ω']
    {m : ℕ} {e : Ω ≃ Ω'} {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Ω')}
    {ϕ : G →* Perm (Fin m)} {ψ : H →* Perm (Fin m)} (h : TopdCompat e ϕ ψ)
    (S : List (alternatingGroup (Fin m))) (E : OrbitEnum (kerSubgroup ϕ))
    (F : OrbitEnum (kerSubgroup ψ)) (hE : F.windows = E.windows.map (fun W => e '' W))
    (x y : Ω → ℕ)
include h hE

 theorem topdGiant_calls :
    (cosetGiantAWith (altHom ψ) S (F.alt ψ) (x ∘ e.symm) (x ∘ e.symm)).calls =
      (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).calls.map (topdInstance e) := by
  rw [← topcsLiftFold_giant_calls (altHom ψ) S (F.alt ψ),
    ← topcsLiftFold_giant_calls (altHom ϕ) S (E.alt ϕ), topcsLiftFold_calls, topcsLiftFold_calls]
  simp only [List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f => (1 :: S).flatMap f)
  funext σ
  have hp : preimageSet (altHom ψ) σ = e.permCongr '' preimageSet (altHom ϕ) σ := by
    rw [topcsPreimage_altHom, topcsPreimage_altHom, h.preimage]
  change (Babai.cosetChain _ _ F.windows _).calls = _
  rw [hE, hp]
  exact (topd_chain e x x E.windows _).1

 theorem topdTop3_calls (O : TopActionOdd ϕ) (O' : TopActionOdd ψ)
    (hO : O'.representative = e.permCongr O.representative)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    (cosetTopAction3With ψ S O' F (x ∘ e.symm) (y ∘ e.symm)).calls =
      (cosetTopAction3With ϕ S O E x y).calls.map (topdInstance e) := by
  have hk : (Babai.cosetChain (x ∘ e.symm) (y ∘ e.symm) F.windows (kerSubgroup ψ : Set (Perm Ω'))).calls =
      (Babai.cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).calls.map (topdInstance e) := by
    rw [hE, ← h.kernel]
    exact (topd_chain e x y E.windows _).1
  have ho : (Babai.cosetChain (x ∘ e.symm) (y ∘ e.symm) F.windows
      (O'.representative • (kerSubgroup ψ : Set (Perm Ω')))).calls =
      (Babai.cosetChain x y E.windows (O.representative • (kerSubgroup ϕ : Set (Perm Ω)))).calls.map (topdInstance e) := by
    rw [hE, hO, ← h.kernel, ← topd_smul]
    exact (topd_chain e x y E.windows _).1
  rw [topdTop3_calls_eq _ S _ _ _ _ hS, topdTop3_calls_eq _ S _ _ _ _ hS,
    topdGiant_calls h S E F hE x, List.map_append]
  rw [h.mapsOntoGiant, ← h.range]
  split_ifs <;> simp only [List.map_append, List.map_nil, hk, ho]

 theorem topdTop3_run (O : TopActionOdd ϕ) (O' : TopActionOdd ψ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    (cosetTopAction3With ψ S O' F (x ∘ e.symm) (y ∘ e.symm)).run =
      ((cosetTopAction3With ϕ S O E x y).run).map (fun C => e.permCongr '' C) := by
  rw [run_cosetTopAction3With _ S _ hS, run_cosetTopAction3With _ S _ hS, h.mapsOntoGiant]
  split_ifs
  · rw [Option.map_some, ← h.group_image, topd_strIso]
  · rfl

end Congruence
end Algo
