import Workspace.Algo.TopSuppliedFold

/-! # Prepare the supplied top-action data

An alternating target has the same preimage under the original action as
under its restriction to the alternating preimage. We therefore compute
the lifting cosets with the original action. This avoids a second choice
of generators for that restriction and keeps all requested cosets exact.
-/

namespace Algo

open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev TopcsRawInput := RawTop3 × RawGens × RawPerm

/-- The alternating pair and odd representative are supplied as raw data. -/
def topcsPrepare (p : TopcsRawInput) : TopcsInput :=
  (fixStr (p.1.1.1.1, p.1.2.1), fixStr (p.1.1.1.1, p.1.2.2), topKernelWindows p.1.1,
    (rawOne p.1.1.2.1 :: p.2.1).map (fun r => topCosetStart (p.1.1, r)),
    some (topKernel p.1.1, rawOne p.1.1.1.1),
    some (topKernel p.1.1, normPerm (p.1.1.1.1, p.2.2)),
    topAllEven p.1.1, tidyGens (p.1.1.1.1, p.1.1.1.2))

theorem topcsPreimage_altHom {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)} {m : ℕ}
    (ϕ : G →* Perm (Fin m)) (σ : alternatingGroup (Fin m)) :
    preimageSet (altHom ϕ) σ = preimageSet ϕ (σ : Perm (Fin m)) := by
  ext τ
  constructor
  · rintro ⟨hτ, he⟩
    refine ⟨preimageAlt_le ϕ hτ, ?_⟩
    exact congrArg (fun a : alternatingGroup (Fin m) => (a : Perm (Fin m))) he
  · rintro ⟨hτ, he⟩
    have ha : τ ∈ preimageAlt ϕ := mem_preimageAlt'.2 ⟨hτ, by rw [he]; exact σ.2⟩
    exact ⟨ha, Subtype.ext he⟩

/-- Exact specifications of the stored data, rather than a matching
assumption. They are proved for the raw preparation below. -/
structure TopcsSpec {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (P : TopcsInput) (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Fin n → ℕ) : Prop where
  source_length : (topcsX P).length = n
  source : decStrN n (topcsX P) = x
  target : decStrN n (topcsY P) = y
  windows : (topcsWins P).map (winSet n) = E.windows
  tests : (topcsTests P).map (decCoset n) = (1 :: S).map (preimageSet (altHom ϕ))
  kernel : decCoset n (topcsKernel P) = (kerSubgroup ϕ : Set (Perm (Fin n)))
  odd : decCoset n (topcsOdd P) = O.representative • (kerSubgroup ϕ : Set (Perm (Fin n)))
  even : topcsEven P = true ↔ ϕ.range ≤ alternatingGroup (Fin m)
  ambient : decGroup n (topcsAmbient P) = G

theorem topcsPrepare_spec {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (x y : Fin n → ℕ) :
    TopcsSpec (topcsPrepare
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encStrN x, encStrN y),
        S.map (fun σ : alternatingGroup (Fin m) => encPerm m σ), encPerm n O.representative))
      ϕ S O (topCosetOrbitEnum hd hg hI) x y := by
  have hdom : rawOne dom = encPerm n 1 := by rw [rawOne_eq, hd]
  have hgdom : rawOne gdom = encPerm m 1 := by rw [rawOne_eq, hg]
  constructor
  · simp [topcsPrepare, topcsX, hd]
  · simp only [topcsPrepare, topcsX, decStrN_fixStr hd, decStrN_encStrN]
  · simp only [topcsPrepare, topcsY, decStrN_fixStr hd, decStrN_encStrN]
  · rfl
  · simp only [topcsPrepare, topcsTests, hgdom, List.map_cons, List.map_map]
    congr 1
    · rw [decCoset_topCosetStart hd hg hI, topcsPreimage_altHom]
      rfl
    · apply List.map_congr_left
      intro σ _
      exact (decCoset_topCosetStart hd hg hI σ).trans (topcsPreimage_altHom ϕ σ).symm
  · simp only [topcsPrepare, topcsKernel, decCoset_some, decGroup_topKernel hd hg hI,
      hdom, decPerm_encPerm, one_smul]
  · simp only [topcsPrepare, topcsOdd, decCoset_some, decGroup_topKernel hd hg hI,
      decPerm_normPerm hd, decPerm_encPerm]
  · exact topAllEven_spec dom gdom hI
  · simp only [topcsPrepare, topcsAmbient, decGroup_tidyGens hd, decGroup_map_encPerm]

namespace TopcsSpec

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {P : TopcsInput}
    {ϕ : G →* Perm (Fin m)} {S : List (alternatingGroup (Fin m))} {O : TopActionOdd ϕ}
    {E : OrbitEnum (kerSubgroup ϕ)} {x y : Fin n → ℕ}
    (h : TopcsSpec P ϕ S O E x y)

include h

theorem count : topcsCount P = S.length + 1 := by
  have hh := congrArg List.length h.tests
  simpa only [List.length_map, List.length_cons, topcsCount] using hh

theorem count_pos : 0 < topcsCount P := by rw [h.count]; omega

theorem wins_length : (topcsWins P).length = orbCount ϕ := by
  have hh := congrArg List.length h.windows
  rw [List.length_map, E.spec.length_eq, length_orbitList] at hh
  exact hh

theorem wins_pos (hn : 0 < n) : 0 < (topcsWins P).length := by
  have hu : (⟨0, hn⟩ : Fin n) ∈ ⋃ w ∈ (topcsWins P).map (winSet n), w := by
    rw [h.windows, E.cover]
    trivial
  obtain ⟨w, hw, _⟩ := Set.mem_iUnion₂.1 hu
  have hh := List.length_pos_of_mem hw
  simpa only [List.length_map] using hh

theorem tests_nonempty (hϕ : IsGiantRep ϕ) :
    ∀ c ∈ topcsTests P, (decCoset n c).Nonempty := by
  intro c hc
  have hm := List.mem_map_of_mem (f := decCoset n) hc
  rw [h.tests] at hm
  obtain ⟨σ, _, he⟩ := List.mem_map.1 hm
  rw [← he, topcsPreimage_altHom]
  obtain ⟨g, hg⟩ := hϕ σ.2
  exact ⟨g, g.2, hg⟩

theorem begin_kernel : decCoset n (topcsBegin P (topcsCount P)) =
    (kerSubgroup ϕ : Set (Perm (Fin n))) := by
  rw [topcsBegin, decCoset_top2NormC h.source_length, if_neg (by omega), if_pos rfl, h.kernel]

theorem begin_odd : decCoset n (topcsBegin P (topcsCount P + 1)) =
    O.representative • (kerSubgroup ϕ : Set (Perm (Fin n))) := by
  rw [topcsBegin, decCoset_top2NormC h.source_length, if_neg (by omega), if_neg (by omega), h.odd]

end TopcsSpec

end Algo
