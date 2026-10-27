import Workspace.Master.AlignDominantRound
import Workspace.Master.StrongAggregateAlign

/-! # Procedure Align, lines 7–11, in coset form

The incoming candidate set is kept. In the small-parameter case the supplied
cosets cover that set. In the other cases the orbit chain starts from it.
The dominant orbit comes first, so its aligned call retains `G*` and its hint.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- Sec. 14.1, lines 7–11: the orbit orders and the coset lists are inputs. -/
structure AlignDominantEnum (Ω : Type u) where
  orbits : List (Set Ω)
  kernelOrbits : List (Set Ω)
  reps : Set (Perm Ω) → List (Perm Ω)

/-- The orbit lists have no repetitions. A dominant orbit comes first. The
representatives cover the incoming coset, rather than just `G*`. -/
structure AlignDominantEnum.Spec (D : AlignDominantRoundData Ω)
    (E : AlignDominantEnum Ω) : Prop where
  orbits : E.orbits.Perm (orbitListOn D.toAlignDominant.Gs D.toAlignDominant.window)
  kernelOrbits : E.kernelOrbits.Perm (orbitListOn D.ker D.toAlignDominant.window)
  first : ∀ S ∈ E.orbits, 2 * Fintype.card Ω < 3 * S.ncard →
    ∃ rest, E.orbits = S :: rest ∧ S ∉ rest
  cover : ∀ C, (∃ σ : Perm Ω, C = σ • (D.toAlignDominant.Gs : Set (Perm Ω))) →
    C = ⋃ σ ∈ E.reps C, σ • (D.ker : Set (Perm Ω))
  length : ∀ C, (E.reps C).length ≤ D.ker.relIndex D.toAlignDominant.Gs

namespace AlignDominantRoundData

variable (D : AlignDominantRoundData Ω)

/-- The old finite enumerations give witnesses for the new list interface. The
choice of a translating element is confined to this witness. -/
noncomputable def defaultCosetEnum : AlignDominantEnum Ω where
  orbits := orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window
  kernelOrbits := orbitListOn D.ker D.toAlignDominant.window
  reps := fun C =>
    if h : ∃ σ : Perm Ω, C = σ • (D.toAlignDominant.Gs : Set (Perm Ω)) then
      (cosetRepList D.ker D.toAlignDominant.Gs).map (h.choose * ·)
    else []

theorem defaultCosetEnum_spec : D.defaultCosetEnum.Spec D := by
  constructor
  · exact orbitListDomFirst_perm _ _
  · exact List.Perm.refl _
  · intro S hS hbig
    obtain ⟨T, hT, hTbig, he⟩ := orbitListDomFirst_eq_cons
      (mem_orbitListDomFirst.1 hS) hbig
    obtain ⟨v, _, hSv⟩ := exists_orbit_of_mem_orbitListOn
      (mem_orbitListDomFirst.1 hS)
    obtain ⟨w, _, hTw⟩ := exists_orbit_of_mem_orbitListOn hT
    have hTS : T = S := by
      rw [hSv, hTw]
      exact D.dominant_orbit_unique (by rwa [← hSv]) (by rwa [← hTw])
    rw [hTS] at he
    exact ⟨_, he, not_mem_erase_orbitListOn _ _ _⟩
  · intro C hC
    change C = ⋃ σ ∈ (if h : ∃ σ : Perm Ω,
        C = σ • (D.toAlignDominant.Gs : Set (Perm Ω)) then
        (cosetRepList D.ker D.toAlignDominant.Gs).map (h.choose * ·) else []),
      σ • (D.ker : Set (Perm Ω))
    rw [dif_pos hC]
    have he := hC.choose_spec
    generalize hC.choose = τ at he ⊢
    rw [he]
    conv_lhs => rw [coe_eq_iUnion_cosetRepList D.ker_le]
    ext ρ
    constructor
    · rintro ⟨μ, hμ, hρ⟩
      obtain ⟨σ, hσ, ν, hν, hμ⟩ := Set.mem_iUnion₂.1 hμ
      refine Set.mem_iUnion₂.2 ⟨τ * σ, List.mem_map.2 ⟨σ, hσ, rfl⟩, ν, hν, ?_⟩
      change τ * σ * ν = ρ
      have hμ' : σ * ν = μ := hμ
      have hρ' : τ * μ = ρ := hρ
      rw [mul_assoc, hμ', hρ']
    · intro hρ
      obtain ⟨μ, hμ, ν, hν, hρ⟩ := Set.mem_iUnion₂.1 hρ
      obtain ⟨σ, hσ, heσ⟩ := List.mem_map.1 hμ
      rw [← heσ] at hρ
      refine ⟨σ * ν, Set.mem_iUnion₂.2 ⟨σ, hσ, ν, hν, rfl⟩, ?_⟩
      change τ * (σ * ν) = ρ
      exact (mul_assoc τ σ ν).symm.trans hρ
  · intro C
    change (if h : ∃ σ : Perm Ω, C = σ • (D.toAlignDominant.Gs : Set (Perm Ω)) then
        (cosetRepList D.ker D.toAlignDominant.Gs).map (h.choose * ·) else []).length ≤ _
    split
    · rw [List.length_map, length_cosetRepList]
    · exact Nat.zero_le _

/-- Sec. 14.1, lines 7–11: strong descent or the orbit chain, with unshifted strings. -/
noncomputable def cosetRound (E : AlignDominantEnum Ω) (I : SIInstance Ω A) :
    SIReduction Ω A (Set (Perm Ω)) :=
  if D.LargeParam then cosetChain I.x I.y E.orbits I.K
  else strongDescent D.ker I.x I.y (E.reps I.K) E.kernelOrbits

theorem run_cosetRound (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω)))
    (hΔ : I.Δ = D.toAlignDominant.window) : (D.cosetRound E I).run = I.answer := by
  have ho : (⋃ S ∈ E.orbits, S) = D.toAlignDominant.window := by
    simpa only [hE.orbits.mem_iff] using iUnion_orbitListOn D.isInvariant_window
  have hk : (⋃ S ∈ E.kernelOrbits, S) = D.toAlignDominant.window := by
    simpa only [hE.kernelOrbits.mem_iff] using iUnion_orbitListOn D.isInvariant_window_ker
  unfold cosetRound
  split
  · rw [run_cosetChain, ho, SIInstance.answer, hΔ]
  · rw [run_strongDescent, hk, ← hE.cover I.K hK, SIInstance.answer, hΔ]

/-- A nonempty incoming coset and a nonempty window force a recursive call. -/
theorem calls_cosetRound_ne_nil (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω)))
    (hw : D.toAlignDominant.window.Nonempty) : (D.cosetRound E I).calls ≠ [] := by
  obtain ⟨u, hu⟩ := hw
  obtain ⟨σ, hσ⟩ := hK
  have hne : I.K.Nonempty := ⟨σ, by rw [hσ]; exact ⟨1, Subgroup.one_mem _, by simp⟩⟩
  unfold cosetRound
  split
  · have ho : E.orbits ≠ [] := List.ne_nil_of_mem
      (hE.orbits.mem_iff.2 (orbit_mem_orbitListOn D.isInvariant_window hu))
    obtain ⟨S, rest, he⟩ := List.exists_cons_of_ne_nil ho
    rw [he]
    exact calls_cosetChain_cons_ne_nil _ _ _ _ hne
  · have hk : E.kernelOrbits ≠ [] := List.ne_nil_of_mem
      (hE.kernelOrbits.mem_iff.2 (orbit_mem_orbitListOn D.isInvariant_window_ker hu))
    have hr : E.reps I.K ≠ [] := by
      intro he
      rw [hE.cover I.K ⟨σ, hσ⟩, he] at hne
      simpa using hne
    obtain ⟨τ, hτ⟩ := List.exists_mem_of_ne_nil _ hr
    obtain ⟨S, rest, he⟩ := List.exists_cons_of_ne_nil hk
    have hc := calls_cosetChain_cons_ne_nil I.x I.y S rest
      (C := τ • (D.ker : Set (Perm Ω))) ⟨τ, 1, Subgroup.one_mem _, by simp⟩
    obtain ⟨J, hJ⟩ := List.exists_mem_of_ne_nil _ hc
    apply List.ne_nil_of_mem (a := J)
    rw [calls_strongDescent, List.mem_flatMap]
    exact ⟨τ, hτ, by rwa [he]⟩

theorem calls_length_cosetRound (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (I : SIInstance Ω A) :
    (D.cosetRound E I).calls.length ≤ alignDominantRoundCost (Fintype.card Ω) := by
  have ho : E.orbits.length ≤ Fintype.card Ω :=
    hE.orbits.length_eq.le.trans (length_orbitListOn_le _ _)
  have hk : E.kernelOrbits.length ≤ Fintype.card Ω :=
    hE.kernelOrbits.length_eq.le.trans (length_orbitListOn_le _ _)
  unfold cosetRound
  split
  · exact ((calls_cosetChain _ _ _ _).1.trans ho).trans (Nat.le_add_left _ _)
  · rename_i h
    have hc := (length_calls_strongDescent D.ker I.x I.y (E.reps I.K) E.kernelOrbits).trans
      (Nat.mul_le_mul (hE.length I.K) hk)
    have hr := (relIndex_kerSubgroup_le D.toAlignDominant.phis).trans
      (Nat.factorial_le (D.ms_le_ellOf h))
    exact (hc.trans (Nat.mul_le_mul_right _ hr)).trans (Nat.le_add_right _ _)

/-- Every candidate tested by the round belongs to its incoming set. -/
theorem calls_cosetRound_K (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω))) :
    ∀ J ∈ (D.cosetRound E I).calls, J.K ⊆ I.K := by
  unfold cosetRound
  split
  · exact calls_cosetChain_K _ _ _ _
  · intro J hJ τ hτ
    obtain ⟨_, σ, hσ, hsub⟩ := mem_calls_strongDescent _ _ _ _ _ hJ
    rw [hE.cover I.K hK]
    exact Set.mem_iUnion₂.2 ⟨σ, hσ, hsub hτ⟩

/-- The subgroup preserving the windows is `G*` or its kernel. The representative
need only belong to the ambient group of the incoming coset. -/
theorem isCosetInstance_calls_cosetRound (E : AlignDominantEnum Ω) (hE : E.Spec D)
    {G : Subgroup (Perm Ω)} (hG : D.toAlignDominant.Gs ≤ G) (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, σ ∈ G ∧ I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω))) :
    ∀ J ∈ (D.cosetRound E I).calls, IsCosetInstance G J := by
  obtain ⟨σ, hσ, hK⟩ := hK
  have hsub : I.K ⊆ (G : Set (Perm Ω)) := by
    rw [hK]
    rintro _ ⟨τ, hτ, rfl⟩
    exact G.mul_mem hσ (hG hτ)
  unfold cosetRound
  split
  · exact isCosetInstance_calls_cosetChain_over hG I.x I.y _ _
      (fun S hS => isInvariant_of_mem_orbitListOn (hE.orbits.mem_iff.1 hS))
      ⟨_, σ, le_rfl, hσ, hK⟩
  · intro J hJ
    exact isCosetInstance_calls_strongDescent (D.ker_le.trans hG) I.x I.y _ _
      (fun S hS => isInvariant_of_mem_orbitListOn (hE.kernelOrbits.mem_iff.1 hS))
      (fun τ hτ => hsub (strongRep_mem_cover _ _ (hE.cover I.K ⟨σ, hK⟩) hτ)) hJ

/-- Sec. 14.1, line 11: the only large call still has group `G*` after alignment.
This fact is also used when the call is first lifted to a larger ground set. -/
theorem cosetRound_small_or_hint (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω))) :
    ∀ J ∈ (D.cosetRound E I).calls,
      3 * J.windowSize ≤ 2 * Fintype.card Ω ∨
        D.HasHint (alignInst J) (alignInst J) := by
  intro J hJ
  by_cases h : D.LargeParam
  · rw [cosetRound, if_pos h] at hJ
    have hmem := (calls_cosetChain I.x I.y E.orbits I.K).2 J hJ
    by_cases hs : 3 * J.windowSize ≤ 2 * Fintype.card Ω
    · exact Or.inl hs
    · have hbig : 2 * Fintype.card Ω < 3 * J.Δ.ncard := by
        change ¬ 3 * J.Δ.ncard ≤ 2 * Fintype.card Ω at hs
        omega
      obtain ⟨rest, he, hn⟩ := hE.first J.Δ hmem hbig
      rw [he] at hJ
      have hhead : J = (⟨I.K, J.Δ, I.x, I.y⟩ : SIInstance Ω A) := by
        rcases calls_cosetChain_cons _ _ _ _ _ J hJ with hh | hh
        · exact hh
        · exact False.elim (hn hh)
      obtain ⟨v, hv, hJv⟩ := exists_orbit_of_mem_orbitListOn (hE.orbits.mem_iff.1 hmem)
      obtain ⟨σ, hσ⟩ := hK
      have hgroup : (alignInst J).K = (D.toAlignDominant.Gs : Set (Perm Ω)) := by
        conv_lhs => rw [hhead, hσ]
        exact K_alignInst_smul_coe _ _ _ _ _
      refine Or.inr ⟨h, D.dominantOrbit h hv (by rwa [← hJv]), ?_⟩
      change (⟨(D.toAlignDominant.Gs : Set (Perm Ω)), orbit D.toAlignDominant.Gs v,
        (alignInst J).x, (alignInst J).y⟩ : SIInstance Ω A) = alignInst J
      rw [← hgroup, ← hJv]
      rfl
  · rw [cosetRound, if_neg h] at hJ
    have hm := (mem_calls_strongDescent _ _ _ _ _ hJ).1
    obtain ⟨v, hv, he⟩ := exists_orbit_of_mem_orbitListOn (hE.kernelOrbits.mem_iff.1 hm)
    left
    change 3 * J.Δ.ncard ≤ _
    rw [he, ker, orbit_kerSubgroup]
    exact D.orbit_ker_le v hv

/-- Sec. 14.1, lines 7–11: every aligned call makes progress. -/
theorem decreases_cosetRound (E : AlignDominantEnum Ω) (hE : E.Spec D)
    (i : HintedInstance Ω A) (hwin : i.inst.windowSize = Fintype.card Ω)
    (hparam : param i = D.toAlignDominant.m) (I : SIInstance Ω A)
    (hK : ∃ σ : Perm Ω, I.K = σ • (D.toAlignDominant.Gs : Set (Perm Ω))) :
    ∀ J ∈ (D.cosetRound E I).calls,
      MakesProgress HintedInstance.win param i
        (⟨alignInst J, D.hint (alignInst J) (alignInst J)⟩ : HintedInstance Ω A) := by
  intro J hJ
  rcases D.cosetRound_small_or_hint E hE I hK J hJ with hs | hh
  · have hn := D.window_large
    left
    constructor
    · change 1 ≤ i.inst.windowSize
      omega
    · change 5 * J.windowSize ≤ 4 * i.inst.windowSize
      omega
  · right
    refine ⟨?_, ?_, ?_⟩
    · change J.Δ.ncard ≤ i.inst.windowSize
      rw [hwin]
      exact ncard_le_card _
    · rw [hparam]
      have := D.toAlignDominant.nine_le_m
      omega
    · rw [hparam]
      exact D.two_mul_param_hint_le _ _ hh

end AlignDominantRoundData

end Babai
