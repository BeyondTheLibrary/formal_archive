import Workspace.TopAction.CosetRounds
import Workspace.TopAction.ColorLabel
import Workspace.Master.CosetWindow

/-! # Corollary 12.0.10 in coset form

The first window is processed by the coset top-action round. Its answer is the
candidate set for the chain over the remaining color windows.
-/

universe u v w
namespace Babai
open Equiv MulAction
open scoped Pointwise Classical
variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

noncomputable def cosetWindowTopAction3 {m : ℕ} (K : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (SIReduction.window K Δ hinv x
      (cosetTopAction3 ϕ E (restrictStr Δ x) (restrictStr Δ y))).bind
    fun r => .done (r.map (windowPreim K Δ hinv))


theorem cosetCorollary_12_0_8_window {m : ℕ} (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (hinv : IsInvariant K Δ) (hKbar : IsTransitive (restrictTo K Δ hinv))
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hm : LargeK m (Nat.card Δ)) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Δ.ncard ∧
      (cosetWindowTopAction3 K Δ hinv ϕ E x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (cosetWindowTopAction3 K Δ hinv ϕ E x y).calls,
        orbCount ϕ * I.windowSize ≤ Δ.ncard) ∧
      (cosetWindowTopAction3 K Δ hinv ϕ E x y).run =
        if MapsOntoGiant ϕ (restrictStr Δ x) then
          some (wIso Δ (K : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  set x' := restrictStr Δ x with hx'
  set y' := restrictStr Δ y with hy'
  set R := cosetTopAction3 ϕ E x' y' with hR
  have hcard : Fintype.card (Δ : Set Ω) = Δ.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨hmk, hkn, hlen, hwin, hrun⟩ := cosetCorollary_12_0_8 hKbar ϕ hϕ hm E x' y'
  have hP : ∀ J ∈ R.calls, J.K ⊆ ((restrictTo K Δ hinv : Subgroup (Equiv.Perm Δ)) :
      Set (Equiv.Perm Δ)) := calls_cosetTopAction3_K ϕ E x' y'
  have hcalls : (cosetWindowTopAction3 K Δ hinv ϕ E x y).calls =
      R.calls.map (windowInstance K Δ hinv x) := by
    rw [cosetWindowTopAction3, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil, ← hR]
    exact SIReduction.calls_window hinv x R hP
  refine ⟨hmk, by rw [← hcard]; exact hkn, ?_, ?_, ?_⟩
  · rw [hcalls, List.length_map]; exact hlen
  · intro I hI
    rw [hcalls, List.mem_map] at hI
    obtain ⟨J, hJ, rfl⟩ := hI
    rw [windowSize_windowInstance hinv x J, ← hcard]
    exact hwin J hJ
  · rw [cosetWindowTopAction3, SIReduction.run_bind, SIReduction.run_done, ← hR,
      SIReduction.run_window hinv x R hP, hrun]
    by_cases hg : MapsOntoGiant ϕ x'
    · rw [if_pos hg, if_pos hg, Option.map_some, wIso_eq_windowPreim hinv x y]
    · rw [if_neg hg, if_neg hg, Option.map_none]


variable {m : ℕ} {G : Subgroup (Perm Ω)} {κ : Type w}

/-- The two lists used after the color class has been found. -/
structure TopAction4Enum (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (C : Set (Fin m)) (hC : m < 2 * C.ncard) where
  orbits : OrbitEnum (kerSubgroup (phiCFin hG ϕ hϕ hk C hC))
  windows : List (Set Ω)
  windows_spec : windows.Perm ((List.range (tOf hG ϕ)).map (omegaCut ϕ C))

noncomputable def TopAction4Enum.default (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (C : Set (Fin m)) (hC : m < 2 * C.ncard) : TopAction4Enum hG ϕ hϕ hk C hC :=
  ⟨.default _, (List.range (tOf hG ϕ)).map (omegaCut ϕ C), List.Perm.refl _⟩

noncomputable def cosetTopAction4Body (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Enum hG ϕ hϕ hk C hC) (x y : Ω → A) :
    SIReduction Ω A (Set (Perm Ω)) :=
  (cosetWindowTopAction3 (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) E.orbits x y).bind
      fun r => match r with
      | none => .done ∅
      | some S => cosetChain x y E.windows S

noncomputable def cosetTopAction4 (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Enum hG ϕ hϕ hk (colorClass col x c) hC) :
    SIReduction Ω A (Set (Perm Ω)) :=
  if (colorClass col x c).ncard = (colorClass col y c).ncard then
    (cosetTopAction4Body hG ϕ hϕ hk (colorClass col x c) hC E x
      (strAct y ((alignColorElt ϕ col x y c : G) : Perm Ω)⁻¹)).bind
        fun ans => .done (((alignColorElt ϕ col x y c : G) : Perm Ω) • ans)
  else .done ∅

theorem cosetTopAction4Body_spec (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Enum hG ϕ hϕ hk C hC) (x y : Ω → A)
    (hlarge : LargeK C.ncard (Nat.card (omegaOf ϕ C)))
    (hmaps : MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC) (restrictStr (omegaOf ϕ C) x)) :
    (cosetTopAction4Body hG ϕ hϕ hk C hC E x y).run = strIso (stabOn ϕ C : Set (Perm Ω)) x y ∧
      ∃ rest : List (SIInstance Ω A),
        (cosetTopAction4Body hG ϕ hϕ hk C hC E x y).calls =
          (cosetWindowTopAction3 (stabOn ϕ C) (omegaOf ϕ C)
            (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) E.orbits x y).calls
            ++ rest ∧
          (∀ I ∈ rest, ∃ j < tOf hG ϕ, I.Δ = omegaCut ϕ C j) ∧
          rest.length ≤ tOf hG ϕ ∧
          (rest.map SIInstance.windowSize).sum ≤
            ∑ j ∈ Finset.range (tOf hG ϕ), (omegaCut (Ω := Ω) ϕ C j).ncard := by
  obtain ⟨-, -, -, -, hr⟩ := cosetCorollary_12_0_8_window (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFin hG ϕ hϕ hk C hC)
    (isGiantRep_phiCFin hG ϕ hϕ hk C hC) hlarge E.orbits x y
  rw [if_pos hmaps] at hr
  have hcover : omegaOf ϕ C ∪ ⋃ Δ ∈ E.windows, Δ = (Set.univ : Set Ω) := by
    have he : (⋃ Δ ∈ E.windows, Δ) = ⋃ j ∈ List.range (tOf hG ϕ), omegaCut (Ω := Ω) ϕ C j := by
      ext u
      simp only [Set.mem_iUnion, E.windows_spec.mem_iff, List.mem_map, exists_prop]
      constructor
      · rintro ⟨Δ, ⟨j, hj, rfl⟩, hu⟩; exact ⟨j, hj, hu⟩
      · rintro ⟨j, hj, hu⟩; exact ⟨_, ⟨j, hj, rfl⟩, hu⟩
    rw [he]
    exact omegaCut_cover ϕ C (fun u => tPoint_eq_tOf hG ϕ hϕ hk u)
  rw [cosetTopAction4Body, SIReduction.run_bind, SIReduction.calls_bind, hr]
  dsimp only
  refine ⟨?_, _, rfl, ?_, ?_, ?_⟩
  · rw [run_cosetChain, ← wIso_univ, ← hcover, wIso_window_union]
    ext τ
    simp only [mem_wIso, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hK, h1⟩, h2⟩; exact ⟨⟨hK, h1⟩, hK, h2⟩
    · rintro ⟨⟨hK, h1⟩, -, h2⟩; exact ⟨⟨hK, h1⟩, h2⟩
  · intro I hI
    have hi := E.windows_spec.mem_iff.1 ((calls_cosetChain _ _ _ _).2 I hI)
    obtain ⟨j, hj, he⟩ := List.mem_map.1 hi
    exact ⟨j, List.mem_range.1 hj, he.symm⟩
  · have hl := (calls_cosetChain x y E.windows (wIso (omegaOf ϕ C) (stabOn ϕ C : Set (Perm Ω)) x y)).1
    simpa only [E.windows_spec.length_eq, List.length_map, List.length_range] using hl
  · refine (sum_windowSize_calls_cosetChain _ _ _ _).trans_eq ?_
    rw [(E.windows_spec.map Set.ncard).sum_eq, List.map_map]
    exact sum_list_range (fun j => (omegaCut (Ω := Ω) ϕ C j).ncard) _

theorem cosetCorollary_12_0_10 (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Enum hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) :
    ∃ (k : ℕ) (main rest : List (SIInstance Ω A)),
      (colorClass col x c).ncard ≤ k ∧ k ≤ Fintype.card Ω ∧
        (cosetTopAction4 hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E).calls =
          main ++ rest ∧
        main.length ≤ 6 * k ∧
        (∀ I ∈ main, k * I.windowSize ≤ Fintype.card Ω) ∧
        (rest.map SIInstance.windowSize).sum ≤ Fintype.card Ω ∧
        (∀ I ∈ rest, 3 * I.windowSize ≤ 2 * Fintype.card Ω) ∧
        rest.length ≤ tOf hG ϕ ∧ tOf hG ϕ ≤ Fintype.card Ω ∧
        (cosetTopAction4 hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E).run =
          strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  haveI : Nonempty Ω := hG.nonempty
  let hk : VeryLargeK m (maxOrbitLength G) := veryLargeK_of_hugeM hG hm
  set C : Set (Fin m) := colorClass col x c with hCdef
  set G₁ : Subgroup (Equiv.Perm Ω) := stabOn ϕ C with hG₁
  set ΩC : Set Ω := omegaOf ϕ C with hΩCdef
  set t : ℕ := tOf hG ϕ with htdef
  have ht : ∀ u : Ω, tPoint ϕ u = t := fun u => tPoint_eq_tOf hG ϕ hϕ hk u
  -- the numeric hypotheses
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hΩCle : ΩC.ncard ≤ Fintype.card Ω := by
    have h1 : ΩC.ncard ≤ (Set.univ : Set Ω).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  have hΩCcard : Nat.card (ΩC : Set Ω) = ΩC.ncard := Nat.card_coe_set_eq ΩC
  have hlarge : LargeK C.ncard (Nat.card (ΩC : Set Ω)) := by
    refine (hm.largeK_of_two_mul_lt hC).mono ?_
    rw [hΩCcard, Nat.card_eq_fintype_card]
    exact hΩCle
  have hmaps : MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC) (restrictStr ΩC x) :=
    mapsOntoGiant_phiCFin hG ϕ hϕ hk C hC x hgiantC
  -- the window part of Cor. 12.0.8, with `k` the number of orbits of the kernel
  obtain ⟨hmk, hkn, hlen, hwin, -⟩ :=
    cosetCorollary_12_0_8_window G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFin hG ϕ hϕ hk C hC)
      (isGiantRep_phiCFin hG ϕ hϕ hk C hC) hlarge E.orbits x
      (strAct y ((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω)⁻¹)
  set k : ℕ := orbCount (phiCFin hG ϕ hϕ hk C hC) with hkk
  set W := cosetWindowTopAction3 G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (phiCFin hG ϕ hϕ hk C hC) E.orbits x
    (strAct y ((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω)⁻¹) with hWdef
  have hkle : k ≤ Fintype.card Ω := le_trans hkn hΩCle
  -- the number of remaining color classes is `t`, and `4t < m < 2|C| ≤ 2k ≤ 2n`
  have h4t : 4 * t < m := by
    have := (theorem_10_5_1_a ϕ hϕ hk hG.nonempty.some).1.1
    rw [show (Tpoint ϕ hG.nonempty.some).ncard = t from ht _] at this
    exact this
  have htn : t ≤ Fintype.card Ω := by omega
  by_cases hcard : C.ncard = (colorClass col y c).ncard
  · -- the aligned case
    obtain ⟨σ, hσ⟩ := exists_alignColorElt ϕ hϕ (by omega) col x y c hcard
    have hσspec : (ϕ (alignColorElt ϕ col x y c)) '' C = colorClass col y c :=
      alignColorElt_spec ⟨σ, hσ⟩
    set τ : G := alignColorElt ϕ col x y c with hτdef
    set y' : Ω → A := strAct y ((τ : G) : Equiv.Perm Ω)⁻¹ with hy'def
    obtain ⟨hcoly', hshift⟩ := Align_shift hcol x y c τ hσspec
    -- `Iso_G(x,y') = Iso_{G₁}(x,y')`
    have hG₁iso : strIso (G : Set (Equiv.Perm Ω)) x y' =
        strIso ((G₁ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y' := by
      refine Set.Subset.antisymm (fun ρ hρ => ⟨?_, hρ.2⟩) (fun ρ hρ => ⟨stabOn_le ϕ C hρ.1, hρ.2⟩)
      refine mem_stabOn.2 ⟨hρ.1, ?_⟩
      have h1 := image_colorClass_of_isIso hcol hρ.1 hρ.2 c
      rw [hcoly'] at h1
      exact h1
    obtain ⟨hbodyrun, rest, hbodycalls, hrestΔ, hrestlen, hrestsum⟩ :=
      cosetTopAction4Body_spec hG ϕ hϕ hk C hC E x y' hlarge hmaps
    refine ⟨k, W.calls, rest, hmk, hkle, ?_, hlen, ?_, ?_, ?_, hrestlen, htn, ?_⟩
    · rw [cosetTopAction4, if_pos hcard, SIReduction.calls_bind,
        SIReduction.calls_done, List.append_nil]
      exact hbodycalls
    · intro I hI
      exact le_trans (hwin I hI) hΩCle
    · refine le_trans hrestsum ?_
      exact sum_ncard_omegaCut_le ϕ C ht t (by omega)
    · intro I hI
      obtain ⟨j, hjt, hIj⟩ := hrestΔ I hI
      have hws : I.windowSize = (omegaCut (Ω := Ω) ϕ C j).ncard := by
        rw [SIInstance.windowSize, hIj]
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · have hcompl : 2 * (Cᶜ : Set (Fin m)).ncard ≤ m := by
          have hsum := Set.ncard_add_ncard_compl C
          rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
          omega
        have h0 := two_mul_ncard_omegaCut_zero_le hG ϕ hϕ hk (by omega) ht
          (by omega) (by omega) C hcompl
        rw [hws]; omega
      · have h3 := three_mul_ncard_omegaCut_le hG ϕ hϕ hk (by omega) ht (by omega) C
          hj1 hjt
        rw [hws]; exact h3
    · rw [cosetTopAction4, if_pos hcard, SIReduction.run_bind,
        SIReduction.run_done, hbodyrun, ← hG₁iso, ← hshift]
  · -- the rejecting case
    refine ⟨k, [], [], hmk, hkle, ?_, by simp, by simp, by simp, by simp, by simp, htn, ?_⟩
    · rw [cosetTopAction4, if_neg hcard, SIReduction.calls_done, List.append_nil]
    · rw [cosetTopAction4, if_neg hcard, SIReduction.run_done]
      symm
      exact Align_reject hcol c hcard


theorem isCosetInstance_calls_cosetWindowTopAction3 {m : ℕ} (K : Subgroup (Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ) (ϕ : restrictTo K Δ hinv →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ I ∈ (cosetWindowTopAction3 K Δ hinv ϕ E x y).calls, IsCosetInstance K I := by
  rw [cosetWindowTopAction3, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, SIReduction.calls_window hinv x _ (calls_cosetTopAction3_K ϕ E _ _)]
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
  exact isCosetInstance_windowInstance hinv x (isCosetInstance_calls_cosetTopAction3 ϕ E _ _ J hJ)

theorem isCosetInstance_calls_cosetTopAction4Body (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Enum hG ϕ hϕ hk C hC) (x y : Ω → A)
    (hlarge : LargeK C.ncard (Nat.card (omegaOf ϕ C))) :
    ∀ I ∈ (cosetTopAction4Body hG ϕ hϕ hk C hC E x y).calls, IsCosetInstance G I := by
  obtain ⟨-, -, -, -, hr⟩ := cosetCorollary_12_0_8_window (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFin hG ϕ hϕ hk C hC)
    (isGiantRep_phiCFin hG ϕ hϕ hk C hC) hlarge E.orbits x y
  rw [cosetTopAction4Body, SIReduction.calls_bind]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI
  · obtain ⟨N, σ, hN, hσ, he, hi⟩ :=
      isCosetInstance_calls_cosetWindowTopAction3 _ _ _ _ E.orbits x y I hI
    exact ⟨N, σ, hN.trans (stabOn_le ϕ C), stabOn_le ϕ C hσ, he, hi⟩
  · rw [hr] at hI
    by_cases hg : MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC) (restrictStr (omegaOf ϕ C) x)
    · rw [if_pos hg] at hI
      dsimp only at hI
      have hinv : ∀ Δ ∈ E.windows, IsInvariant (stabOn ϕ C) Δ := by
        intro Δ hΔ
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 (E.windows_spec.mem_iff.1 hΔ)
        exact isInvariant_omegaCut ϕ hϕ hk C j _ (stabOn_le ϕ C)
          (fun τ hτ => (mem_stabOn.1 hτ).choose_spec)
      have hs := wIso_smul_eq_empty_or_smul_coe (G := G) (N := stabOn ϕ C)
        (M := stabOn ϕ C) (stabOn_le ϕ C) le_rfl
        (isInvariant_omegaOf_stabOn ϕ hϕ hk C) x y G.one_mem
      simp only [one_smul] at hs
      rcases hs with hs | hs
      · simp only [hs, cosetChain_empty_calls, List.not_mem_nil] at hI
      · exact isCosetInstance_calls_cosetChain (stabOn_le ϕ C) x y _ _ hinv hs I hI
    · simp [if_neg hg] at hI

theorem isCosetInstance_calls_cosetTopAction4 (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Enum hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) :
    ∀ I ∈ (cosetTopAction4 hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E).calls,
      IsCosetInstance G I := by
  rw [cosetTopAction4]
  split
  · rw [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    apply isCosetInstance_calls_cosetTopAction4Body
    refine (hm.largeK_of_two_mul_lt hC).mono ?_
    rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  · simp only [SIReduction.calls_done, List.not_mem_nil, false_implies, implies_true]

theorem decreases_cosetTopAction4 (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Enum hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) :
    ∀ I ∈ (cosetTopAction4 hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E).calls,
      3 * I.windowSize ≤ 2 * Fintype.card Ω := by
  obtain ⟨k, main, rest, hCk, hkn, hsplit, -, hmain, -, hrest, -, -, -⟩ :=
    cosetCorollary_12_0_10 hG ϕ hϕ hm x y col hcol c hC hgiantC E
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hk3 : 3 ≤ k := by omega
  intro I hI
  rw [hsplit] at hI
  rcases List.mem_append.1 hI with h | h
  · have := hmain I h
    nlinarith [this, hk3, Nat.zero_le I.windowSize]
  · exact hrest I h


theorem calls_length_cosetTopAction4 (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Enum hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) :
    ((cosetTopAction4 hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E).calls).length ≤
      7 * Fintype.card Ω := by
  obtain ⟨k, main, rest, -, hkn, hsplit, hmainlen, -, -, -, hrestlen, htn, -⟩ :=
    cosetCorollary_12_0_10 hG ϕ hϕ hm x y col hcol c hC hgiantC E
  rw [hsplit, List.length_append]
  omega


/-! ### Supplied top-action choices

The alignment specification is needed only when the color class sizes agree.
The ordered generators, labeling, and odd representative are used literally in
the calls. The record specifications do not assert equality to a fixed choice.
-/

/-- Cor. 12.0.8, §12, on a window with the supplied ordered generators. -/
noncomputable def cosetWindowTopAction3With {m : ℕ} (K : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (SIReduction.window K Δ hinv x
      (cosetTopAction3With ϕ S O E (restrictStr Δ x) (restrictStr Δ y))).bind
    fun r => .done (r.map (windowPreim K Δ hinv))


/-- Cor. 12.0.8, §12: correctness and call bounds for any supplied generating pair. -/
theorem cosetCorollary_12_0_8_window_with {m : ℕ} (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (hinv : IsInvariant K Δ) (hKbar : IsTransitive (restrictTo K Δ hinv))
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hm : LargeK m (Nat.card Δ)) (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (hS : S.length = 2 ∧ Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Δ.ncard ∧
      (cosetWindowTopAction3With K Δ hinv ϕ S O E x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (cosetWindowTopAction3With K Δ hinv ϕ S O E x y).calls,
        orbCount ϕ * I.windowSize ≤ Δ.ncard) ∧
      (cosetWindowTopAction3With K Δ hinv ϕ S O E x y).run =
        if MapsOntoGiant ϕ (restrictStr Δ x) then
          some (wIso Δ (K : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  set x' := restrictStr Δ x with hx'
  set y' := restrictStr Δ y with hy'
  set R := cosetTopAction3With ϕ S O E x' y' with hR
  have hcard : Fintype.card (Δ : Set Ω) = Δ.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨hmk, hkn, hlen, hwin, hrun⟩ := cosetCorollary_12_0_8_with hKbar ϕ S O hS hϕ hm E x' y'
  have hP : ∀ J ∈ R.calls, J.K ⊆ ((restrictTo K Δ hinv : Subgroup (Equiv.Perm Δ)) :
      Set (Equiv.Perm Δ)) := calls_cosetTopAction3With_K ϕ S O E x' y'
  have hcalls : (cosetWindowTopAction3With K Δ hinv ϕ S O E x y).calls =
      R.calls.map (windowInstance K Δ hinv x) := by
    rw [cosetWindowTopAction3With, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil, ← hR]
    exact SIReduction.calls_window hinv x R hP
  refine ⟨hmk, by rw [← hcard]; exact hkn, ?_, ?_, ?_⟩
  · rw [hcalls, List.length_map]; exact hlen
  · intro I hI
    rw [hcalls, List.mem_map] at hI
    obtain ⟨J, hJ, rfl⟩ := hI
    rw [windowSize_windowInstance hinv x J, ← hcard]
    exact hwin J hJ
  · rw [cosetWindowTopAction3With, SIReduction.run_bind, SIReduction.run_done, ← hR,
      SIReduction.run_window hinv x R hP, hrun]
    by_cases hg : MapsOntoGiant ϕ x'
    · rw [if_pos hg, if_pos hg, Option.map_some, wIso_eq_windowPreim hinv x y]
    · rw [if_neg hg, if_neg hg, Option.map_none]

theorem isCosetInstance_calls_cosetWindowTopAction3With {m : ℕ} (K : Subgroup (Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ) (ϕ : restrictTo K Δ hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ I ∈ (cosetWindowTopAction3With K Δ hinv ϕ S O E x y).calls, IsCosetInstance K I := by
  rw [cosetWindowTopAction3With, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, SIReduction.calls_window hinv x _ (calls_cosetTopAction3With_K ϕ S O E _ _)]
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
  exact isCosetInstance_windowInstance hinv x (isCosetInstance_calls_cosetTopAction3With ϕ S O E _ _ J hJ)

/-- Cor. 12.0.10, §12: the labels, ordered generators, odd representative, and
both window orders used after the dominant color class is found. -/
structure TopAction4Data (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (C : Set (Fin m)) (hC : m < 2 * C.ncard) where
  label : C ≃ Fin C.ncard
  generators : List (alternatingGroup (Fin C.ncard))
  generators_length : generators.length = 2
  generators_generate : Subgroup.closure {σ : alternatingGroup (Fin C.ncard) |
    σ ∈ generators} = ⊤
  odd : TopActionOdd (phiCFinWith hG ϕ hϕ hk C hC label)
  orbits : OrbitEnum (kerSubgroup (phiCFinWith hG ϕ hϕ hk C hC label))
  windows : List (Set Ω)
  windows_spec : windows.Perm ((List.range (tOf hG ϕ)).map (omegaCut ϕ C))

/-- Use precisely the choices of the old tree, with the caller's orbit and window orders. -/
noncomputable def TopAction4Data.ofEnum (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (C : Set (Fin m)) (hC : m < 2 * C.ncard) (hm3 : 3 ≤ C.ncard)
    (E : TopAction4Enum hG ϕ hϕ hk C hC) : TopAction4Data hG ϕ hϕ hk C hC :=
  ⟨colorEquivFin C, altGens C.ncard, (altGens_spec _ hm3).1,
    (altGens_spec _ hm3).2, .default _, E.orbits, E.windows, E.windows_spec⟩

/-- Cor. 12.0.10, §12: start with `Ω(C)`, then chain through the remaining windows. -/
noncomputable def cosetTopAction4BodyWith (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Data hG ϕ hϕ hk C hC) (x y : Ω → A) :
    SIReduction Ω A (Set (Perm Ω)) :=
  (cosetWindowTopAction3With (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFinWith hG ϕ hϕ hk C hC E.label) E.generators E.odd E.orbits x y).bind
      fun r => match r with
      | none => .done ∅
      | some S => cosetChain x y E.windows S

/-- Cor. 12.0.10, §12: Align with the supplied element, then process the color windows. -/
noncomputable def cosetTopAction4With (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Data hG ϕ hϕ hk (colorClass col x c) hC) (τ : G) :
    SIReduction Ω A (Set (Perm Ω)) :=
  if (colorClass col x c).ncard = (colorClass col y c).ncard then
    (cosetTopAction4BodyWith hG ϕ hϕ hk (colorClass col x c) hC E x
      (strAct y (τ : Perm Ω)⁻¹)).bind
        fun ans => .done ((τ : Perm Ω) • ans)
  else .done ∅

theorem cosetTopAction4BodyWith_spec (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Data hG ϕ hϕ hk C hC) (x y : Ω → A)
    (hlarge : LargeK C.ncard (Nat.card (omegaOf ϕ C)))
    (hmaps : MapsOntoGiant (phiCFinWith hG ϕ hϕ hk C hC E.label) (restrictStr (omegaOf ϕ C) x)) :
    (cosetTopAction4BodyWith hG ϕ hϕ hk C hC E x y).run = strIso (stabOn ϕ C : Set (Perm Ω)) x y ∧
      ∃ rest : List (SIInstance Ω A),
        (cosetTopAction4BodyWith hG ϕ hϕ hk C hC E x y).calls =
          (cosetWindowTopAction3With (stabOn ϕ C) (omegaOf ϕ C)
            (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFinWith hG ϕ hϕ hk C hC E.label) E.generators E.odd E.orbits x y).calls
            ++ rest ∧
          (∀ I ∈ rest, ∃ j < tOf hG ϕ, I.Δ = omegaCut ϕ C j) ∧
          rest.length ≤ tOf hG ϕ ∧
          (rest.map SIInstance.windowSize).sum ≤
            ∑ j ∈ Finset.range (tOf hG ϕ), (omegaCut (Ω := Ω) ϕ C j).ncard := by
  obtain ⟨-, -, -, -, hr⟩ := cosetCorollary_12_0_8_window_with (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFinWith hG ϕ hϕ hk C hC E.label)
    (isGiantRep_phiCFinWith hG ϕ hϕ hk C hC E.label) hlarge E.generators E.odd ⟨E.generators_length, E.generators_generate⟩ E.orbits x y
  rw [if_pos hmaps] at hr
  have hcover : omegaOf ϕ C ∪ ⋃ Δ ∈ E.windows, Δ = (Set.univ : Set Ω) := by
    have he : (⋃ Δ ∈ E.windows, Δ) = ⋃ j ∈ List.range (tOf hG ϕ), omegaCut (Ω := Ω) ϕ C j := by
      ext u
      simp only [Set.mem_iUnion, E.windows_spec.mem_iff, List.mem_map, exists_prop]
      constructor
      · rintro ⟨Δ, ⟨j, hj, rfl⟩, hu⟩; exact ⟨j, hj, hu⟩
      · rintro ⟨j, hj, hu⟩; exact ⟨_, ⟨j, hj, rfl⟩, hu⟩
    rw [he]
    exact omegaCut_cover ϕ C (fun u => tPoint_eq_tOf hG ϕ hϕ hk u)
  rw [cosetTopAction4BodyWith, SIReduction.run_bind, SIReduction.calls_bind, hr]
  dsimp only
  refine ⟨?_, _, rfl, ?_, ?_, ?_⟩
  · rw [run_cosetChain, ← wIso_univ, ← hcover, wIso_window_union]
    ext τ
    simp only [mem_wIso, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hK, h1⟩, h2⟩; exact ⟨⟨hK, h1⟩, hK, h2⟩
    · rintro ⟨⟨hK, h1⟩, -, h2⟩; exact ⟨⟨hK, h1⟩, h2⟩
  · intro I hI
    have hi := E.windows_spec.mem_iff.1 ((calls_cosetChain _ _ _ _).2 I hI)
    obtain ⟨j, hj, he⟩ := List.mem_map.1 hi
    exact ⟨j, List.mem_range.1 hj, he.symm⟩
  · have hl := (calls_cosetChain x y E.windows (wIso (omegaOf ϕ C) (stabOn ϕ C : Set (Perm Ω)) x y)).1
    simpa only [E.windows_spec.length_eq, List.length_map, List.length_range] using hl
  · refine (sum_windowSize_calls_cosetChain _ _ _ _).trans_eq ?_
    rw [(E.windows_spec.map Set.ncard).sum_eq, List.map_map]
    exact sum_list_range (fun j => (omegaCut (Ω := Ω) ϕ C j).ncard) _

/-- Cor. 12.0.10, §12: all supplied choices satisfying their specifications give
the string-isomorphism set and the stated bounds on recursive calls. -/
theorem cosetCorollary_12_0_10_with (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Data hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) (τ : G)
    (hτ : (colorClass col x c).ncard = (colorClass col y c).ncard →
      (ϕ τ) '' colorClass col x c = colorClass col y c) :
    ∃ (k : ℕ) (main rest : List (SIInstance Ω A)),
      (colorClass col x c).ncard ≤ k ∧ k ≤ Fintype.card Ω ∧
        (cosetTopAction4With hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E τ).calls =
          main ++ rest ∧
        main.length ≤ 6 * k ∧
        (∀ I ∈ main, k * I.windowSize ≤ Fintype.card Ω) ∧
        (rest.map SIInstance.windowSize).sum ≤ Fintype.card Ω ∧
        (∀ I ∈ rest, 3 * I.windowSize ≤ 2 * Fintype.card Ω) ∧
        rest.length ≤ tOf hG ϕ ∧ tOf hG ϕ ≤ Fintype.card Ω ∧
        (cosetTopAction4With hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E τ).run =
          strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  haveI : Nonempty Ω := hG.nonempty
  let hk : VeryLargeK m (maxOrbitLength G) := veryLargeK_of_hugeM hG hm
  set C : Set (Fin m) := colorClass col x c with hCdef
  set G₁ : Subgroup (Equiv.Perm Ω) := stabOn ϕ C with hG₁
  set ΩC : Set Ω := omegaOf ϕ C with hΩCdef
  set t : ℕ := tOf hG ϕ with htdef
  have ht : ∀ u : Ω, tPoint ϕ u = t := fun u => tPoint_eq_tOf hG ϕ hϕ hk u
  -- the numeric hypotheses
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hΩCle : ΩC.ncard ≤ Fintype.card Ω := by
    have h1 : ΩC.ncard ≤ (Set.univ : Set Ω).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  have hΩCcard : Nat.card (ΩC : Set Ω) = ΩC.ncard := Nat.card_coe_set_eq ΩC
  have hlarge : LargeK C.ncard (Nat.card (ΩC : Set Ω)) := by
    refine (hm.largeK_of_two_mul_lt hC).mono ?_
    rw [hΩCcard, Nat.card_eq_fintype_card]
    exact hΩCle
  have hmaps : MapsOntoGiant (phiCFinWith hG ϕ hϕ hk C hC E.label) (restrictStr ΩC x) :=
    mapsOntoGiant_phiCFinWith hG ϕ hϕ hk C hC E.label x hgiantC
  -- the window part of Cor. 12.0.8, with `k` the number of orbits of the kernel
  obtain ⟨hmk, hkn, hlen, hwin, -⟩ :=
    cosetCorollary_12_0_8_window_with G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFinWith hG ϕ hϕ hk C hC E.label)
      (isGiantRep_phiCFinWith hG ϕ hϕ hk C hC E.label) hlarge E.generators E.odd ⟨E.generators_length, E.generators_generate⟩ E.orbits x
      (strAct y (τ : Equiv.Perm Ω)⁻¹)
  set k : ℕ := orbCount (phiCFinWith hG ϕ hϕ hk C hC E.label) with hkk
  set W := cosetWindowTopAction3With G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (phiCFinWith hG ϕ hϕ hk C hC E.label) E.generators E.odd E.orbits x
    (strAct y (τ : Equiv.Perm Ω)⁻¹) with hWdef
  have hkle : k ≤ Fintype.card Ω := le_trans hkn hΩCle
  -- the number of remaining color classes is `t`, and `4t < m < 2|C| ≤ 2k ≤ 2n`
  have h4t : 4 * t < m := by
    have := (theorem_10_5_1_a ϕ hϕ hk hG.nonempty.some).1.1
    rw [show (Tpoint ϕ hG.nonempty.some).ncard = t from ht _] at this
    exact this
  have htn : t ≤ Fintype.card Ω := by omega
  by_cases hcard : C.ncard = (colorClass col y c).ncard
  · -- the aligned case
    have hσspec : (ϕ τ) '' C = colorClass col y c := hτ hcard
    set y' : Ω → A := strAct y (τ : Equiv.Perm Ω)⁻¹ with hy'def
    obtain ⟨hcoly', hshift⟩ := Align_shift hcol x y c τ hσspec
    -- `Iso_G(x,y') = Iso_{G₁}(x,y')`
    have hG₁iso : strIso (G : Set (Equiv.Perm Ω)) x y' =
        strIso ((G₁ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y' := by
      refine Set.Subset.antisymm (fun ρ hρ => ⟨?_, hρ.2⟩) (fun ρ hρ => ⟨stabOn_le ϕ C hρ.1, hρ.2⟩)
      refine mem_stabOn.2 ⟨hρ.1, ?_⟩
      have h1 := image_colorClass_of_isIso hcol hρ.1 hρ.2 c
      rw [hcoly'] at h1
      exact h1
    obtain ⟨hbodyrun, rest, hbodycalls, hrestΔ, hrestlen, hrestsum⟩ :=
      cosetTopAction4BodyWith_spec hG ϕ hϕ hk C hC E x y' hlarge hmaps
    refine ⟨k, W.calls, rest, hmk, hkle, ?_, hlen, ?_, ?_, ?_, hrestlen, htn, ?_⟩
    · rw [cosetTopAction4With, if_pos hcard, SIReduction.calls_bind,
        SIReduction.calls_done, List.append_nil]
      exact hbodycalls
    · intro I hI
      exact le_trans (hwin I hI) hΩCle
    · refine le_trans hrestsum ?_
      exact sum_ncard_omegaCut_le ϕ C ht t (by omega)
    · intro I hI
      obtain ⟨j, hjt, hIj⟩ := hrestΔ I hI
      have hws : I.windowSize = (omegaCut (Ω := Ω) ϕ C j).ncard := by
        rw [SIInstance.windowSize, hIj]
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · have hcompl : 2 * (Cᶜ : Set (Fin m)).ncard ≤ m := by
          have hsum := Set.ncard_add_ncard_compl C
          rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
          omega
        have h0 := two_mul_ncard_omegaCut_zero_le hG ϕ hϕ hk (by omega) ht
          (by omega) (by omega) C hcompl
        rw [hws]; omega
      · have h3 := three_mul_ncard_omegaCut_le hG ϕ hϕ hk (by omega) ht (by omega) C
          hj1 hjt
        rw [hws]; exact h3
    · rw [cosetTopAction4With, if_pos hcard, SIReduction.run_bind,
        SIReduction.run_done, hbodyrun, ← hG₁iso, ← hshift]
  · -- the rejecting case
    refine ⟨k, [], [], hmk, hkle, ?_, by simp, by simp, by simp, by simp, by simp, htn, ?_⟩
    · rw [cosetTopAction4With, if_neg hcard, SIReduction.calls_done, List.append_nil]
    · rw [cosetTopAction4With, if_neg hcard, SIReduction.run_done]
      symm
      exact Align_reject hcol c hcard


theorem isCosetInstance_calls_cosetTopAction4BodyWith (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (E : TopAction4Data hG ϕ hϕ hk C hC) (x y : Ω → A)
    (hlarge : LargeK C.ncard (Nat.card (omegaOf ϕ C))) :
    ∀ I ∈ (cosetTopAction4BodyWith hG ϕ hϕ hk C hC E x y).calls, IsCosetInstance G I := by
  obtain ⟨-, -, -, -, hr⟩ := cosetCorollary_12_0_8_window_with (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFinWith hG ϕ hϕ hk C hC E.label)
    (isGiantRep_phiCFinWith hG ϕ hϕ hk C hC E.label) hlarge E.generators E.odd ⟨E.generators_length, E.generators_generate⟩ E.orbits x y
  rw [cosetTopAction4BodyWith, SIReduction.calls_bind]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI
  · obtain ⟨N, σ, hN, hσ, he, hi⟩ :=
      isCosetInstance_calls_cosetWindowTopAction3With _ _ _ _ E.generators E.odd E.orbits x y I hI
    exact ⟨N, σ, hN.trans (stabOn_le ϕ C), stabOn_le ϕ C hσ, he, hi⟩
  · rw [hr] at hI
    by_cases hg : MapsOntoGiant (phiCFinWith hG ϕ hϕ hk C hC E.label) (restrictStr (omegaOf ϕ C) x)
    · rw [if_pos hg] at hI
      dsimp only at hI
      have hinv : ∀ Δ ∈ E.windows, IsInvariant (stabOn ϕ C) Δ := by
        intro Δ hΔ
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 (E.windows_spec.mem_iff.1 hΔ)
        exact isInvariant_omegaCut ϕ hϕ hk C j _ (stabOn_le ϕ C)
          (fun τ hτ => (mem_stabOn.1 hτ).choose_spec)
      have hs := wIso_smul_eq_empty_or_smul_coe (G := G) (N := stabOn ϕ C)
        (M := stabOn ϕ C) (stabOn_le ϕ C) le_rfl
        (isInvariant_omegaOf_stabOn ϕ hϕ hk C) x y G.one_mem
      simp only [one_smul] at hs
      rcases hs with hs | hs
      · simp only [hs, cosetChain_empty_calls, List.not_mem_nil] at hI
      · exact isCosetInstance_calls_cosetChain (stabOn_le ϕ C) x y _ _ hinv hs I hI
    · simp [if_neg hg] at hI

theorem isCosetInstance_calls_cosetTopAction4With (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Data hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) (τ : G) :
    ∀ I ∈ (cosetTopAction4With hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E τ).calls,
      IsCosetInstance G I := by
  rw [cosetTopAction4With]
  split
  · rw [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    apply isCosetInstance_calls_cosetTopAction4BodyWith
    refine (hm.largeK_of_two_mul_lt hC).mono ?_
    rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  · simp only [SIReduction.calls_done, List.not_mem_nil, false_implies, implies_true]

theorem decreases_cosetTopAction4With (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Data hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) (τ : G)
    (hτ : (colorClass col x c).ncard = (colorClass col y c).ncard →
      (ϕ τ) '' colorClass col x c = colorClass col y c) :
    ∀ I ∈ (cosetTopAction4With hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E τ).calls,
      3 * I.windowSize ≤ 2 * Fintype.card Ω := by
  obtain ⟨k, main, rest, hCk, hkn, hsplit, -, hmain, -, hrest, -, -, -⟩ :=
    cosetCorollary_12_0_10_with hG ϕ hϕ hm x y col hcol c hC hgiantC E τ hτ
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hk3 : 3 ≤ k := by omega
  intro I hI
  rw [hsplit] at hI
  rcases List.mem_append.1 hI with h | h
  · have := hmain I h
    nlinarith [this, hk3, Nat.zero_le I.windowSize]
  · exact hrest I h


theorem calls_length_cosetTopAction4With (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ)
    (E : TopAction4Data hG ϕ hϕ (veryLargeK_of_hugeM hG hm) (colorClass col x c) hC) (τ : G)
    (hτ : (colorClass col x c).ncard = (colorClass col y c).ncard →
      (ϕ τ) '' colorClass col x c = colorClass col y c) :
    ((cosetTopAction4With hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC E τ).calls).length ≤
      7 * Fintype.card Ω := by
  obtain ⟨k, main, rest, -, hkn, hsplit, hmainlen, -, -, -, hrestlen, htn, -⟩ :=
    cosetCorollary_12_0_10_with hG ϕ hϕ hm x y col hcol c hC hgiantC E τ hτ
  rw [hsplit, List.length_append]
  omega


/-- Cor. 12.0.8, §12: the old generator list gives exactly the old window tree. -/
theorem cosetWindowTopAction3With_default {m : ℕ} (K : Subgroup (Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    cosetWindowTopAction3With K Δ hinv ϕ (altGens m) (.default ϕ) E x y =
      cosetWindowTopAction3 K Δ hinv ϕ E x y := rfl

/-- Cor. 12.0.10, §12: specializing the supplied data preserves every continuation. -/
theorem cosetTopAction4BodyWith_default (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (hm3 : 3 ≤ C.ncard)
    (E : TopAction4Enum hG ϕ hϕ hk C hC) (x y : Ω → A) :
    cosetTopAction4BodyWith hG ϕ hϕ hk C hC
      (TopAction4Data.ofEnum hG ϕ hϕ hk C hC hm3 E) x y =
      cosetTopAction4Body hG ϕ hϕ hk C hC E x y := rfl

/-- Cor. 12.0.10, §12: the old tree is the supplied form with its original choices.
This is equality of trees, including branches at arbitrary answers. -/
theorem cosetTopAction4With_default (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard) (hm3 : 3 ≤ (colorClass col x c).ncard)
    (E : TopAction4Enum hG ϕ hϕ hk (colorClass col x c) hC) :
    cosetTopAction4With hG ϕ hϕ hk col c x y hC
      (TopAction4Data.ofEnum hG ϕ hϕ hk (colorClass col x c) hC hm3 E)
      (alignColorElt ϕ col x y c) = cosetTopAction4 hG ϕ hϕ hk col c x y hC E := rfl

/-- The original aligning element satisfies the supplied-data specification. -/
theorem alignColorElt_spec_of_card (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hm : 3 ≤ m) (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A) :
    (colorClass col x c).ncard = (colorClass col y c).ncard →
      (ϕ (alignColorElt ϕ col x y c)) '' colorClass col x c = colorClass col y c :=
  fun hc => alignColorElt_spec (exists_alignColorElt ϕ hϕ hm col x y c hc)

/-- Cor. 12.0.10, §12: a supplied element for Procedure Align and its exact
class-image specification. Unequal sizes reject before this element is used. -/
structure TopActionAlignment (ϕ : G →* Perm (Fin m))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A) where
  element : G
  spec : (colorClass col x c).ncard = (colorClass col y c).ncard →
    (ϕ element) '' colorClass col x c = colorClass col y c

noncomputable def TopActionAlignment.default (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : 3 ≤ m)
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A) :
    TopActionAlignment ϕ col c x y :=
  ⟨alignColorElt ϕ col x y c, alignColorElt_spec_of_card ϕ hϕ hm col c x y⟩

noncomputable def TopAction4Data.default (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (C : Set (Fin m)) (hC : m < 2 * C.ncard) (hm3 : 3 ≤ C.ncard) :
    TopAction4Data hG ϕ hϕ hk C hC :=
  .ofEnum hG ϕ hϕ hk C hC hm3 (.default _ _ _ _ _ _)

end Babai
