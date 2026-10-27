/-
Section 13.1 of Babai, version 2.5: the repaired comparison invariant.
-/
import Workspace.LocalCertificates.Compare
import Workspace.LocalCertificates.Canonicity

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ}
  {x y : Ω → Λ} {T : Set Γ}

/-- A stage only uses letters inside its window. Agreement on the window at stage `i`
therefore gives the same windows and groups through stage `i`. -/
theorem stages_locality (i : ℕ)
    (h : ∀ u ∈ (stages ϕ x T i).W, x u = y u) :
    (stages ϕ x T i).W = (stages ϕ y T i).W ∧
      (stages ϕ x T i).H = (stages ϕ y T i).H := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    obtain ⟨hW, hH⟩ := ih (fun u hu => h u ((stages ϕ x T i).sub_aff hu))
    have ha : (stages ϕ x T i).aff = (stages ϕ y T i).aff := by
      ext u
      exact affectedIn_congr hH _ _ u
    refine ⟨ha, SetLike.ext fun σ => ?_⟩
    change (σ ∈ (stages ϕ x T i).H ∧
      ∀ u ∈ (stages ϕ x T i).aff, x u = x (σ u)) ↔
      (σ ∈ (stages ϕ y T i).H ∧
      ∀ u ∈ (stages ϕ y T i).aff, y u = y (σ u))
    rw [← hH, ← ha]
    constructor <;> rintro ⟨hσ, hr⟩ <;> refine ⟨hσ, fun u hu => ?_⟩
    · rw [← h u hu, ← h (σ u) ((stages ϕ x T i).isInvariant_aff.mem_of_mem hσ hu)]
      exact hr u hu
    · rw [h u hu, h (σ u) ((stages ϕ x T i).isInvariant_aff.mem_of_mem hσ hu)]
      exact hr u hu

/-- The loop condition is determined by the window and group. -/
theorem loopCond_congr {s : Stage ϕ x T} {s' : Stage ϕ y T}
    (hW : s.W = s'.W) (hH : s.H = s'.H) : s.LoopCond ↔ s'.LoopCond := by
  have ha : s.aff = s'.aff := Set.ext fun u => affectedIn_congr hH _ _ u
  have hi := imgOn_congr hH s.le s'.le
  unfold Stage.LoopCond
  rw [hW, ha, hi]

/-- Agreement on the final source window forces the target run to halt at the same
stage. No letters outside that window are needed. -/
theorem haltIndex_locality
    (h : ∀ u ∈ windowOut ϕ x T, x u = y u) :
    haltIndex ϕ x T = haltIndex ϕ y T := by
  have hp : ∀ i ≤ haltIndex ϕ x T,
      (stages ϕ x T i).LoopCond ↔ (stages ϕ y T i).LoopCond := by
    intro i hi
    obtain ⟨hW, hH⟩ := stages_locality i
      (fun u hu => h u (stages_W_mono ϕ x T hi hu))
    exact loopCond_congr hW hH
  apply le_antisymm
  · by_contra hn
    have hl : haltIndex ϕ y T < haltIndex ϕ x T := by omega
    exact not_loopCond_outStage ϕ y T
      ((hp _ (Nat.le_of_lt hl)).1 (loopCond_of_lt_haltIndex ϕ x T hl))
  · exact Nat.find_le (fun hc => not_loopCond_outStage ϕ x T ((hp _ le_rfl).2 hc))

/-- Agreement on the final source window also fixes the final target window. -/
theorem windowOut_locality (h : ∀ u ∈ windowOut ϕ x T, x u = y u) :
    windowOut ϕ x T = windowOut ϕ y T := by
  have he := (stages_locality (haltIndex ϕ x T) h).1
  simpa only [windowOut, outStage, ← haltIndex_locality h] using he

variable (ϕ x y T)

/-- The repaired invariant of Proposition 13.1.11, §13.1. The candidates carry `T` to
`T'` through the initial coset and match the plain strings on the current window.
The window transport, and hence agreement of the truncated strings, is proved below. -/
noncomputable def pairedQ (σ₀ : Equiv.Perm Ω) (i : ℕ) : Set (Equiv.Perm Ω) :=
  wIso (stages ϕ x T i).W (σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω))) x y

variable {ϕ x y T}

/-- A member of the initial coset has the same image of the test set as its representative. -/
theorem initialCoset_testImage {σ₀ σ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G)
    (hσ : σ ∈ σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω))) :
    ∃ h : σ ∈ G, testImage ϕ T ⟨σ, h⟩ = testImage ϕ T ⟨σ₀, hσ₀⟩ := by
  obtain ⟨κ, hκ, rfl⟩ := hσ
  have hkG := stabIn_le_top hκ
  refine ⟨G.mul_mem hσ₀ hkG, ?_⟩
  have he : (⟨σ₀ * κ, G.mul_mem hσ₀ hkG⟩ : G) = ⟨σ₀, hσ₀⟩ * ⟨κ, hkG⟩ := rfl
  change (ϕ ⟨σ₀ * κ, _⟩ : Equiv.Perm Γ) '' T = _
  rw [he, map_mul, perm_mul_image, (mem_stabIn.1 hκ).2]
  rfl

/-- Matching the source window transports the target stage. This proves the parallel
windows used on line 04c0, without assuming a full isomorphism of the input strings. -/
theorem pairedQ_window {σ₀ σ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G) (i : ℕ)
    (hσ : σ ∈ pairedQ ϕ x y T σ₀ i) :
    (stages ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) i).W =
      σ '' (stages ϕ x T i).W := by
  obtain ⟨hG, hT⟩ := initialCoset_testImage hσ₀ hσ.1
  have hag : ∀ u ∈ (stages ϕ x T i).W, x u = strAct y σ⁻¹ u := by
    intro u hu
    simpa only [strAct, inv_inv] using hσ.2 u hu
  have hW := (stages_locality i hag).1
  have he : strAct (strAct y σ⁻¹) σ = y := by
    rw [← strAct_mul, mul_inv_cancel, strAct_one]
  rw [← hT, ← he, stages_conj ϕ (strAct y σ⁻¹) T ⟨σ, hG⟩]
  exact congrArg (fun W => σ '' W) hW.symm

/-- Nonempty `Q` is the coset of the current source group that line 04c0 requires. -/
theorem pairedQ_eq_coset {σ₀ π : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G) (i : ℕ)
    (hπ : π ∈ pairedQ ϕ x y T σ₀ i) :
    pairedQ ϕ x y T σ₀ i = π • ((stages ϕ x T i).H : Set (Equiv.Perm Ω)) := by
  ext σ
  rw [mem_perm_smul_set, (stages ϕ x T i).isAut]
  constructor
  · intro hσ
    have hmem : π⁻¹ * σ ∈ bigGT ϕ T := by
      have he : π⁻¹ * σ = (σ₀⁻¹ * π)⁻¹ * (σ₀⁻¹ * σ) := by group
      rw [he]
      exact (bigGT ϕ T).mul_mem ((bigGT ϕ T).inv_mem (mem_perm_smul_set.1 hπ.1))
        (mem_perm_smul_set.1 hσ.1)
    refine ⟨hmem, fun u hu => ?_⟩
    have hw : (π⁻¹ * σ) u ∈ (stages ϕ x T i).W := by
      have he := (pairedQ_window hσ₀ i hπ).symm.trans (pairedQ_window hσ₀ i hσ)
      have hv : σ u ∈ π '' (stages ϕ x T i).W := by rw [he]; exact ⟨u, hu, rfl⟩
      obtain ⟨v, hv, heq⟩ := hv
      simpa [Equiv.Perm.mul_apply, ← heq] using hv
    have ha := hπ.2 _ hw
    simp only [Equiv.Perm.mul_apply] at ha
    simp at ha
    simpa [Equiv.Perm.mul_apply] using (hσ.2 u hu).trans ha.symm
  · rintro ⟨hmem, hr⟩
    have hH : π⁻¹ * σ ∈ (stages ϕ x T i).H := by
      change π⁻¹ * σ ∈ ((stages ϕ x T i).H : Set (Equiv.Perm Ω))
      rw [(stages ϕ x T i).isAut]
      exact ⟨hmem, hr⟩
    refine ⟨mem_perm_smul_set.2 ?_, fun u hu => ?_⟩
    · have he : σ₀⁻¹ * σ = (σ₀⁻¹ * π) * (π⁻¹ * σ) := by group
      rw [he]
      exact (bigGT ϕ T).mul_mem (mem_perm_smul_set.1 hπ.1) hmem
    · have ha := hπ.2 _ ((stages ϕ x T i).inv.mem_of_mem hH hu)
      simpa [Equiv.Perm.mul_apply] using (hr u hu).trans ha

/-- The comparison update adds only the new window conditions. -/
theorem pairedQ_succ (σ₀ : Equiv.Perm Ω) (i : ℕ) :
    pairedQ ϕ x y T σ₀ (i + 1) =
      wIso (stages ϕ x T i).aff (pairedQ ϕ x y T σ₀ i) x y := by
  ext σ
  constructor
  · rintro ⟨hm, hr⟩
    exact ⟨⟨hm, fun u hu => hr u ((stages ϕ x T i).sub_aff hu)⟩, hr⟩
  · rintro ⟨⟨hm, -⟩, hr⟩
    exact ⟨hm, hr⟩

/-- At termination a surviving candidate transports the final windows. -/
theorem pairedQ_windowOut {σ₀ σ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G)
    (hσ : σ ∈ pairedQ ϕ x y T σ₀ (haltIndex ϕ x T)) :
    windowOut ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) = σ '' windowOut ϕ x T := by
  obtain ⟨hG, hT⟩ := initialCoset_testImage hσ₀ hσ.1
  have hag : ∀ u ∈ windowOut ϕ x T, x u = strAct y σ⁻¹ u := by
    intro u hu
    simpa only [strAct, inv_inv] using hσ.2 u hu
  have hW := windowOut_locality hag
  have he : strAct (strAct y σ⁻¹) σ = y := by
    rw [← strAct_mul, mul_inv_cancel, strAct_one]
  rw [← hT, ← he, canonical_windowOut ϕ (strAct y σ⁻¹) T ⟨σ, hG⟩]
  exact congrArg (fun W => σ '' W) hW.symm

/-- **Proposition 13.1.11**, §13.1: the repaired final invariant gives the requested
colored, truncated isomorphisms. The size hypotheses give face transport and let the
reverse inclusion recover the test set from its face. -/
theorem pairedQ_out_eq_compareIso (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ)
    {T' : Set Γ} (hT' : T'.ncard = T.ncard) [Nonempty Ω]
    (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G)
    (hmap : testImage ϕ T ⟨σ₀, hσ₀⟩ = T') :
    pairedQ ϕ x y T σ₀ (haltIndex ϕ x T) = compareIso ϕ x y T T' := by
  have hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G) :=
    veryLargeK_of_setting ϕ hset (by have := ht.eight_lt; omega)
  ext σ
  constructor
  · intro hσ
    obtain ⟨hG, hT⟩ := initialCoset_testImage hσ₀ hσ.1
    have hW : windowOut ϕ y T' = σ '' windowOut ϕ x T := by
      rw [← hmap]
      exact pairedQ_windowOut hσ₀ hσ
    have hF : σ '' face ϕ T = face ϕ T' := by
      rw [face_image ϕ T hset hk ⟨σ, hG⟩]
      change face ϕ (testImage ϕ T ⟨σ, hG⟩) = _
      rw [hT, hmap]
    refine ⟨hG, strAct_eq_iff.2 fun u => ?_⟩
    have hw : σ u ∈ windowOut ϕ y T' ↔ u ∈ windowOut ϕ x T := by
      rw [hW, Set.mem_image_equiv]
      simp
    have hf : (u ∈ face ϕ T) ↔ σ u ∈ face ϕ T' := by
      rw [← hF, Set.mem_image_equiv]
      simp
    by_cases hu : u ∈ windowOut ϕ x T
    · rw [truncate_of_mem hu, truncate_of_mem (hw.2 hu)]
      exact congrArg some (Prod.ext (hσ.2 u hu) (decide_eq_decide.2 hf))
    · rw [truncate_of_not_mem hu, truncate_of_not_mem (fun hv => hu (hw.1 hv))]
  · intro hσ
    have hp : σ ∈ pairQOut ϕ x y T T' σ₀ := by
      rw [proposition_13_1_11 ϕ x y T T' hset ht htm hT' σ₀ hσ₀ hmap]
      exact hσ
    exact ⟨hp.1, fun u hu => (compareIso_window ϕ x y T T' hσ hu).2.1.symm⟩

/-- Every old candidate carries the new source window to the new target window.
This is the parallelism needed before making the calls on line 04e2. -/
theorem pairedQ_next_window {σ₀ σ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G) (i : ℕ)
    (hσ : σ ∈ pairedQ ϕ x y T σ₀ i) :
    (stages ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) (i + 1)).W =
      σ '' (stages ϕ x T i).aff := by
  obtain ⟨hG, hT⟩ := initialCoset_testImage hσ₀ hσ.1
  have hag : ∀ u ∈ (stages ϕ x T i).W, x u = strAct y σ⁻¹ u := by
    intro u hu
    simpa only [strAct, inv_inv] using hσ.2 u hu
  have hH := (stages_locality i hag).2
  have ha : (stages ϕ x T i).aff = (stages ϕ (strAct y σ⁻¹) T i).aff :=
    Set.ext fun u => affectedIn_congr hH _ _ u
  have he : strAct (strAct y σ⁻¹) σ = y := by
    rw [← strAct_mul, mul_inv_cancel, strAct_one]
  rw [← hT, ← he, stages_succ, Stage.step_W,
    stages_conj ϕ (strAct y σ⁻¹) T ⟨σ, hG⟩, Stage.conj_aff, ← ha]

/-- Transporting a window and matching its letters transports the truncated string. -/
theorem truncate_agree_of_image {A : Type*} {a b : Ω → A} {W W' : Set Ω}
    {σ : Equiv.Perm Ω} (hW : W' = σ '' W) (hr : ∀ u ∈ W, a u = b (σ u)) :
    strAct (truncate a W) σ = truncate b W' := by
  apply strAct_eq_iff.2
  intro u
  have hw : σ u ∈ W' ↔ u ∈ W := by rw [hW, Set.mem_image_equiv]; simp
  by_cases hu : u ∈ W
  · rw [truncate_of_mem hu, truncate_of_mem (hw.2 hu), hr u hu]
  · rw [truncate_of_not_mem hu, truncate_of_not_mem (fun hv => hu (hw.1 hv))]

/-- Agreement of truncated strings gives agreement of the original letters on the
source window. -/
theorem agree_of_truncate {A : Type*} {a b : Ω → A} {W W' : Set Ω}
    {σ : Equiv.Perm Ω} (hr : strAct (truncate a W) σ = truncate b W') :
    ∀ u ∈ W, a u = b (σ u) := by
  intro u hu
  have he := strAct_eq_iff.1 hr u
  rw [truncate_of_mem hu] at he
  by_cases hv : σ u ∈ W'
  · rw [truncate_of_mem hv] at he
    exact Option.some.inj he
  · rw [truncate_of_not_mem hv] at he
    simp at he

/-- **Proposition 13.1.11**, §13.1, the repaired invariant from its proof: `Q` consists
of the isomorphisms of the plain truncated strings in the initial test-set coset.
Unlike the printed invariant this also holds when both windows are empty. -/
theorem pairedQ_repaired_invariant (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G) (i : ℕ) :
    pairedQ ϕ x y T σ₀ i =
      strIso (σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω)))
        (truncate x (stages ϕ x T i).W)
        (truncate y (stages ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) i).W) := by
  ext σ
  constructor
  · intro hσ
    exact ⟨hσ.1, truncate_agree_of_image (pairedQ_window hσ₀ i hσ) hσ.2⟩
  · rintro ⟨hm, hr⟩
    exact ⟨hm, agree_of_truncate hr⟩

/-- **Proposition 13.1.11**, §13.1, line 04e2. Inside any part of `Q_old`, comparing
plain letters on the new window is exactly the printed comparison of colored,
truncated strings. The other letters are stars on both sides, and the test-set coset
already preserves the face bit. In particular this applies to each coset `(π * σ) N`.
Thus the paired reduction can keep the original alphabet in its oracle calls. -/
theorem pairedQ_colored_round (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G) (i : ℕ)
    (K : Set (Equiv.Perm Ω)) (hK : K ⊆ pairedQ ϕ x y T σ₀ i) :
    wIso (stages ϕ x T i).aff K x y =
      strIso K (truncate (colorByFace ϕ x T) (stages ϕ x T i).aff)
        (truncate (colorByFace ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩))
          (stages ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) (i + 1)).W) := by
  ext σ
  constructor
  · rintro ⟨hm, hr⟩
    obtain ⟨hG, hT⟩ := initialCoset_testImage hσ₀ (hK hm).1
    have hF : σ '' face ϕ T = face ϕ (testImage ϕ T ⟨σ₀, hσ₀⟩) := by
      rw [face_image ϕ T hset hk ⟨σ, hG⟩]
      exact congrArg (face ϕ) hT
    refine ⟨hm, truncate_agree_of_image (pairedQ_next_window hσ₀ i (hK hm)) ?_⟩
    intro u hu
    apply Prod.ext (hr u hu)
    apply decide_eq_decide.2
    rw [← hF, Set.mem_image_equiv]
    simp
  · rintro ⟨hm, hr⟩
    exact ⟨hm, fun u hu => congrArg Prod.fst (agree_of_truncate hr u hu)⟩

end Babai
