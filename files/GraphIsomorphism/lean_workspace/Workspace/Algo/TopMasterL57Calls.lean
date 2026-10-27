import Workspace.Algo.TopMasterLine4cd

/-! # The calls of lines 5–7 are admitted on the master carrier
The master carrier admits a call only if its letters are those of the node's strings and its
window is smaller than the node's (`Algo.MasterCallLetters`, `Algo.masterCheckedCall_admitted`).
Both hold for every call of the round of lines 5–7 without a hint:

* every call of Procedure AggregateCertificates (Sec. 13.2) and of the Chain Rule of line 5
  is a call of `Babai.cosetChain` on the two strings (or twice on one of them), so it has
  their letters;
* a call with no hint has a window of at most `4|Δ|/5` points (Eq. (72),
  `Babai.Line57Data.calls_progress`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Letters
variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {k : ℕ}

theorem masterLetters_strongDescent (N : Subgroup (Perm Ω)) {x y : Ω → ℕ}
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    ∀ J ∈ (strongDescent N x y L Δs).calls, MasterCallLetters k J := by
  intro J hJ
  rw [calls_strongDescent, List.mem_flatMap] at hJ
  obtain ⟨σ, _, hJ⟩ := hJ
  exact masterLetters_cosetChain k x y hx hy Δs _ J hJ

theorem masterLetters_localCertStrong {x : Ω → ℕ} (hx : ∀ u, x u < k) (T : Set Γ)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    ∀ J ∈ (localCertStrong ϕ x T L Δs).calls, MasterCallLetters k J := by
  intro J hJ
  rw [calls_localCertStrong] at hJ
  obtain ⟨i, _, hJ⟩ := mem_calls_loopStrong L Δs _ J hJ
  exact masterLetters_strongDescent _ hx hx _ _ J hJ

theorem masterLetters_compareStrong {x y : Ω → ℕ} (hx : ∀ u, x u < k) (hy : ∀ u, y u < k)
    (T : Set Γ) (σ : Option (Perm Ω)) (E : StrongPairEnum Ω) :
    ∀ J ∈ (compareStrong ϕ x T y σ E).calls, MasterCallLetters k J := by
  intro J hJ
  cases σ with
  | none => simp [compareStrong] at hJ
  | some ρ =>
    rw [compareStrong, calls_pairedComparisonStrong_eq] at hJ
    obtain ⟨i, _, hJ⟩ := mem_calls_pairedLoopStrong ρ E _ hJ
    rcases hJ with hJ | hJ
    · exact masterLetters_strongDescent _ hx hx _ _ J hJ
    · exact masterLetters_strongDescent _ hx hy _ _ J hJ

/-- **Sec. 13.2: every call of Procedure AggregateCertificates has the letters of the two
strings**, and so does every call of the round, if its continuation's calls do. -/
theorem masterLetters_aggregateRoundStrong {x y : Ω → ℕ} (hx : ∀ u, x u < k)
    (hy : ∀ u, y u < k) (E : AggEnum Ω Γ) {α : Type*} (R : SIReduction Ω ℕ α)
    (hR : ∀ J ∈ R.calls, MasterCallLetters k J) :
    ∀ J ∈ (aggregateRoundStrong ϕ x y E R).calls, MasterCallLetters k J := by
  have hb : ∀ b : Bool, ∀ u, (cond b y x) u < k := fun b => by cases b <;> assumption
  intro J hJ
  rw [calls_aggregateRoundStrong, List.mem_append, List.mem_append] at hJ
  rcases hJ with hJ | hJ | hJ
  · obtain ⟨S, hS, hJ⟩ := SIReduction.mem_calls_sequence hJ
    obtain ⟨b, T, _, rfl⟩ := (mem_certRunsStrong E).1 hS
    rw [calls_certRunStrong] at hJ
    exact masterLetters_localCertStrong (hb b) T _ _ J hJ
  · obtain ⟨S, hS, hJ⟩ := SIReduction.mem_calls_sequence hJ
    obtain ⟨b, T, _, T', _, rfl⟩ := (mem_compareRunsStrong E).1 hS
    exact masterLetters_compareStrong hx (hb b) T _ _ J hJ
  · exact hR J hJ
end Letters

/-! ### The round of lines 5–7 without a hint -/

/-- The round of lines 5–7 makes no hinted call: a reject exit, or Procedure Align without a
dominant color class. -/
def line57NoDom {W : Type*} [Fintype W] [DecidableEq W] {A : Type*}
    {G : Subgroup (Perm W)} {x y : W → A} {m : ℕ} {ϕ : G →* Perm (Fin m)} {ts : ℕ} :
    Line57Shape W A G x y ϕ ts → Prop
  | .align S => S.dom = none
  | .rejectDefect _ => True
  | .rejectCase _ _ => True
  | .rejectGuide _ _ _ _ _ => True

section Shape
variable {N : ℕ} {G : Subgroup (Perm (Fin N))} {x y : Fin N → ℕ} {m : ℕ}
    {ϕ : G →* Perm (Fin m)} {ts : ℕ}

theorem line57Shape_hint_none (S : Line57Shape (Fin N) ℕ G x y ϕ ts) (h : line57NoDom S)
    (J : SIInstance (Fin N) ℕ) : S.hint J = none := by
  cases S with
  | align S => exact alignShape_hint_eq_none_of_dom_none S h J
  | rejectDefect _ => rfl
  | rejectCase _ _ => rfl
  | rejectGuide _ _ _ _ _ => rfl

theorem line57Shape_letters {k : ℕ} (S : Line57Shape (Fin N) ℕ G x y ϕ ts) (h : line57NoDom S)
    (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) (E : AggEnum (Fin N) (Fin m)) :
    ∀ J ∈ (S.red E).calls, MasterCallLetters k J := by
  refine masterLetters_aggregateRoundStrong hx hy E _ ?_
  cases S with
  | align S => exact alignShape_letters_of_dom_none S h hx hy
  | rejectDefect _ => intro J hJ; simp [Line57Shape.inner] at hJ
  | rejectCase _ _ => intro J hJ; simp [Line57Shape.inner] at hJ
  | rejectGuide _ _ _ _ _ => intro J hJ; simp [Line57Shape.inner] at hJ

/-- **Eq. (72) for lines 5–7**: without a hint, every call of the round has a window of at
most `4N/5` points and the letters of the two strings. -/
theorem line57Data_calls_small {k par cost : ℕ} (D : Line57Data (Fin N) ℕ G x y ϕ ts par cost)
    (h : line57NoDom D.shape) (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ (D.shape.red D.enum).calls, MasterCallLetters k J ∧ 5 * J.windowSize ≤ 4 * N := by
  intro J hJ
  refine ⟨line57Shape_letters D.shape h hx hy D.enum J hJ, ?_⟩
  rcases D.calls_progress J hJ with hs | hs
  · rwa [Fintype.card_fin] at hs
  · rw [line57Shape_hint_none D.shape h] at hs
    exact absurd hs (by simp)
end Shape

/-! ### The lifted calls at a hinted node -/

section Node
variable {n : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1) (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n p.1.1))

include hx hy hnd hlt in
/-- The two strings on the window keep the letters of the node's strings. -/
theorem masterHintTop_letters :
    (∀ u, decStrN p.1.1.length (masterHintTop p).2.1 u < 2 * n + 1) ∧
      ∀ u, decStrN p.1.1.length (masterHintTop p).2.2 u < 2 * n + 1 := by
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hyy := (masterStrWF_iff hy.1).mp hy
  constructor
  · rw [show (masterHintTop p).2.1 = rawRestrictStr (p.1.2.2.2.1, p.1.1) from rfl,
      topwRestrictStr_decode hnd hlt]
    exact fun u => hxx _
  · rw [show (masterHintTop p).2.2 = rawRestrictStr
      (top4aTarget (p.1.2.2.2.1, p.1.2.2.1, p.1.2.2.2.2), p.1.1) from rfl,
      top4aTarget_restrict hx.1 hnd hlt]
    exact fun u => hyy _

/-- A letter of a string of length `N` whose decoded letters are below `k` is below `k`. -/
theorem lt_of_mem_decStrN_lt {N k : ℕ} {xs : RawStr} (hxs : xs.length = N)
    (h : ∀ u : Fin N, decStrN N xs u < k) {a : ℕ} (ha : a ∈ xs) : a < k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  have := h ⟨i, hxs ▸ hi⟩
  simp only [decStrN] at this
  rwa [List.getD_eq_getElem _ _ hi] at this

include hx hy hnd hlt in
/-- The letters of the window are below `2n + 1`, and so is every entry of the list `M` of the
renaming (`Algo.masterL57Order`). -/
theorem masterL57Order_letters :
    ∀ a ∈ masterL57Order (p.1, some p.2), a < 2 * n + 1 := by
  obtain ⟨hix, hiy⟩ := masterHintTop_letters hx hy hnd hlt
  have hL : ∀ a ∈ masterL57Letters (p.1, some p.2), a < 2 * p.1.2.2.2.1.length + 1 := by
    intro a ha
    rw [hx.1]
    rcases mem_masterL57Letters.1 ha with ha | ha
    · exact lt_of_mem_decStrN_lt (length_masterL57XW _) hix ha
    · exact lt_of_mem_decStrN_lt (length_masterL57YW _) hiy ha
  intro a ha
  have := masterL57Order_lt hL ha
  rwa [hx.1] at this

include hx hy in
/-- **The calls of lines 5–7, renamed back and lifted to the node's domain**: if the calls of
a window tree `T₀` have letters at most `2|Δ|` and are coset instances in the restricted group,
then every lifted call of `T₀` with its letters renamed back has the letters of the node's
strings, is a coset instance, and has the window of a call of `T₀`. -/
theorem masterL57Unl_lifted_calls
    {T₀ : SIReduction (Fin p.1.1.length) ℕ (Set (Perm (Fin p.1.1.length)))}
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * p.1.1.length + 1) J)
    (hcos : ∀ J ∈ T₀.calls, IsCosetInstance (winRestrictHom n p.1.1 hnd hlt G hinv).range J) :
    ∀ J ∈ (top4wTree p.1.1 hnd hlt G hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) T₀)).calls,
      MasterCallLetters (2 * n + 1) J ∧ IsCosetInstance G J ∧
        ∃ K ∈ T₀.calls, J.windowSize = K.windowSize := by
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hN : p.1.1.length ≤ p.1.2.2.2.1.length := by
    rw [hx.1]; exact length_le_of_nodup_lt hnd hlt
  have hcalls := masterL57Unl_calls (P := (p.1, some p.2)) hN hlet
  have hcosU : ∀ J ∈ (masterL57Unl (p.1, some p.2) T₀).calls,
      IsCosetInstance (winRestrictHom n p.1.1 hnd hlt G hinv).range J := by
    rw [hcalls]
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact isCosetInstance_siUnlabel _ (hcos J₀ hJ₀)
  have hKU : ∀ J ∈ (masterL57Unl (p.1, some p.2) T₀).calls,
      J.K ⊆ ((winRestrictHom n p.1.1 hnd hlt G hinv).range : Set (Perm (Fin p.1.1.length))) :=
    fun J hJ => (hcosU J hJ).K_subset
  have hcos' := top4wTree_calls_isCosetInstance hnd hlt hinv (decStrN n p.1.2.2.2.1) _ hcosU
  intro J hJ
  have hJc := hcos' J hJ
  simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
  rw [calls_topwReduction hnd hlt hinv _ _ hKU, hcalls, List.map_map] at hJ
  obtain ⟨K, hKm, rfl⟩ := List.mem_map.mp hJ
  refine ⟨masterLetters_topwInstance p.1.1 hnd hlt _ hinv _ hxx _
    (siUnlabel_letters (Nat.succ_pos _) (masterL57Order_letters hx hy hnd hlt) K), hJc, K, hKm,
    ?_⟩
  simp only [Function.comp, topwInstance_windowSize, siUnlabel_windowSize]

include hx hy in
/-- **The calls of lines 5–7, lifted to the node's domain, are admitted**: at a node with a
nonempty window, every lifted call of a round of lines 5–7 without a hint, with its letters
renamed back, has the letters of the node's strings and a smaller window. This is the
hypothesis `hL` of `Algo.masterL57_match`. -/
theorem masterL57_calls_admitted (hΔ : 0 < p.1.1.length)
    {G' : Subgroup (Perm (Fin p.1.1.length))} {m : ℕ} {ϕ : G' →* Perm (Fin m)} {ts par cost : ℕ}
    (D : Line57Data (Fin p.1.1.length) ℕ G'
      (decStrN p.1.1.length (masterL57Ctx (p.1, some p.2)).2.1)
      (decStrN p.1.1.length (masterL57Ctx (p.1, some p.2)).2.2.1) ϕ ts par cost)
    (hno : line57NoDom D.shape)
    (hK : ∀ J ∈ (D.shape.red D.enum).calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt G hinv).range : Set (Perm (Fin p.1.1.length)))) :
    ∀ J ∈ (top4wTree p.1.1 hnd hlt G hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) (D.shape.red D.enum))).calls,
      MasterCallLetters (2 * n + 1) J ∧ J.windowSize < p.1.1.length ∧
        ∃ G₀ : Subgroup (Perm (Fin n)), IsCosetInstance G₀ J := by
  have hsmall := line57Data_calls_small D hno (k := 2 * p.1.1.length + 1)
    (masterL57Ctx_letters_x (p.1, some p.2)) (masterL57Ctx_letters_y (p.1, some p.2))
  have h := masterL57Unl_lifted_calls hx hy hnd hlt hinv (T₀ := D.shape.red D.enum)
    (fun J hJ => (hsmall J hJ).1) (fun J hJ => (D.calls_coset J hJ).of_K_subset (hK J hJ))
  intro J hJ
  obtain ⟨hl, hc, K, hKm, hw⟩ := h J hJ
  refine ⟨hl, ?_, _, hc⟩
  rw [hw]
  have := (hsmall K hKm).2
  omega
end Node

end Algo
