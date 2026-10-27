import Workspace.Algo.TopMasterHintCarrier
import Workspace.Algo.AggNodeCertInit

/-! # The context of lines 5–7, in the window's own size

Section 15, lines 5–7: at a hinted node of degree `n` with window `Δ` of size `N = |Δ|`, the
Master Algorithm runs Procedure AggregateCertificates and then Procedure Align on the window,
that is on the action of `G_Δ` on `Δ` with the two strings `x_Δ`, `y_Δ` (the restrictions of
`x` and of `y^{σ⁻¹}` to `Δ`). The machine runs this round on its own input, whose size must be
bounded by a function of `N` (the round's width, state and children are bounded in the size of
its input, `Algo.AggnCheckedWF`), and whose letters must lie below `2N + 1` (the round reads
its children with the letters capped at `2N`, `Algo.aggnCheckedWindow`).

The restriction of the node's data to `Δ` does not have this shape: the list of the window
holds the node's points (up to `n`), the generators of `G_Δ` are as many as those of `G`
(up to `n²`), the hint's list of `Γ` may hold large numbers, and the letters of `x_Δ`, `y_Δ`
are those of `x`, `y` (up to `2n`). This file gives the window's data in its own size, with
the same meaning:

* the domain of the action is `0, …, N-1`, and the domain of `Γ` is `0, …, m-1`;
* the generators of `G_Δ` are shortened to at most `N²` (`Algo.tidyGens`), and their images
  under the hint's representation `ϕ` are recomputed (`Algo.rawImgOf`);
* the letters of `x_Δ`, `y_Δ` are renamed by one injective map `ρ` onto `0, …, k-1`, where
  `k ≤ 2N` is the number of letters they use (`Algo.masterL57Relabel`). A common injective
  renaming of the letters changes no set of isomorphisms (`Algo.strIso_comp_injOn`,
  `Algo.wIso_comp_injOn`). The renaming is a bijection of `0, …, 2n` (`Algo.masterL57Order`
  lists its inverse), so the calls of the round are renamed back (`Algo.masterL57Unlabel`)
  before they are lifted to the node: the node's children are the paper's calls.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ### Renaming letters does not change isomorphisms -/

section Rename

variable {Ω : Type*} {A B : Type*}

/-- A renaming of the letters that is injective on the letters used changes no `Iso_K`. -/
theorem strIso_comp_injOn (K : Set (Perm Ω)) {x y : Ω → A} {r : A → B} {S : Set A}
    (hr : Set.InjOn r S) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    strIso K (r ∘ x) (r ∘ y) = strIso K x y := by
  ext τ
  simp only [strIso, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h => funext fun u => ?_, fun h => ?_⟩
  · have := congrFun h u
    exact hr (hx _) (hy _) this
  · rw [← h]
    rfl

/-- A renaming of the letters that is injective on the letters used changes no `Iso^Δ_K`. -/
theorem wIso_comp_injOn (Δ : Set Ω) (K : Set (Perm Ω)) {x y : Ω → A} {r : A → B} {S : Set A}
    (hr : Set.InjOn r S) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    wIso Δ K (r ∘ x) (r ∘ y) = wIso Δ K x y := by
  ext τ
  simp only [wIso, Set.mem_setOf_eq, Function.comp]
  refine and_congr_right fun _ => forall₂_congr fun u _ => ⟨fun h => ?_, fun h => by rw [h]⟩
  exact hr (hx _) (hy _) h

end Rename

/-! ### The renaming of the letters -/

/-- The first string on the window (`x_Δ`), before the renaming. -/
abbrev masterL57XW (P : RawMasterSI) : RawStr := (masterHintTop (masterHintGet P)).2.1

/-- The second string on the window (`y^{σ⁻¹}` on `Δ`), before the renaming. -/
abbrev masterL57YW (P : RawMasterSI) : RawStr := (masterHintTop (masterHintGet P)).2.2

/-- The letters the two strings on the window use, each once. -/
def masterL57Letters (P : RawMasterSI) : List ℕ :=
  dedupG (([] : List ℕ), masterL57XW P ++ masterL57YW P)

/-- The test of the second part of `Algo.masterL57Order`: `a` is not a letter of the window. -/
def masterL57NotLetter (p : List ℕ × ℕ) : Bool := !decide (p.2 ∈ p.1)

/-- **The inverse of the renaming**: the letters of the window first, then the other numbers
below `2n + 1`, with `n` the node's degree. Position `i` holds the letter renamed to `i`. -/
def masterL57Order (P : RawMasterSI) : List ℕ :=
  masterL57Letters P ++ (List.range (2 * P.1.2.2.2.1.length + 1)).filter
    (fun a => masterL57NotLetter (masterL57Letters P, a))

/-- The position of `a` in the list `M` (the renaming of a letter). -/
def masterL57Rank (p : List ℕ × ℕ) : ℕ := rawInvLookup (p.1.zipIdx, p.2)

/-- **The renaming of a string**: each letter is replaced by its position in `M`. -/
def masterL57Relabel (p : List ℕ × RawStr) : RawStr := p.2.map (fun a => masterL57Rank (p.1, a))

/-- **The renaming back**: each letter `i` is replaced by the entry of `M` at position `i`. -/
def masterL57Unlabel (p : List ℕ × RawStr) : RawStr := p.2.map (fun c => rawGet (p.1, c))

/-- A window instance with its letters renamed back. -/
def masterL57UnlabelWin (p : List ℕ × RawWinSI) : RawWinSI :=
  (p.2.1, p.2.2.1, p.2.2.2.1, masterL57Unlabel (p.1, p.2.2.2.2.1),
    masterL57Unlabel (p.1, p.2.2.2.2.2))

/-! ### The action on the window -/

/-- The generators of `G_Δ` on the window, shortened to at most `N²`. -/
def masterL57Gens (P : RawMasterSI) : RawGens :=
  tidyGens (masterL57XW P, (masterHintTop (masterHintGet P)).1.1.2)

/-- **The action on the window, in the window's size**: the domain `0, …, N-1` with the
shortened generators of `G_Δ`, and the domain `0, …, m-1` of `Γ` with their images under the
hint's representation. -/
def masterL57Action (P : RawMasterSI) : RawAction :=
  ((List.range P.1.1.length, masterL57Gens P),
    (List.range (masterHintTop (masterHintGet P)).1.2.1.length,
      (masterL57Gens P).map (fun g => rawImgOf ((masterHintTop (masterHintGet P)).1, g))))

/-! ### Specifications -/

section Spec

variable {P : RawMasterSI}

theorem length_masterL57XW (P : RawMasterSI) : (masterL57XW P).length = P.1.1.length := by
  simp [masterL57XW, masterHintTop, primitiveWindowInput, masterHintGet]

theorem length_masterL57YW (P : RawMasterSI) : (masterL57YW P).length = P.1.1.length := by
  simp [masterL57YW, masterHintTop, primitiveWindowInput, masterHintGet]

theorem mem_masterL57Letters {a : ℕ} :
    a ∈ masterL57Letters P ↔ a ∈ masterL57XW P ∨ a ∈ masterL57YW P := by
  rw [masterL57Letters, mem_dedupG_nil, List.mem_append]

theorem nodup_masterL57Letters (P : RawMasterSI) : (masterL57Letters P).Nodup :=
  nodup_dedupG _

theorem length_masterL57Letters_le (P : RawMasterSI) :
    (masterL57Letters P).length ≤ 2 * P.1.1.length := by
  have h := (nodup_masterL57Letters P).subperm (l₂ := masterL57XW P ++ masterL57YW P)
    (fun a ha => List.mem_append.2 (mem_masterL57Letters.1 ha))
  have := h.length_le
  rw [List.length_append, length_masterL57XW, length_masterL57YW] at this
  omega

theorem nodup_masterL57Order (P : RawMasterSI) : (masterL57Order P).Nodup := by
  rw [masterL57Order, List.nodup_append]
  refine ⟨nodup_masterL57Letters P, List.nodup_range.filter _, fun a ha b hb => ?_⟩
  rintro rfl
  rw [List.mem_filter] at hb
  simp [masterL57NotLetter, ha] at hb

/-- When the letters of the window lie below `B = 2n + 1`, the list `M` holds exactly the
numbers below `B`. -/
theorem mem_masterL57Order (hL : ∀ a ∈ masterL57Letters P, a < 2 * P.1.2.2.2.1.length + 1)
    {a : ℕ} : a ∈ masterL57Order P ↔ a < 2 * P.1.2.2.2.1.length + 1 := by
  rw [masterL57Order, List.mem_append, List.mem_filter, List.mem_range]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact hL a h
    · exact h
  · intro h
    by_cases hm : a ∈ masterL57Letters P
    · exact Or.inl hm
    · exact Or.inr ⟨h, by simp [masterL57NotLetter, hm]⟩

theorem length_masterL57Order (hL : ∀ a ∈ masterL57Letters P, a < 2 * P.1.2.2.2.1.length + 1) :
    (masterL57Order P).length = 2 * P.1.2.2.2.1.length + 1 := by
  have hp : (masterL57Order P).Perm (List.range (2 * P.1.2.2.2.1.length + 1)) :=
    (List.perm_ext_iff_of_nodup (nodup_masterL57Order P) List.nodup_range).2 fun a => by
      rw [mem_masterL57Order hL, List.mem_range]
  rw [hp.length_eq, List.length_range]

/-- The renaming of a letter of the window is its position among the letters, and the entry of
`M` there is the letter. -/
theorem masterL57Rank_letter {a : ℕ} (ha : a ∈ masterL57Letters P) :
    masterL57Rank (masterL57Order P, a) < (masterL57Letters P).length ∧
      rawGet (masterL57Order P, masterL57Rank (masterL57Order P, a)) = a := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
  have hjM : j < (masterL57Order P).length := by
    rw [masterL57Order, List.length_append]; omega
  have he : (masterL57Order P)[j] = (masterL57Letters P)[j] := by
    simp only [masterL57Order]
    rw [List.getElem_append_left hj]
  have hr : masterL57Rank (masterL57Order P, (masterL57Letters P)[j]) = j := by
    rw [← he]
    exact rawInvLookup_getElem (nodup_masterL57Order P) hjM
  rw [hr]
  refine ⟨hj, ?_⟩
  rw [rawGet, List.getD_eq_getElem _ _ hjM, he]

/-- The renaming back is injective on the positions of `M`. -/
theorem masterL57Unlabel_injOn (P : RawMasterSI) :
    Set.InjOn (fun c => rawGet (masterL57Order P, c)) {c | c < (masterL57Order P).length} := by
  intro c hc c' hc' h
  simp only [rawGet, Set.mem_setOf_eq] at h hc hc'
  rw [List.getD_eq_getElem _ _ hc, List.getD_eq_getElem _ _ hc'] at h
  exact (List.Nodup.getElem_inj_iff (nodup_masterL57Order P)).1 h

/-- The renaming is injective on the letters of the window. -/
theorem masterL57Rank_injOn (P : RawMasterSI) :
    Set.InjOn (fun a => masterL57Rank (masterL57Order P, a)) {a | a ∈ masterL57Letters P} := by
  intro a ha a' ha' h
  have h1 := (masterL57Rank_letter ha).2
  have h2 := (masterL57Rank_letter ha').2
  simp only at h
  rw [← h1, ← h2, h]

/-- Every number below `2n + 1` is in `M`, so `M` has at least `2n + 1` entries. -/
theorem lt_mem_masterL57Order (P : RawMasterSI) {a : ℕ} (ha : a < 2 * P.1.2.2.2.1.length + 1) :
    a ∈ masterL57Order P := by
  rw [masterL57Order, List.mem_append, List.mem_filter, List.mem_range]
  by_cases hm : a ∈ masterL57Letters P
  · exact Or.inl hm
  · exact Or.inr ⟨ha, by simp [masterL57NotLetter, hm]⟩

theorem le_length_masterL57Order (P : RawMasterSI) :
    2 * P.1.2.2.2.1.length + 1 ≤ (masterL57Order P).length := by
  have h := (List.nodup_range (n := 2 * P.1.2.2.2.1.length + 1)).subperm
    (l₂ := masterL57Order P) (fun a ha => lt_mem_masterL57Order P (List.mem_range.1 ha))
  simpa using h.length_le

/-- When the letters of the window are below `2n + 1`, so is every entry of `M`. -/
theorem masterL57Order_lt (hL : ∀ a ∈ masterL57Letters P, a < 2 * P.1.2.2.2.1.length + 1)
    {a : ℕ} (ha : a ∈ masterL57Order P) : a < 2 * P.1.2.2.2.1.length + 1 :=
  (mem_masterL57Order hL).1 ha

/-- The renamed string, decoded: each letter is renamed. -/
theorem decStrN_masterL57Relabel {N : ℕ} (M : List ℕ) {xs : RawStr} (hxs : xs.length = N) :
    decStrN N (masterL57Relabel (M, xs)) = fun u => masterL57Rank (M, decStrN N xs u) := by
  funext u
  have hu : (u : ℕ) < xs.length := hxs ▸ u.isLt
  simp only [decStrN, masterL57Relabel]
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map,
    List.getD_eq_getElem _ _ hu]

/-- The string renamed back, decoded: each letter is renamed back. -/
theorem decStrN_masterL57Unlabel {N : ℕ} (M : List ℕ) {xs : RawStr} (hxs : xs.length = N) :
    decStrN N (masterL57Unlabel (M, xs)) = fun u => rawGet (M, decStrN N xs u) := by
  funext u
  have hu : (u : ℕ) < xs.length := hxs ▸ u.isLt
  simp only [decStrN, masterL57Unlabel]
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map,
    List.getD_eq_getElem _ _ hu]

/-- The letters of the renamed strings are positions among the window's letters. -/
theorem masterL57Rank_lt_letters {N : ℕ} {xs : RawStr} (hxs : xs.length = N)
    (hsub : ∀ a ∈ xs, a ∈ masterL57Letters P) (u : Fin N) :
    decStrN N (masterL57Relabel (masterL57Order P, xs)) u < (masterL57Letters P).length := by
  rw [decStrN_masterL57Relabel _ hxs]
  have hu : (u : ℕ) < xs.length := hxs ▸ u.isLt
  refine (masterL57Rank_letter (hsub _ ?_)).1
  simp only [decStrN]
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem hu

/-- **Renaming the letters of the window does not change `Iso_K`.** -/
theorem strIso_masterL57Relabel {N : ℕ} (K : Set (Perm (Fin N))) {xs ys : RawStr}
    (hxs : xs.length = N) (hys : ys.length = N)
    (hx : ∀ a ∈ xs, a ∈ masterL57Letters P) (hy : ∀ a ∈ ys, a ∈ masterL57Letters P) :
    strIso K (decStrN N (masterL57Relabel (masterL57Order P, xs)))
        (decStrN N (masterL57Relabel (masterL57Order P, ys))) =
      strIso K (decStrN N xs) (decStrN N ys) := by
  rw [decStrN_masterL57Relabel _ hxs, decStrN_masterL57Relabel _ hys]
  have hmem : ∀ (zs : RawStr), zs.length = N → (∀ a ∈ zs, a ∈ masterL57Letters P) →
      ∀ u : Fin N, decStrN N zs u ∈ {a | a ∈ masterL57Letters P} := by
    intro zs hzs hz u
    have hu : (u : ℕ) < zs.length := hzs ▸ u.isLt
    simp only [decStrN, Set.mem_setOf_eq]
    rw [List.getD_eq_getElem _ _ hu]
    exact hz _ (List.getElem_mem hu)
  exact strIso_comp_injOn K (masterL57Rank_injOn P) (hmem xs hxs hx) (hmem ys hys hy)

theorem masterL57XW_letters (P : RawMasterSI) : ∀ a ∈ masterL57XW P, a ∈ masterL57Letters P :=
  fun _ ha => mem_masterL57Letters.2 (Or.inl ha)

theorem masterL57YW_letters (P : RawMasterSI) : ∀ a ∈ masterL57YW P, a ∈ masterL57Letters P :=
  fun _ ha => mem_masterL57Letters.2 (Or.inr ha)

end Spec


/-! ### Renaming back the calls of a round -/

section Calls
variable {Ω : Type} {α : Type}

/-- An instance with its letters renamed back through the list `M`: letter `c` becomes the
entry of `M` at position `c`. The group, the coset and the window are unchanged. -/
def siUnlabel (M : List ℕ) (I : SIInstance Ω ℕ) : SIInstance Ω ℕ :=
  ⟨I.K, I.Δ, fun u => rawGet (M, I.x u), fun u => rawGet (M, I.y u)⟩

@[simp] theorem siUnlabel_K (M : List ℕ) (I : SIInstance Ω ℕ) : (siUnlabel M I).K = I.K := rfl
@[simp] theorem siUnlabel_Δ (M : List ℕ) (I : SIInstance Ω ℕ) : (siUnlabel M I).Δ = I.Δ := rfl

theorem siUnlabel_windowSize (M : List ℕ) (I : SIInstance Ω ℕ) :
    (siUnlabel M I).windowSize = I.windowSize := rfl

theorem isCosetInstance_siUnlabel {G : Subgroup (Perm Ω)} (M : List ℕ) {I : SIInstance Ω ℕ}
    (h : IsCosetInstance G I) : IsCosetInstance G (siUnlabel M I) := h

/-- Renaming back through a list without repetition changes no answer, when every letter of
the instance is a position of the list. -/
theorem siUnlabel_answer {M : List ℕ} (hM : M.Nodup) {I : SIInstance Ω ℕ}
    (hx : ∀ u, I.x u < M.length) (hy : ∀ u, I.y u < M.length) :
    (siUnlabel M I).answer = I.answer := by
  have hr : Set.InjOn (fun c => rawGet (M, c)) {c | c < M.length} := by
    intro c hc c' hc' h
    simp only [rawGet, Set.mem_setOf_eq] at h hc hc'
    rw [List.getD_eq_getElem _ _ hc, List.getD_eq_getElem _ _ hc'] at h
    exact (List.Nodup.getElem_inj_iff hM).1 h
  exact wIso_comp_injOn I.Δ I.K hr hx hy

/-- The letters of an instance renamed back are entries of `M` (or the default `0`). -/
theorem siUnlabel_letters {M : List ℕ} {k : ℕ} (hk : 0 < k) (hM : ∀ a ∈ M, a < k)
    (I : SIInstance Ω ℕ) : MasterCallLetters k (siUnlabel M I) := by
  have h : ∀ c, rawGet (M, c) < k := by
    intro c
    simp only [rawGet]
    rcases lt_or_ge c M.length with hc | hc
    · rw [List.getD_eq_getElem _ _ hc]
      exact hM _ (List.getElem_mem hc)
    · rw [List.getD_eq_default _ _ hc]
      exact hk
  exact ⟨fun u => h _, fun u => h _⟩

/-- A reduction with every call replaced by its image under `f`; the continuations are
unchanged. -/
def redMapCalls (f : SIInstance Ω ℕ → SIInstance Ω ℕ) :
    SIReduction Ω ℕ α → SIReduction Ω ℕ α
  | .done a => .done a
  | .call I k => .call (f I) (fun a => redMapCalls f (k a))

/-- The mapped reduction has the same value, when `f` keeps the answer of every call. -/
theorem run_redMapCalls (f : SIInstance Ω ℕ → SIInstance Ω ℕ) :
    ∀ (T : SIReduction Ω ℕ α), (∀ I ∈ T.calls, (f I).answer = I.answer) →
      (redMapCalls f T).run = T.run := by
  intro T
  induction T with
  | done a => intro _; rfl
  | call I k ih =>
    intro h
    have hI : (f I).answer = I.answer := h I (by simp)
    change (redMapCalls f (k (f I).answer)).run = (k I.answer).run
    rw [hI]
    exact ih _ fun I' hI' => h I' (by simp [hI'])

/-- The calls of the mapped reduction are the images of the calls, when `f` keeps the answer
of every call. -/
theorem calls_redMapCalls (f : SIInstance Ω ℕ → SIInstance Ω ℕ) :
    ∀ (T : SIReduction Ω ℕ α), (∀ I ∈ T.calls, (f I).answer = I.answer) →
      (redMapCalls f T).calls = T.calls.map f := by
  intro T
  induction T with
  | done a => intro _; rfl
  | call I k ih =>
    intro h
    have hI : (f I).answer = I.answer := h I (by simp)
    change f I :: (redMapCalls f (k (f I).answer)).calls = f I :: (k I.answer).calls.map f
    rw [hI, ih _ fun I' hI' => h I' (by simp [hI'])]

/-- **Renaming the calls of a fold.** If at every call of the round the second decoding is
the image under `f` of the first, with the same answer, then a match with the first decoding
gives a match with the second, for the tree with its calls mapped by `f`. -/
theorem loopMatch_redMapCalls {ι ω β : Type} [Fintype Ω] [DecidableEq Ω] {R : Round ι ω β}
    {dec₁ dec₂ : ι → SIInstance Ω ℕ} {decA : β → Set (Perm Ω)} {I : ι}
    (f : SIInstance Ω ℕ → SIInstance Ω ℕ)
    (hf : ∀ j s J, R.child (I, j, s) = some J →
      dec₂ J = f (dec₁ J) ∧ (f (dec₁ J)).answer = (dec₁ J).answer) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω ℕ (Set (Perm Ω))},
      LoopMatch R dec₁ decA I w j s T → LoopMatch R dec₂ decA I w j s (redMapCalls f T) := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact .done w j s a hc ha
  | call w j s J k hc _ ih =>
    obtain ⟨h2, hans⟩ := hf j s J hc
    have hans' : (dec₂ J).answer = (dec₁ J).answer := by rw [h2, hans]
    change LoopMatch R dec₂ decA I (w + 1) j s (.call (f (dec₁ J)) _)
    rw [← h2]
    refine .call w j s J _ hc fun a ha => ?_
    rw [hans'] at ha ⊢
    exact ih a ha
/-- A window instance renamed back, decoded, is the decoded instance renamed back. -/
theorem decWinSI_masterL57UnlabelWin {N : ℕ} (M : List ℕ) {V : RawWinSI}
    (hx : V.2.2.2.1.length = N) (hy : V.2.2.2.2.length = N) :
    decWinSI N (masterL57UnlabelWin (M, V)) = siUnlabel M (decWinSI N V) := by
  unfold decWinSI siUnlabel masterL57UnlabelWin
  simp only [decStrN_masterL57Unlabel M hx, decStrN_masterL57Unlabel M hy]

end Calls

/-! ### Running time -/

section Poly

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_masterL57XW : PolyFun masterL57XW :=
  pfst (psnd (polyFun_masterHintGet.comp polyFun_masterHintTop))

theorem polyFun_masterL57YW : PolyFun masterL57YW :=
  psnd (psnd (polyFun_masterHintGet.comp polyFun_masterHintTop))

theorem polyFun_masterL57Letters : PolyFun masterL57Letters :=
  (((polyFun_const ([] : List ℕ)).pair ((polyFun_masterL57XW.pair polyFun_masterL57YW).comp
    polyFun_append)).comp (polyFun_dedupG polyFun_natEq)).of_eq (fun _ => rfl)

theorem polyFun_masterL57NotLetter : PolyFun masterL57NotLetter := by
  have hm : PolyFun (fun p : List ℕ × ℕ => decide (p.2 ∈ p.1)) :=
    (polyFun_snd.pair polyFun_fst).comp (polyFun_listMem polyFun_natEq)
  refine (PolyFun.ite hm (polyFun_const false) (polyFun_const true)).of_eq (fun p => ?_)
  by_cases h : p.2 ∈ p.1 <;> simp [masterL57NotLetter, h]

theorem polyFun_masterL57Order : PolyFun masterL57Order := by
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun P : RawMasterSI => List.range (2 * P.1.2.2.2.1.length + 1)) := by
    refine (((hx.pair hx).comp polyFun_append).pair (polyFun_const [0])).comp polyFun_append
      |>.comp polyFun_rangeLength |>.of_eq (fun P => ?_)
    simp only [List.length_append, List.length_singleton]
    congr 1
    omega
  exact ((polyFun_masterL57Letters.pair ((polyFun_masterL57Letters.pair hr).comp
    (PolyFun.filterParam polyFun_masterL57NotLetter))).comp polyFun_append).of_eq
      (fun _ => rfl)

theorem polyFun_masterL57Rank : PolyFun masterL57Rank :=
  ((((polyFun_fst.comp polyFun_zipIdx).pair polyFun_snd)).comp polyFun_rawInvLookup).of_eq
    (fun _ => rfl)

theorem polyFun_masterL57Relabel : PolyFun masterL57Relabel :=
  (PolyFun.mapParam polyFun_masterL57Rank).of_eq (fun _ => rfl)

theorem polyFun_masterL57Unlabel : PolyFun masterL57Unlabel :=
  (PolyFun.mapParam polyFun_rawGet).of_eq (fun _ => rfl)

theorem polyFun_masterL57UnlabelWin : PolyFun masterL57UnlabelWin := by
  let Z := List ℕ × RawWinSI
  have i : PolyFun (fun z : Z => z) := polyFun_id
  exact (pfst (psnd i)).pair ((pfst (psnd (psnd i))).pair ((pfst (psnd (psnd (psnd i)))).pair
    ((((pfst i).pair (pfst (psnd (psnd (psnd (psnd i)))))).comp polyFun_masterL57Unlabel).pair
      (((pfst i).pair (psnd (psnd (psnd (psnd (psnd i)))))).comp polyFun_masterL57Unlabel))))

theorem polyFun_masterL57Gens : PolyFun masterL57Gens := by
  have ht := polyFun_masterHintGet.comp polyFun_masterHintTop
  exact (polyFun_masterL57XW.pair (psnd (pfst (pfst ht)))).comp polyFun_tidyGens

theorem polyFun_masterL57Action : PolyFun masterL57Action := by
  have ht := polyFun_masterHintGet.comp polyFun_masterHintTop
  have hΔ : PolyFun (fun P : RawMasterSI => P.1.1) := polyFun_fst.comp polyFun_fst
  have himg : PolyFun (fun P : RawMasterSI => (masterL57Gens P).map
      (fun g => rawImgOf ((masterHintTop (masterHintGet P)).1, g))) :=
    ((pfst ht).pair polyFun_masterL57Gens).comp (PolyFun.mapParam polyFun_rawImgOf)
  exact ((hΔ.comp polyFun_rangeLength).pair polyFun_masterL57Gens).pair
    (((pfst (psnd (pfst ht))).comp polyFun_rangeLength).pair himg)

end Poly

end Algo
