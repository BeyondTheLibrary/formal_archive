/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the loop of `Workspace/Algo/AlignDescentLoop.lean` walks the tree of
Eq. (71) with the strong descent to `ker ϕ*` on the dominant window (§14.1, lines 7–11,
case 1 of the repair), call for call.
-/
import Workspace.Algo.AlignDescentLoop
import Workspace.Algo.PhaseUnion
import Workspace.Master.CosetForms

/-!
# The link for case 1 of the repair

`Algo.phaseMatch_adVersions`: any round whose child and combine are `Algo.adChild` and
`Algo.adCombine` (read through a projection of its state) walks the tree

`⋃_Y (if C_Y = ∅ then ∅ else (strongDescent N x y L_Y KO).bind (Chain Rule over TW))`

call for call, where `C_Y` is the transporter of the version `Y`, `N` the group of
`Algo.adKG`, `KO` its orbits in the dominant window, `TW` the other color classes, and `L_Y`
the cosets of `N` the machine lists for `C_Y` (`Algo.adReps` at the lexicographically least
element of `C_Y`).

The descent phase is `Algo.aggrPhaseMatch_strongDescent`; each of its chains and the chain over
the other classes are `Algo.phaseMatch_cosetChain`. The machine keeps the hull of the answers
of the cosets of `N`; at the end of the descent that hull is the union itself, because the
union is `Iso` on the dominant window inside `C_Y`, which is empty or a coset
(`Babai.wIso_smul_eq_empty_or_smul_coe`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The search for coset representatives starts from the identity, so it lists at least one. -/
theorem adRN_pos (h : AVHdr) : 0 < adRN h := by
  unfold adRN adRightReps
  rw [rawCosetReps_eq]
  have key : ∀ (c : CosetParam) (l : List ℕ) (start : RawGens), 0 < start.length →
      0 < (List.foldl (fun reps (_ : ℕ) => cosetRound (c, reps)) start l).length := by
    intro c l
    induction l with
    | nil => intro start h; exact h
    | cons a s ih =>
      intro start hs
      refine ih _ ?_
      obtain ⟨e, he⟩ := cosetFold_append c (cosetCands (start, c.1.2)) start
      show 0 < (List.foldl (fun acc cand => cosetAdd (c, (acc, cand))) start
        (cosetCands (start, c.1.2))).length
      rw [he, List.length_append]
      omega
  exact key _ _ _ (by simp)

theorem length_adReps_canon (h : AVHdr) (k : ℕ) :
    (adReps ((h.1, h.2.1), adCanon (h, k))).length = adRN h :=
  length_adReps _

theorem adSegLen_lt {h : AVHdr} {r : ℕ} (hr : r < adRN h) : adSegLen (h, r) = (adKO h).length := by
  rw [adSegLen, if_pos hr]

theorem adSegLen_ge {h : AVHdr} {r : ℕ} (hr : adRN h ≤ r) :
    adSegLen (h, r) = (adTW h).length := by
  rw [adSegLen, if_neg (Nat.not_lt.2 hr)]

theorem adSegWin_lt {h : AVHdr} {r w : ℕ} (hr : r < adRN h) :
    adSegWin (h, r, w) = (adKO h).getD w [] := by
  rw [adSegWin, if_pos hr]

theorem adSegWin_ge {h : AVHdr} {r w : ℕ} (hr : adRN h ≤ r) :
    adSegWin (h, r, w) = (adTW h).getD w [] := by
  rw [adSegWin, if_neg (Nat.not_lt.2 hr)]

section Phase

variable {ι ω : Type*} {n m : ℕ} {R : Round ι ω RawCoset} {decI : ι → SIInstance (Fin n) ℕ}
  {I : ι} {h : AVHdr} {pr : ω → ADState} {emb : RawWinSI → ι} {Good : ℕ → ω → Prop}
  {ϕ : decGroup n h.1.1.2 →* Perm (Fin m)}
  [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
  {X : Pt (SplitOutcomes (Fin m))} {Ys : List (Pt (SplitOutcomes (Fin m)))}

/-- The cosets of `ker ϕ*` the machine lists for the version with index `k`. -/
noncomputable def adLk (n : ℕ) (h : AVHdr) (k : ℕ) : List (Perm (Fin n)) :=
  (adReps ((h.1, h.2.1), adCanon (h, k))).map (decPerm n)

/-- The coset `r` of `ker ϕ*` for the version `k`, decoded. -/
theorem decCoset_adBegin {k r : ℕ} (hr : r < adRN h) :
    decCoset n (adBegin (h, k, r)) =
      (adLk n h k)[r]'(by rw [adLk, List.length_map, length_adReps_canon]; exact hr) •
        (decGroup n (adKG h) : Set (Perm (Fin n))) := by
  have hr' : r < (adReps ((h.1, h.2.1), adCanon (h, k))).length := by
    rw [length_adReps_canon]; exact hr
  rw [adBegin, decCoset_some, List.getD_eq_getElem _ _ hr']
  simp [adLk]

/-- The branch of the Master side for one version. -/
noncomputable def adBranch (N : Subgroup (Perm (Fin n))) (x y : Fin n → ℕ)
    (KOs TWs : List (Set (Fin n))) (C : Set (Perm (Fin n))) (L : List (Perm (Fin n))) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if C = ∅ then .done ∅
  else (strongDescent N x y L KOs).bind (fun a => Babai.cosetChain x y TWs a)

variable (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
    decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
  (hchild : ∀ j s J, Good j s → adChild (h, pr s) = some J → R.child (I, j, s) = some (emb J))
  (hcomb : ∀ j s a J, Good j s → adChild (h, pr s) = some J →
    pr (R.combine (I, j, s, a)) = adCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
  (hA : RawAction.WF n m h.1 ϕ) (hgiant : IsGiantRep ϕ)
  (hK : IsCatAction (SplitOutcomes (Fin m))) (hX : decAlignOutcome m h.2.1 = some X)
  (hYs : h.2.2.1.map (decAlignOutcome m) = Ys.map some)
  (hx : h.2.2.2.2.1.length = n)
  (hNle : decGroup n (adKG h) ≤ preimageSubgroup ϕ (structAut X))
  (hKOne : adKO h ≠ [])
  (hKOlt : ∀ W ∈ adKO h, ∀ u ∈ W, u < n)
  (hKOinv : ∀ W ∈ adKO h, IsInvariant (decGroup n (adKG h)) (winSet n W))
  (hUinv : IsInvariant (preimageSubgroup ϕ (structAut X))
    (⋃ W ∈ (adKO h).map (winSet n), W))
  (hTWlt : ∀ W ∈ adTW h, ∀ u ∈ W, u < n)
  (hTWinv : ∀ W ∈ adTW h, IsInvariant (preimageSubgroup ϕ (structAut X)) (winSet n W))
  (hcover : ∀ k (hk : k < Ys.length), alignTransporter ϕ X Ys[k] ≠ ∅ →
    alignTransporter ϕ X Ys[k] =
      ⋃ σ ∈ adLk n h k, σ • (decGroup n (adKG h) : Set (Perm (Fin n))))
include hdec hchild hcomb hA hgiant hK hX hYs hx hNle hKOne hKOlt hKOinv hUinv hTWlt hTWinv
  hcover

/-- The chain of one coset `σ N` of the version `k` over the orbits of `N`: from the state
opening the coset `i`, to the state opening the coset `i + 1`, with the hull of the answers
grown by the answer of this chain. -/
theorem phaseMatch_adRep {k : ℕ} (hk : k < Ys.length) (i : ℕ) (hi : i < adRN h)
    (A : Set (Perm (Fin n))) (accRaw : RawCoset) (rb ab : RawCoset)
    (hrb : decCoset n rb = cosetHull A) (hab : decCoset n ab = decCoset n accRaw)
    (j : ℕ) (s : ω) (hs : pr s = adOpen (h, k, i, rb, ab)) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (adKO h).length j s
      (Babai.cosetChain (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)
        ((adKO h).map (winSet n))
        ((adLk n h k)[i]'(by rw [adLk, List.length_map, length_adReps_canon]; exact hi) •
          (decGroup n (adKG h) : Set (Perm (Fin n)))))
      (fun B j' s' => Good j' s' ∧ ∃ rb' ab', decCoset n rb' = cosetHull (A ∪ B) ∧
        decCoset n ab' = decCoset n accRaw ∧ pr s' = adOpen (h, k, i + 1, rb', ab')) := by
  set KO := adKO h with hKOdef
  set x := h.2.2.2.2.1 with hxdef
  set y := h.2.2.2.2.2 with hydef
  set N := decGroup n (adKG h) with hNdef
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  have hkL : min k h.2.2.1.length = k := min_eq_left (by omega)
  set Inv : List (Set (Fin n)) → Set (Perm (Fin n)) → ℕ → ω → Prop := fun Δs C j s =>
    Good j s ∧
    (C = ∅ → ∃ rb' ab', decCoset n rb' = cosetHull A ∧ decCoset n ab' = decCoset n accRaw ∧
      pr s = adOpen (h, k, i + 1, rb', ab')) ∧
    (C ≠ ∅ → Δs = [] → ∃ a rb' ab', decCoset n a = C ∧ decCoset n rb' = cosetHull A ∧
      decCoset n ab' = decCoset n accRaw ∧
      pr s = adOpen (h, k, i + 1, rawCosetNorm (x, rawCosetJoin (x, rb', a)), ab')) ∧
    (C ≠ ∅ → Δs ≠ [] → ∃ w g τ rb' ab', Δs = (KO.drop w).map (winSet n) ∧
      pr s = ((k, w, some (g, τ), ab'), (i, rb')) ∧ decCoset n (some (g, τ)) = C ∧
      decGroup n g ≤ N ∧ decCoset n rb' = cosetHull A ∧ decCoset n ab' = decCoset n accRaw)
    with hInv
  have hmain := phaseMatch_cosetChain (R := R) (decI := decI) (decA := decCoset n) (I := I)
    (decStrN n x) (decStrN n y) Inv ?step ?stop
  case step =>
    rintro Δ Δs C j s ⟨hgood, -, -, h3⟩ hCne
    obtain ⟨w, g, τ, rb', ab', hdrop, hsw, hC, hg, hrb', hab'⟩ :=
      h3 hCne (List.cons_ne_nil _ _)
    have hw : w < KO.length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at hdrop
      exact absurd hdrop (List.cons_ne_nil _ _)
    rw [List.drop_eq_getElem_cons hw, List.map_cons] at hdrop
    obtain ⟨hΔ, hΔs⟩ := List.cons.inj hdrop
    have hgetD : KO.getD w [] = KO[w] := List.getD_eq_getElem _ _ hw
    have hmemw : KO[w] ∈ KO := List.getElem_mem hw
    have hltw : ∀ u ∈ KO.getD w [], u < n := by rw [hgetD]; exact hKOlt _ hmemw
    have htidy : decGroup n (tidyGens (x, g)) = decGroup n g := decGroup_tidyGens hx g
    have hinvw : rawIsInvariant (tidyGens (x, g), KO.getD w []) = true := by
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g) hltw, htidy]
      have := hKOinv _ hmemw
      rw [← hgetD] at this
      exact isInvariant_of_le this hg
    set J : RawWinSI := (KO.getD w [], tidyGens (x, g), normPerm (x, τ), x, y) with hJ
    have hav : adChild (h, pr s) = some J := by
      rw [hsw]
      unfold adChild
      simp only [Option.bind_some]
      rw [adSegLen_lt hi, adSegWin_lt hi, if_pos ⟨hw, hinvw⟩]
    have hdecJ : decI (emb J) = ⟨C, Δ, decStrN n x, decStrN n y⟩ := by
      rw [hJ, hdec]
      have hK' : decCoset n (some (tidyGens (x, g), normPerm (x, τ))) = C := by
        rw [← hC]
        show {ρ | ∃ u ∈ decGroup n (tidyGens (x, g)), ρ = decPerm n (normPerm (x, τ)) * u} = _
        rw [htidy, decPerm_normPerm hx τ]
        rfl
      simp only [decWinSI]
      rw [hK', hgetD, hΔ]
    refine ⟨emb J, hchild _ _ _ hgood hav, hdecJ, fun a ha => ?_⟩
    have hsub : (decI (emb J)).answer ⊆ C := by
      rw [hdecJ]; exact fun ρ hρ => hρ.1
    rw [hInv]
    beta_reduce
    obtain ⟨hcomb1, hgood'⟩ := hcomb j s a J hgood hav
    refine ⟨hgood', ?_⟩
    rw [hcomb1, hsw]
    rcases a with _ | ⟨g', τ'⟩
    · have hempty : (decI (emb J)).answer = ∅ := by rw [← ha]; rfl
      rw [hempty]
      refine ⟨fun _ => ?_, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
      refine ⟨rawCosetNorm (x, rb'), rawCosetNorm (x, ab'), by rw [decCoset_rawCosetNorm hx, hrb'],
        by rw [decCoset_rawCosetNorm hx, hab'], ?_⟩
      show adCombine (h, ((k, w, some (g, τ), ab'), (i, rb')), none) = _
      unfold adCombine
      simp only [Option.elim]
      rw [if_pos hi, hkL]
    · have hne : (decI (emb J)).answer ≠ ∅ := by
        rw [← ha]; exact decCoset_some_ne_empty g' τ'
      have hg' : decGroup n g' ≤ N := by
        refine le_trans (decGroup_le_of_subset (σ₀ := decPerm n τ) (τ := decPerm n τ') ?_) hg
        have h1 : decCoset n (some (g', τ')) ⊆ decCoset n (some (g, τ)) := by
          rw [ha, hC]; exact hsub
        exact h1
      refine ⟨fun he => absurd he hne, ?_, ?_⟩
      · intro _ hnil
        have hge : KO.length ≤ w + 1 := by
          by_contra hcon
          have hne' : (KO.drop (w + 1)).map (winSet n) ≠ [] := by
            simp only [ne_eq, List.map_eq_nil_iff, List.drop_eq_nil_iff]
            omega
          exact hne' (hΔs ▸ hnil)
        refine ⟨some (g', τ'), rb', rawCosetNorm (x, ab'), ha, hrb',
          by rw [decCoset_rawCosetNorm hx, hab'], ?_⟩
        show adCombine (h, ((k, w, some (g, τ), ab'), (i, rb')), some (g', τ')) = _
        unfold adCombine
        simp only [Option.elim]
        rw [adSegLen_lt hi, if_neg (Nat.not_lt.2 hge), if_pos hi, hkL]
      · intro _ hnil
        have hlt' : w + 1 < KO.length := by
          by_contra hcon
          rw [hΔs, List.drop_eq_nil_of_le (by omega), List.map_nil] at hnil
          exact hnil rfl
        refine ⟨w + 1, tidyGens (x, g'), normPerm (x, τ'), rawCosetNorm (x, rb'),
          rawCosetNorm (x, ab'), hΔs, ?_, ?_, by rw [decGroup_tidyGens hx]; exact hg',
          by rw [decCoset_rawCosetNorm hx, hrb'], by rw [decCoset_rawCosetNorm hx, hab']⟩
        · show adCombine (h, ((k, w, some (g, τ), ab'), (i, rb')), some (g', τ')) = _
          unfold adCombine
          simp only [Option.elim]
          rw [adSegLen_lt hi, if_pos hlt', hkL, Nat.min_eq_left (by omega)]
          rfl
        · have := decCoset_rawCosetNorm hx (some (g', τ'))
          rw [ha] at this
          exact this
  case stop =>
    rintro Δs C j s ⟨hgood, h1, -, -⟩ hCe
    rw [hInv]
    beta_reduce
    exact ⟨hgood, fun _ => h1 hCe, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
  -- the start
  have hilt : i < (adLk n h k).length := by
    rw [adLk, List.length_map, length_adReps_canon]; exact hi
  have h0 : Inv (KO.map (winSet n)) ((adLk n h k)[i] • (N : Set (Perm (Fin n)))) j s := by
    have hne : (adLk n h k)[i] • (N : Set (Perm (Fin n))) ≠ ∅ := by
      rw [← decCoset_adBegin (h := h) (k := k) hi]
      unfold adBegin
      exact decCoset_some_ne_empty _ _
    refine ⟨hgs, fun he => absurd he hne,
      fun _ hnil => absurd hnil (by simpa using hKOne), fun _ _ => ?_⟩
    refine ⟨0, adKG h, (adReps ((h.1, h.2.1), adCanon (h, k))).getD i [], rb, ab,
      by rw [List.drop_zero], ?_, ?_, le_rfl, hrb, hab⟩
    · rw [hs, adOpen_lt rb ab hi]
      rfl
    · exact decCoset_adBegin hi
  have hrun := hmain (KO.map (winSet n)) _ j s h0
  rw [List.length_map] at hrun
  rw [← aggrCosetChain_eq]
  refine phaseMatch_weaken hrun ?_
  rintro B j' s' ⟨hgood, h1, h2, -⟩
  by_cases hB : B = ∅
  · obtain ⟨rb', ab', hrb', hab', hpos⟩ := h1 hB
    refine ⟨hgood, rb', ab', ?_, hab', hpos⟩
    rw [hrb', hB, Set.union_empty]
  · obtain ⟨a, rb', ab', ha, hrb', hab', hpos⟩ := h2 hB rfl
    refine ⟨hgood, rawCosetNorm (x, rawCosetJoin (x, rb', a)), ab', ?_, hab', hpos⟩
    rw [decCoset_rawCosetNorm hx, decCoset_rawCosetJoin hx, hrb', ha, cosetHull_hull_union]

set_option maxHeartbeats 1600000 in
/-- One version: the strong descent to `N` on the dominant window, then the Chain Rule over
the other classes, from the state `adPos (h, k, accRaw)` to `adPos (h, k + 1, a)`, with the
gathered answer grown by the piece of this version. -/
theorem phaseMatch_adVersion (Lf : Pt (SplitOutcomes (Fin m)) → List (Perm (Fin n)))
    (hLf : ∀ k (hk : k < Ys.length), alignTransporter ϕ X Ys[k] ≠ ∅ → Lf Ys[k] = adLk n h k)
    {k : ℕ} (hk : k < Ys.length) (acc : Set (Perm (Fin n)))
    (accRaw : RawCoset) (hacc : decCoset n accRaw = cosetHull acc) (j : ℕ) (s : ω)
    (hs : pr s = adPos (h, k, accRaw)) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (adRN h * (adKO h).length + (adTW h).length) j s
      (adBranch (decGroup n (adKG h)) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)
        ((adKO h).map (winSet n)) ((adTW h).map (winSet n)) (alignTransporter ϕ X Ys[k])
        (Lf Ys[k]))
      (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = adPos (h, k + 1, a) ∧
        decCoset n a = cosetHull (acc ∪ S)) := by
  set x := h.2.2.2.2.1 with hxdef
  set y := h.2.2.2.2.2 with hydef
  set N := decGroup n (adKG h) with hNdef
  set G₁ := preimageSubgroup ϕ (structAut X) with hG₁
  set TW := adTW h with hTWdef
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  have hk' : k < h.2.2.1.length := by omega
  have hkL : min k h.2.2.1.length = k := min_eq_left (by omega)
  have htr := decCoset_avTr hA hgiant hK hX hYs hx hk
  set C := alignTransporter ϕ X Ys[k] with hCdef
  unfold adBranch
  by_cases hC : C = ∅
  · rw [if_pos hC]
    have hnone : avTr (h, k) = none := by
      rcases ht : avTr (h, k) with _ | ⟨g, τ⟩
      · rfl
      · exfalso
        have h1 := htr
        rw [ht] at h1
        exact decCoset_some_ne_empty g τ (h1.trans hC)
    exact phaseMatch_mono (phaseMatch_done ⟨hgs, accRaw, by rw [hs, adPos_skip accRaw hnone],
      by rw [hacc, Set.union_empty]⟩) (Nat.zero_le _)
  rw [if_neg hC, hLf k hk hC]
  have hsome : (avTr (h, k)).isSome := by
    rcases ht : avTr (h, k) with _ | ⟨g, τ⟩
    · exfalso; rw [ht] at htr; exact hC htr.symm
    · rfl
  obtain ⟨τ0, hτ0⟩ := Set.nonempty_iff_ne_empty.2 hC
  have hCeq : C = τ0 • (G₁ : Set (Perm (Fin n))) :=
    alignTransporter_eq_smul ϕ X Ys[k] ⟨τ0, hτ0.1⟩ hτ0.2
  set L := adLk n h k with hLdef
  have hLlen : L.length = adRN h := by rw [hLdef, adLk, List.length_map, length_adReps_canon]
  -- the descent
  set Inv : List (Perm (Fin n)) → Set (Perm (Fin n)) → ℕ → ω → Prop := fun σs A j s =>
    Good j s ∧ σs.length ≤ L.length ∧ σs = L.drop (L.length - σs.length) ∧
      ∃ rb ab, decCoset n rb = cosetHull A ∧ decCoset n ab = decCoset n accRaw ∧
        pr s = adOpen (h, k, L.length - σs.length, rb, ab) with hInv
  have hs0 : pr s = adOpen (h, k, 0, none, rawCosetNorm (x, accRaw)) := by
    rw [hs, adPos_self accRaw hk' hsome hKOne, adOpen_lt none _ (adRN_pos h)]
  have hD := aggrPhaseMatch_strongDescent (R := R) (decI := decI) (decA := decCoset n) (I := I)
    N (decStrN n x) (decStrN n y) L ((adKO h).map (winSet n)) Inv ?hstep j s
    ⟨hgs, le_rfl, by rw [Nat.sub_self, List.drop_zero], none, rawCosetNorm (x, accRaw),
      by rw [cosetHull_empty]; rfl, decCoset_rawCosetNorm hx accRaw,
      by rw [Nat.sub_self]; exact hs0⟩
  case hstep =>
    rintro σ σs A j s ⟨hgood, hle, hdrop, rb, ab, hrb, hab, hps⟩
    have hle' : σs.length + 1 ≤ L.length := by simpa using hle
    set i := L.length - (σs.length + 1) with hidef
    have hi : i < L.length := by omega
    have hdi : σ :: σs = L.drop i := by simpa using hdrop
    rw [List.drop_eq_getElem_cons hi] at hdi
    obtain ⟨hσ, hσs⟩ := List.cons.inj hdi
    have hir : i < adRN h := hLlen ▸ hi
    have hrep := phaseMatch_adRep hdec hchild hcomb hA hgiant hK hX hYs hx hNle hKOne hKOlt
      hKOinv hUinv hTWlt hTWinv hcover hk i hir A accRaw rb ab hrb hab j s
      (by simpa using hps) hgood
    rw [List.length_map, hσ]
    refine phaseMatch_weaken hrep ?_
    rintro B j' s' ⟨hg', rb', ab', hrb', hab', hpos⟩
    have hi1 : L.length - σs.length = i + 1 := by omega
    refine ⟨hg', by omega, by rw [hi1]; exact hσs, rb', ab', hrb', hab', by rw [hi1]; exact hpos⟩
  have hD' := aggrPhaseMatch_value hD
  have hcost : adRN h * (adKO h).length + TW.length =
      L.length * ((adKO h).map (winSet n)).length + (TW.map (winSet n)).length := by
    rw [hLlen, List.length_map, List.length_map]
  rw [hcost]
  refine phaseMatch_bind hD' ?_
  rintro U j' s' ⟨⟨hg', -, -, rb, ab, hrb, hab, hps⟩, hU⟩
  have hps' : pr s' = adAfter (h, k, rb, ab) := by
    rw [hps, List.length_nil, Nat.sub_zero, adOpen_ge rb ab (by rw [hLlen])]
  -- the union of the descent is its own hull
  have hUrun : U = wIso (⋃ Δ ∈ (adKO h).map (winSet n), Δ) C (decStrN n x) (decStrN n y) := by
    rw [hU, run_strongDescent, ← hcover k hk hC]
  have hUc : cosetHull U = U := by
    rcases wIso_smul_eq_empty_or_smul_coe (G := ⊤) (N := G₁) (M := G₁) le_top le_rfl hUinv
      (decStrN n x) (decStrN n y) (σ := τ0) (Subgroup.mem_top _) with he | ⟨M', ρ, -, -, he⟩
    · rw [hUrun, hCeq, he, cosetHull_empty]
    · rw [hUrun, hCeq, he, cosetHull_smul_subgroup]
  have hrbU : decCoset n rb = U := hrb.trans hUc
  by_cases hT : TW = []
  · have hA' : adAfter (h, k, rb, ab) = adPos (h, k + 1, rawCosetJoin (x, ab, rb)) := by
      rw [adAfter, if_pos (by rw [← hTWdef, hT]; rfl)]
    rw [hT, List.map_nil, List.length_nil]
    exact phaseMatch_done ⟨hg', _, by rw [hps', hA'], by
      rw [decCoset_rawCosetJoin hx, hab, hacc, hrbU, cosetHull_hull_union]⟩
  by_cases hU0 : U = ∅
  · have hrbn : rb = none := by
      rcases rb with _ | ⟨g0, τ1⟩
      · rfl
      · exact absurd (hrbU.trans hU0) (decCoset_some_ne_empty g0 τ1)
    have hA' : adAfter (h, k, rb, ab) = adPos (h, k + 1, ab) := by
      rw [adAfter, if_neg (by rw [← hTWdef]; simpa using hT), hrbn]
      rfl
    rw [hU0, babaiCosetChain_empty]
    exact phaseMatch_mono (phaseMatch_done ⟨hg', ab, by rw [hps', hA'],
      by rw [hab, hacc, Set.union_empty]⟩) (Nat.zero_le _)
  obtain ⟨g0, τ1, hrbs⟩ : ∃ g0 τ1, rb = some (g0, τ1) := by
    rcases rb with _ | ⟨g0, τ1⟩
    · exact absurd (hrbU.symm.trans rfl) hU0
    · exact ⟨g0, τ1, rfl⟩
  have hA' : adAfter (h, k, rb, ab) =
      ((k, 0, some (tidyGens (x, g0), normPerm (x, τ1)), ab), (adRN h, none)) := by
    rw [adAfter, if_neg (by rw [← hTWdef]; simpa using hT), hrbs]
    rfl
  -- the chain over the other classes
  set Inv2 : List (Set (Fin n)) → Set (Perm (Fin n)) → ℕ → ω → Prop := fun Δs C j s =>
    Good j s ∧ (C = ∅ → ∃ b, decCoset n b = decCoset n accRaw ∧ pr s = adPos (h, k + 1, b)) ∧
    (C ≠ ∅ → Δs = [] → ∃ a b, decCoset n a = C ∧ decCoset n b = decCoset n accRaw ∧
      pr s = adPos (h, k + 1, rawCosetJoin (x, b, a))) ∧
    (C ≠ ∅ → Δs ≠ [] → ∃ w g τ b q, Δs = (TW.drop w).map (winSet n) ∧
      pr s = ((k, w, some (g, τ), b), (adRN h, q)) ∧ decCoset n (some (g, τ)) = C ∧
      decGroup n g ≤ G₁ ∧ decCoset n b = decCoset n accRaw)
    with hInv2
  have hmain := phaseMatch_cosetChain (R := R) (decI := decI) (decA := decCoset n) (I := I)
    (decStrN n x) (decStrN n y) Inv2 ?step2 ?stop2
  case step2 =>
    rintro Δ Δs C j s ⟨hgood, -, -, h3⟩ hCne
    obtain ⟨w, g, τ, b, q, hdrop, hsw, hC', hg, hb⟩ := h3 hCne (List.cons_ne_nil _ _)
    have hw : w < TW.length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at hdrop
      exact absurd hdrop (List.cons_ne_nil _ _)
    rw [List.drop_eq_getElem_cons hw, List.map_cons] at hdrop
    obtain ⟨hΔ, hΔs⟩ := List.cons.inj hdrop
    have hgetD : TW.getD w [] = TW[w] := List.getD_eq_getElem _ _ hw
    have hmemw : TW[w] ∈ TW := List.getElem_mem hw
    have hltw : ∀ u ∈ TW.getD w [], u < n := by rw [hgetD]; exact hTWlt _ hmemw
    have htidy : decGroup n (tidyGens (x, g)) = decGroup n g := decGroup_tidyGens hx g
    have hinvw : rawIsInvariant (tidyGens (x, g), TW.getD w []) = true := by
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g) hltw, htidy]
      have := hTWinv _ hmemw
      rw [← hgetD] at this
      exact isInvariant_of_le this hg
    set J : RawWinSI := (TW.getD w [], tidyGens (x, g), normPerm (x, τ), x, y) with hJ
    have hav : adChild (h, pr s) = some J := by
      rw [hsw]
      unfold adChild
      simp only [Option.bind_some]
      rw [adSegLen_ge le_rfl, adSegWin_ge le_rfl, if_pos ⟨hw, hinvw⟩]
    have hdecJ : decI (emb J) = ⟨C, Δ, decStrN n x, decStrN n y⟩ := by
      rw [hJ, hdec]
      have hK' : decCoset n (some (tidyGens (x, g), normPerm (x, τ))) = C := by
        rw [← hC']
        show {ρ | ∃ u ∈ decGroup n (tidyGens (x, g)), ρ = decPerm n (normPerm (x, τ)) * u} = _
        rw [htidy, decPerm_normPerm hx τ]
        rfl
      simp only [decWinSI]
      rw [hK', hgetD, hΔ]
    refine ⟨emb J, hchild _ _ _ hgood hav, hdecJ, fun a ha => ?_⟩
    have hsub : (decI (emb J)).answer ⊆ C := by
      rw [hdecJ]; exact fun ρ hρ => hρ.1
    rw [hInv2]
    beta_reduce
    obtain ⟨hcomb1, hgood'⟩ := hcomb j s a J hgood hav
    refine ⟨hgood', ?_⟩
    rw [hcomb1, hsw]
    have hnlt : ¬ adRN h < adRN h := lt_irrefl _
    rcases a with _ | ⟨g', τ'⟩
    · have hempty : (decI (emb J)).answer = ∅ := by rw [← ha]; rfl
      rw [hempty]
      refine ⟨fun _ => ⟨b, hb, ?_⟩, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
      show adCombine (h, ((k, w, some (g, τ), b), (adRN h, q)), none) = _
      unfold adCombine
      simp only [Option.elim]
      rw [if_neg hnlt, hkL]
    · have hne : (decI (emb J)).answer ≠ ∅ := by
        rw [← ha]; exact decCoset_some_ne_empty g' τ'
      have hg' : decGroup n g' ≤ G₁ := by
        refine le_trans (decGroup_le_of_subset (σ₀ := decPerm n τ) (τ := decPerm n τ') ?_) hg
        have h1 : decCoset n (some (g', τ')) ⊆ decCoset n (some (g, τ)) := by
          rw [ha, hC']; exact hsub
        exact h1
      refine ⟨fun he => absurd he hne, ?_, ?_⟩
      · intro _ hnil
        have hge : TW.length ≤ w + 1 := by
          by_contra hcon
          have hne' : (TW.drop (w + 1)).map (winSet n) ≠ [] := by
            simp only [ne_eq, List.map_eq_nil_iff, List.drop_eq_nil_iff]
            omega
          exact hne' (hΔs ▸ hnil)
        refine ⟨some (g', τ'), b, ha, hb, ?_⟩
        show adCombine (h, ((k, w, some (g, τ), b), (adRN h, q)), some (g', τ')) = _
        unfold adCombine
        simp only [Option.elim]
        rw [adSegLen_ge le_rfl, if_neg (Nat.not_lt.2 hge), if_neg hnlt, hkL]
      · intro _ hnil
        have hlt' : w + 1 < TW.length := by
          by_contra hcon
          rw [hΔs, List.drop_eq_nil_of_le (by omega), List.map_nil] at hnil
          exact hnil rfl
        refine ⟨w + 1, tidyGens (x, g'), normPerm (x, τ'), rawCosetNorm (x, b),
          rawCosetNorm (x, q), hΔs, ?_, ?_, by rw [decGroup_tidyGens hx]; exact hg',
          by rw [decCoset_rawCosetNorm hx, hb]⟩
        · show adCombine (h, ((k, w, some (g, τ), b), (adRN h, q)), some (g', τ')) = _
          unfold adCombine
          simp only [Option.elim]
          rw [adSegLen_ge le_rfl, if_pos hlt', hkL, Nat.min_self]
          rfl
        · have := decCoset_rawCosetNorm hx (some (g', τ'))
          rw [ha] at this
          exact this
  case stop2 =>
    rintro Δs C j s ⟨hgood, h1, -, -⟩ hCe
    rw [hInv2]
    beta_reduce
    exact ⟨hgood, fun _ => h1 hCe, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
  have hTne : TW.map (winSet n) ≠ [] := by simpa using hT
  have hU' : decCoset n (some (tidyGens (x, g0), normPerm (x, τ1))) = U := by
    rw [← hrbU, hrbs]
    show {ρ | ∃ u ∈ decGroup n (tidyGens (x, g0)), ρ = decPerm n (normPerm (x, τ1)) * u} = _
    rw [decGroup_tidyGens hx, decPerm_normPerm hx τ1]
    rfl
  have hUsub : U ⊆ C := by
    rw [hUrun]; exact fun ρ hρ => hρ.1
  have hgU : decGroup n (tidyGens (x, g0)) ≤ G₁ := by
    refine decGroup_le_of_subset (σ₀ := τ0) (τ := decPerm n (normPerm (x, τ1))) ?_
    have h1 : decCoset n (some (tidyGens (x, g0), normPerm (x, τ1))) ⊆
        τ0 • (G₁ : Set (Perm (Fin n))) := by
      rw [hU', ← hCeq]; exact hUsub
    rw [smul_subgroup_eq_setOf] at h1
    exact h1
  have h0 : Inv2 (TW.map (winSet n)) U j' s' :=
    ⟨hg', fun he => absurd he hU0, fun _ hnil => absurd hnil hTne, fun _ _ =>
      ⟨0, tidyGens (x, g0), normPerm (x, τ1), ab, none, by rw [List.drop_zero],
        by rw [hps', hA'], hU', hgU, hab⟩⟩
  have hrun := hmain (TW.map (winSet n)) U j' s' h0
  rw [← aggrCosetChain_eq]
  refine phaseMatch_weaken hrun ?_
  rintro S j'' s'' ⟨hgood, h1, h2, -⟩
  by_cases hS : S = ∅
  · obtain ⟨b, hb, hpos⟩ := h1 hS
    exact ⟨hgood, b, hpos, by rw [hb, hacc, hS, Set.union_empty]⟩
  · obtain ⟨a, b, ha, hb, hpos⟩ := h2 hS rfl
    exact ⟨hgood, rawCosetJoin (x, b, a), hpos, by
      rw [decCoset_rawCosetJoin hx, hb, hacc, ha, cosetHull_hull_union]⟩

/-- The versions from index `k` on, from the state `adPos (h, k, accRaw)`. -/
theorem phaseMatch_adVersions_from (Lf : Pt (SplitOutcomes (Fin m)) → List (Perm (Fin n)))
    (hLf : ∀ k (hk : k < Ys.length), alignTransporter ϕ X Ys[k] ≠ ∅ → Lf Ys[k] = adLk n h k) :
    ∀ (rest : List (Pt (SplitOutcomes (Fin m)))) (k : ℕ), Ys.drop k = rest →
      ∀ (acc : Set (Perm (Fin n))) (accRaw : RawCoset), decCoset n accRaw = cosetHull acc →
      ∀ (j : ℕ) (s : ω), pr s = adPos (h, k, accRaw) → Good j s →
      PhaseMatch R decI (decCoset n) I
        (rest.length * (adRN h * (adKO h).length + (adTW h).length)) j s
        (SIReduction.unionOver rest fun Y =>
          adBranch (decGroup n (adKG h)) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)
            ((adKO h).map (winSet n)) ((adTW h).map (winSet n)) (alignTransporter ϕ X Y)
            (Lf Y))
        (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = ((h.2.2.1.length, 0, none, a), (0, none)) ∧
          decCoset n a = cosetHull (acc ∪ S)) := by
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  intro rest
  induction rest with
  | nil =>
    intro k hk acc accRaw hacc j s hs hgs
    have hle : Ys.length ≤ k := List.drop_eq_nil_iff.1 hk
    rw [SIReduction.unionOver, List.length_nil, Nat.zero_mul]
    refine phaseMatch_done ?_
    exact ⟨hgs, rawCosetNorm (h.2.2.2.2.1, accRaw), by rw [hs, adPos_end accRaw (by omega)],
      by rw [decCoset_rawCosetNorm hx, hacc, Set.union_empty]⟩
  | cons Y rest ih =>
    intro k hk acc accRaw hacc j s hs hgs
    have hkl : k < Ys.length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega)] at hk
      exact List.cons_ne_nil _ _ hk.symm
    rw [List.drop_eq_getElem_cons hkl] at hk
    obtain ⟨rfl, hrest⟩ := List.cons.inj hk
    have hc : (Ys[k] :: rest).length * (adRN h * (adKO h).length + (adTW h).length) =
        (adRN h * (adKO h).length + (adTW h).length) +
          (rest.length * (adRN h * (adKO h).length + (adTW h).length) + 0) := by
      rw [List.length_cons, Nat.succ_mul]; omega
    rw [hc, SIReduction.unionOver]
    refine phaseMatch_bind (phaseMatch_adVersion hdec hchild hcomb hA hgiant hK hX hYs hx hNle
      hKOne hKOlt hKOinv hUinv hTWlt hTWinv hcover Lf hLf hkl acc accRaw hacc j s hs hgs) ?_
    rintro S j' s' ⟨hg', a, hpos, ha⟩
    refine phaseMatch_bind (ih (k + 1) hrest (acc ∪ S) a ha j' s' hpos hg') ?_
    rintro S' j'' s'' ⟨hg'', a', hend, ha'⟩
    refine phaseMatch_done ?_
    exact ⟨hg'', a', hend, by rw [ha', Set.union_assoc]⟩

/-- §14.1, lines 7–11, case 1 of the repair, **the link**: a round whose steps
are `adChild` and `adCombine` walks, from the state `adInit h`, the tree that unions over the
versions `Y` the strong descent to `N` on the dominant window followed by the Chain Rule over
the other classes, call for call, with at most `Algo.adCalls h` calls. At the end no version
is left, and the gathered raw answer describes the smallest coset containing the value of the
tree. -/
theorem phaseMatch_adVersions (Lf : Pt (SplitOutcomes (Fin m)) → List (Perm (Fin n)))
    (hLf : ∀ k (hk : k < Ys.length), alignTransporter ϕ X Ys[k] ≠ ∅ → Lf Ys[k] = adLk n h k)
    (j : ℕ) (s : ω) (hs : pr s = adInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (adCalls h) j s
      (SIReduction.unionOver Ys fun Y =>
        adBranch (decGroup n (adKG h)) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)
          ((adKO h).map (winSet n)) ((adTW h).map (winSet n)) (alignTransporter ϕ X Y) (Lf Y))
      (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = ((h.2.2.1.length, 0, none, a), (0, none)) ∧
        decCoset n a = cosetHull S) := by
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  have := phaseMatch_adVersions_from hdec hchild hcomb hA hgiant hK hX hYs hx hNle hKOne hKOlt
    hKOinv hUinv hTWlt hTWinv hcover Lf hLf Ys 0 List.drop_zero ∅ none
    (by rw [cosetHull_empty]; rfl) j s hs hgs
  have hc : adCalls h = Ys.length * (adRN h * (adKO h).length + (adTW h).length) := by
    rw [adCalls, hlen]
  rw [hc]
  refine phaseMatch_weaken this ?_
  rintro S j' s' ⟨hg, a, h1, h2⟩
  exact ⟨hg, a, h1, by rw [h2, Set.empty_union]⟩

end Phase

end Algo
