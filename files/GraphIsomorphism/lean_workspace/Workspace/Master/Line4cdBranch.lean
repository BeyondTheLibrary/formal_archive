/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 4c and 4d: the branch itself.
-/
import Workspace.Master.CosetCore

/-!
# Lines 4c and 4d as a branch of the round

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :)
>     (: view these hypergraphs as `t`-ary relational structures :)
>     apply Extended Design Lemma (Theorem 9.2.3)
> 4d. (: canonical structure `X` on `Γ` found: colored equipartition or Johnson scheme :)
>     apply Procedure Align to `X` (Sec. 14.1)

`Babai.nonempty_line4cdCore` is the branch, on the window type and with everything the
fields of `Babai.Sec15Remaining` ask for (`Babai.Line4cdCore`).  It is built with `α = 3/4`,
the threshold Theorem 9.2.3 is stated for:

1. line 4b has failed, so the relative symmetry defect of `H(x|_Δ)` is at least `1/2`, which
   is `Babai.LargeDefectData` for every `α > 1/2` (`Babai.largeDefectData_of_not_smallDefect`);
2. Theorem 9.2.3 gives a canonical family `Vers` of versions of the structure
   (`Babai.exists_canonicalVersions_of_uniform`), and `X'` is a version of `X(x)`;
3. Procedure Align colors `Γ` by `X'` (`Babai.alignColor`) and `Ω` by the color vectors of
   the labels (`Babai.omegaColorClass`), and `Babai.alignColor_cases` splits line 5 from
   lines 6–7: either every color class of `Γ` has at most `3m/4` vertices, and then every
   color class of `Ω` has at most `2n/3` points (Eq. (72)), or there is a dominant color
   class, and it carries the extra structure of line 7;
4. in the first case the branch is the Chain Rule of line 5 over the color classes
   (`Babai.designAlignReduction`); in the second it is the same Chain Rule with the dominant
   window first (line 6) and the call on that window expanded by the round of lines 7–11
   (`Babai.alignExpandBranch`, `Babai.AlignDominantRoundData.round`), which halves the
   Johnson parameter instead of the window (Eq. (73)).

`Babai.line4cdFun` is the branch read on `Ω` (`Babai.liftWindow`), `Babai.line4cdLift` is the
hint it hands to each of its calls (`Babai.cosetWindowHintLift`), and the five theorems at the end
are the five fields of `Babai.Sec15Remaining` for it.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### The calls of the Chain Rule of line 5, without a dominant window -/

section Aux

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳] {G : Subgroup (Equiv.Perm W)}

open scoped Classical in
/-- §15, lines 4c–4d: every call of the Chain Rule of line 5 has a color class for its
window, is a group instance, and is made with respect to a subgroup of
`G₁ = ϕ⁻¹(Aut(X'))`.  This is `Babai.calls_designAlignReduction_spec` for a list that need
not begin with the dominant window. -/
theorem calls_designAlignReduction_group {ϕ : G →* Equiv.Perm Γ} {Vers : (W → A) → Set 𝒳}
    (x y : W → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set W))
    (hinv : ∀ Δ ∈ Δs, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ) :
    ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' Δs).calls,
      J.Δ ∈ Δs ∧ IsGroupInstance J ∧
        J.K ⊆ ((preimageSubgroup ϕ (structAut X') : Subgroup (Equiv.Perm W)) :
          Set (Equiv.Perm W)) := by
  classical
  refine calls_versionsReduction y hfin _ (fun Y' => ?_)
  refine calls_alignBranch_at (ϕ := ϕ) y X' Y' _ (fun z J hJ => ?_)
  rw [alignChainReduction] at hJ
  obtain ⟨M', hKJ, hle, hΔ⟩ := calls_chainReduction_group
    (preimageSubgroup ϕ (structAut X')) x z Δs 1 (preimageSubgroup ϕ (structAut X')) J hJ
  exact ⟨hΔ, ⟨M', hKJ, fun τ hτ => hinv J.Δ hΔ τ (hle hτ)⟩,
    by rw [hKJ]; exact SetLike.coe_subset_coe.2 hle⟩

end Aux

/-! ### The branch on the window, from the canonical versions -/

section FromVersions

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- The number of color classes of `Ω` is at most the number of points. -/
theorem length_omegaColorClasses_le {m : ℕ} {G : Subgroup (Equiv.Perm W)}
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι) :
    (omegaColorClasses (Ω := W) ϕ c).length ≤ Fintype.card W := by
  classical
  rw [omegaColorClasses, Finset.length_toList]
  exact le_trans (Finset.card_image_le) (le_of_eq (Finset.card_univ))

/-- §15, **lines 4d, 7 and 7a on the window**: Procedure Align (Sec. 14.1) applied to a
canonical family of versions of the structure, with everything the fields of
`Babai.Sec15Remaining` ask for.

This is the part of lines 4c–4d that comes **after** the canonical structure has been
found, so it is shared by line 4d (the structure comes from Theorem 9.2.3 at line 4c),
line 6a–7a (from Theorem 9.2.3 applied at line 6a to the structure Theorem 13.2.1
aggregated) and line 7–7a (the colored equipartition Theorem 13.2.1 returns).  What it
needs of the ambient data is Sec. 14's *"Situation"*: a transitive `G ≤ S(Ω)` with a giant
representation `ϕ : G → S(Γ)`, and the standard blocks `Φ = {B_T : T ∈ Γ^{(t)}}` of
Theorem 10.5.1, all labels of size `t`.

The threshold `α` is the one of the structure: `3/4` for Theorem 9.2.3 (line 4c, line 6a)
and `4/5` for Theorem 13.2.1 (line 7).  The three numeric conditions on it are the ones
Sec. 14.2 uses: `1/2 < α` (line 6's *"dominant color"* is a real dichotomy), `0 ≤ α` and
`5α ≤ 4` — Eq. (72) at the threshold of `Babai.MakesProgress`, through
`Babai.five_mul_card_tupleClass_le_of_le`.

**`1 ≤ t` is enough.**  Lemma 7.2.1 (b) gives `|Ω(Δ)|/n ≤ (|Δ|/m)^t ≤ α^t ≤ α` for every
`t ≥ 1`, so a color class that carries no structure gives a window of at most `αn ≤ 4n/5`
points, which is the window alternative of `Babai.MakesProgress`.  This is what lines 5–7
need, where `t = 1` is not excluded; see the corrected paper entry on Sec. 15 lines 5–7a
and Sec. 14.2 Eqs. (72)–(73).

**The reduction is a function of the data** (`Babai.AlignShape.red`).  The two cases of
line 6 differ only in the field `dom`: when there is no dominant color class the call of
the Chain Rule on the first window stands, and when there is one it is expanded by the
round of lines 7–11.  See the corrected paper entry on Finding 1 of the audit of
Secs. 14–15. -/
theorem nonempty_alignData_of_versions {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m t : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (ht : ∀ u : W, tPoint ϕ u = t) (ht1 : 1 ≤ t)
    (h4t : 4 * t < m) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W) {x y : W → A}
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    {Vers : (W → A) → Set (Pt (SplitOutcomes (Fin m)))}
    (hcan : IsCanonicalVersions ϕ Vers) (hfiny : (Vers y).Finite) {V : ℕ}
    (hqv : (Vers y).ncard ≤ V) {X' : Pt (SplitOutcomes (Fin m))} (hX' : X' ∈ Vers x)
    {α : ℝ} (hα12 : 1 / 2 < α) (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4)
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') :
    Nonempty (Line4cdData W A G x y m
      (V * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W))) := by
  classical
  haveI : Nonempty (AlignIdx X') := nonempty_alignIdx (by omega)
  have hinvcls : ∀ Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X'),
      IsInvariant (preimageSubgroup ϕ (structAut X')) Δ :=
    isInvariant_omegaColorClasses_alignIdx hK ϕ hgiant hvl X'
  have hcov : (⋃ Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X'), Δ) = (Set.univ : Set W) :=
    iUnion_omegaColorClasses ϕ _
  have hlen : (omegaColorClasses (Ω := W) ϕ (alignIdx X')).length ≤ Fintype.card W :=
    length_omegaColorClasses_le ϕ _
  have hG₁G : ((preimageSubgroup ϕ (structAut X') : Subgroup (Equiv.Perm W)) :
      Set (Equiv.Perm W)) ⊆ (G : Set (Equiv.Perm W)) :=
    SetLike.coe_subset_coe.2 (preimageSubgroup_le ϕ _)
  have hcr : 1 ≤ AlignDominantRoundData.alignDominantRoundCost (Fintype.card W) := by
    rw [AlignDominantRoundData.alignDominantRoundCost]
    have : 1 ≤ Fintype.card W := by omega
    omega
  obtain ⟨w₀⟩ : Nonempty W := Fintype.card_pos_iff.1 (by omega)
  rcases alignColor_cases hα12 hZ with hsmall | ⟨i₀, hdom, hstruct⟩
  · -- line 5: no dominant color class, every color class of `Ω` has at most `4n/5` points
    have hsizes : ∀ Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X'),
        5 * Δ.ncard ≤ 4 * Fintype.card W :=
      five_mul_ncard_omegaColorClasses_le hG ϕ hgiant hvl (by omega) ht ht1 (by omega) X'
        (α := α) hα0 hα45 hsmall
    -- the list of color classes is nonempty, so line 6 has a window to start with
    have hnenil : omegaColorClasses (Ω := W) ϕ (alignIdx X') ≠ [] := by
      intro h0
      have hw : w₀ ∈ (⋃ Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X'), Δ) := by
        rw [hcov]; trivial
      rw [h0] at hw
      simp at hw
    obtain ⟨S₀, rest, hlist⟩ := List.exists_cons_of_ne_nil hnenil
    have hnd : (S₀ :: rest).Nodup := by
      rw [← hlist, omegaColorClasses]; exact Finset.nodup_toList _
    have hS₀nr : S₀ ∉ rest := (List.nodup_cons.1 hnd).1
    have hinvlist : ∀ Δ ∈ S₀ :: rest,
        IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
      rw [← hlist]; exact hinvcls
    have hcovlist : (⋃ Δ ∈ S₀ :: rest, Δ) = (Set.univ : Set W) := by
      rw [← hlist]; exact hcov
    have hsizes' : ∀ Δ ∈ S₀ :: rest, 5 * Δ.ncard ≤ 4 * Fintype.card W := by
      rw [← hlist]; exact hsizes
    have hlistlen : (S₀ :: rest).length ≤ Fintype.card W + 1 := by
      rw [← hlist]; omega
    let S : AlignShape W A G x y :=
      { m := m, ϕ := ϕ, act := inst, Vers := Vers, finY := hfiny, X' := X',
        head := S₀, tail := rest, dom := none }
    refine ⟨Line4cdData.ofShape S m V (Fintype.card W + 1)
      (AlignDominantRoundData.alignDominantRoundCost (Fintype.card W))
      (List.Perm.refl _) hS₀nr hcovlist hinvlist
      (fun D hD => by simp [S] at hD) (fun D hD => by simp [S] at hD)
      hcan hX' ?_ hlistlen hcr (fun _ _ => le_rfl) ?_⟩
    · change hfiny.toFinset.toList.length ≤ V
      rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card (Vers y) hfiny]
      exact hqv
    · exact fun Δ hΔ _ => hsizes' Δ hΔ
  · -- lines 6–11: a dominant color class
    obtain ⟨γ₀, hγ₀⟩ : ∃ γ : Fin m, alignColor X' γ = i₀ := by
      have hpos : 0 < (colorSet (alignColor X') i₀).card := by omega
      obtain ⟨γ, hγ⟩ := Finset.card_pos.1 hpos
      exact ⟨γ, by simpa [colorSet] using hγ⟩
    set i₀' : AlignIdx X' := alignIdx X' γ₀ with hi₀'def
    have hi₀c : ((i₀' : AlignIdx X') : AlignColor) = i₀ := hγ₀
    have hcs : colorSet (alignIdx X') i₀' = colorSet (alignColor X') i₀ := by
      rw [colorSet_alignIdx, hi₀c]
    set v₀ : AlignIdx X' → ℕ := fun j => if j = i₀' then t else 0 with hv₀def
    have hv₀i : v₀ i₀' = t := by simp [hv₀def]
    have hv₀j : ∀ j, j ≠ i₀' → v₀ j = 0 := by intro j hj; simp [hv₀def, hj]
    set S₀ : Set W := omegaColorClass ϕ (alignIdx X') v₀ with hS₀def
    have hS₀eq : S₀ = omegaOf ϕ {γ : Fin m | alignIdx X' γ = i₀'} := by
      rw [hS₀def]
      exact omegaColorClass_eq_omegaOf ϕ ht (alignIdx X') i₀' v₀ hv₀i hv₀j
    have hsetcoe : {γ : Fin m | alignIdx X' γ = i₀'}
        = ((colorSet (alignColor X') i₀ : Finset (Fin m)) : Set (Fin m)) := by
      rw [← hcs]; ext γ; simp [colorSet]
    obtain ⟨D, hDm, hDGs, hDwin⟩ :=
      exists_alignDominantRoundData hK hG ϕ hgiant hvl t ht hZ hdom hstruct (by omega)
        (by omega)
    have hDwin' : D.toAlignDominant.window = S₀ := by rw [hDwin, hS₀eq, hsetcoe]
    -- the list of color classes, the dominant window first
    set rest := (omegaColorClasses (Ω := W) ϕ (alignIdx X')).erase S₀ with hrestdef
    have hS₀nr : S₀ ∉ rest := by
      rw [hrestdef, omegaColorClasses]
      exact (Finset.nodup_toList _).not_mem_erase
    have hinvlist : ∀ Δ ∈ S₀ :: rest,
        IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
      intro Δ' hΔ'
      rcases List.mem_cons.1 hΔ' with rfl | hmem
      · rw [hS₀def]
        exact isInvariant_omegaColorClass_alignIdx hK ϕ hgiant hvl X' v₀
      · exact hinvcls Δ' (List.mem_of_mem_erase hmem)
    have hcovlist : (⋃ Δ ∈ S₀ :: rest, Δ) = (Set.univ : Set W) := by
      refine Set.eq_univ_of_forall fun u => ?_
      have hu : u ∈ (⋃ Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X'), Δ) := by
        rw [hcov]; trivial
      obtain ⟨Δ', hΔ', hu'⟩ := Set.mem_iUnion₂.1 hu
      by_cases he : Δ' = S₀
      · exact Set.mem_iUnion₂.2 ⟨S₀, List.mem_cons_self, he ▸ hu'⟩
      · exact Set.mem_iUnion₂.2
          ⟨Δ', List.mem_cons_of_mem _ ((List.mem_erase_of_ne he).2 hΔ'), hu'⟩
    -- the classes other than the dominant one are small
    have hother : ∀ v : AlignIdx X' → ℕ,
        omegaColorClass (Ω := W) ϕ (alignIdx X') v ≠ S₀ →
        5 * (omegaColorClass (Ω := W) ϕ (alignIdx X') v).ncard ≤ 4 * Fintype.card W := by
      intro v hv
      by_cases hemp : (omegaColorClass (Ω := W) ϕ (alignIdx X') v).ncard = 0
      · rw [hemp]; omega
      obtain ⟨u, hu⟩ : (omegaColorClass (Ω := W) ϕ (alignIdx X') v).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        rw [h, Set.ncard_empty] at hemp
        exact hemp rfl
      refine five_mul_ncard_omegaColorClass_le_of_le_at hG ϕ hgiant hvl (by omega) ht ht1
        (by omega) (alignIdx X') (α := α) hα0 hα45 v ?_
      intro j hj
      have hjne : j ≠ i₀' := by
        rintro rfl
        refine hv ?_
        have hvu : omegaColor ϕ (alignIdx X') u = v := hu
        have hnc : (Tpoint ϕ u ∩ {γ : Fin m | alignIdx X' γ = i₀'}).ncard = t := by
          have h := congrFun hvu i₀'
          rw [hj] at h
          exact h
        have htot : (Tpoint ϕ u).ncard = t := ht u
        have hsub : Tpoint ϕ u ⊆ {γ : Fin m | alignIdx X' γ = i₀'} := by
          have h1 : Tpoint ϕ u ∩ {γ : Fin m | alignIdx X' γ = i₀'} = Tpoint ϕ u :=
            Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hnc, htot])
              (Set.toFinite _)
          rw [← h1]
          exact Set.inter_subset_right
        have huS : u ∈ S₀ := by rw [hS₀eq, mem_omegaOf]; exact hsub
        have hvv : v = v₀ := hvu.symm.trans huS
        rw [hvv, hS₀def]
      have hdisj : Disjoint (colorSet (alignIdx X') j) (colorSet (alignIdx X') i₀') := by
        rw [Finset.disjoint_left]
        intro γ h1 h2
        simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact hjne (h1.symm.trans h2)
      have hsum : (colorSet (alignIdx X') j).card + (colorSet (alignIdx X') i₀').card ≤ m := by
        rw [← Finset.card_union_of_disjoint hdisj]
        have h := Finset.card_le_univ
          ((colorSet (alignIdx X') j) ∪ (colorSet (alignIdx X') i₀'))
        rwa [Fintype.card_fin] at h
      have hbig : m < 2 * (colorSet (alignIdx X') i₀').card := by rw [hcs]; exact hdom
      have h2 : 2 * (colorSet (alignIdx X') j).card ≤ m := by omega
      have h2R : (2 : ℝ) * ((colorSet (alignIdx X') j).card : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast h2
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have hhalf : (1 : ℝ) / 2 * (m : ℝ) ≤ α * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hα12.le hm0
      linarith
    let S : AlignShape W A G x y :=
      { m := m, ϕ := ϕ, act := inst, Vers := Vers, finY := hfiny, X' := X',
        head := S₀, tail := rest, dom := some D }
    refine ⟨Line4cdData.ofShape S m V (Fintype.card W + 1)
      (AlignDominantRoundData.alignDominantRoundCost (Fintype.card W))
      (List.Perm.refl _) hS₀nr hcovlist hinvlist ?_ ?_ hcan hX' ?_ ?_ hcr
      (fun _ _ => le_rfl) ?_⟩
    · intro D' hD'
      have he : D' = D := (Option.some.inj hD').symm
      subst D'
      exact ⟨hDGs, hDwin', hDm⟩
    · intro D' hD'
      have he : D' = D := (Option.some.inj hD').symm
      subst D'
      exact D.defaultCosetEnum_spec
    · change hfiny.toFinset.toList.length ≤ V
      rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card (Vers y) hfiny]
      exact hqv
    · change (S₀ :: rest).length ≤ Fintype.card W + 1
      rw [List.length_cons]
      have hle : rest.length ≤ (omegaColorClasses (Ω := W) ϕ (alignIdx X')).length := by
        rw [hrestdef]; exact List.length_erase_le
      omega
    · intro Δ hΔ hn
      have hne : Δ ≠ S₀ := by
        rcases hn with hn | hn
        · exact hn
        · simp [S] at hn
      have hm : Δ ∈ omegaColorClasses (Ω := W) ϕ (alignIdx X') := by
        rcases List.mem_cons.1 hΔ with h | h
        · exact False.elim (hne h)
        · exact List.mem_of_mem_erase h
      obtain ⟨u, hu⟩ := mem_omegaColorClasses.1 hm
      rw [hu]
      exact hother _ (by rw [← hu]; exact hne)

end FromVersions

/-! ### The branch of lines 4c–4d on the window -/

section Core

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- §15, **lines 4c and 4d on the window**: the branch, with everything the fields of
`Babai.Sec15Remaining` ask for.

The hypotheses are the data lines 1–4 leave: the group `G` induced on the window is
transitive with a giant representation `ϕ : G → S(Γ)`, the window is the set of standard
blocks labelled by the `t`-subsets of `Γ` (`Babai.PrimitiveCaseId`), the Johnson parameter
is at least `217` — the test of line 2 has failed (`Babai.le_param_of_line4c`) — and the
relative symmetry defect of `H(x)` is at least `1/2` (`Babai.LargeDefectData` at
`α = 3/4`).

Line 4c is Theorem 9.2.3 (`Babai.exists_canonicalVersions_of_uniform`); line 4d is
Procedure Align, which is `Babai.nonempty_alignData_of_versions` with `α = 3/4`.

**The reject exit of lines 4c–4d.**  When the family `Vers y` is empty, Eq. (71) is a union
over nothing and `Babai.AlignShape.red` answers `∅` with no call.  That is right, and it is
not a way of writing the answer down: Theorem 9.2.3 makes `Vers z` empty *exactly* when
`Babai.LargeDefectData` fails at `z` — `Babai.exists_canonicalVersions_of_uniform` gives
both directions, `hne` for nonemptiness under the test and `hoff` for emptiness outside it —
and that test reads `z` alone.  The test holds at `x` here, by the failure of line 4b, so a
failure at `y` says that `x` and `y` have different relative symmetry defects; the defect is
canonical, so `Iso_G(x,y) = ∅`.  This is the same shape as the two reject exits of
lines 5–7 (`Babai.Line57Data.rejectDefect`, `Babai.Line57Data.rejectCase`). -/
theorem nonempty_line4cdData {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m t : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (pid : PrimitiveCaseId ϕ t) (hvl : VeryLargeK m (maxOrbitLength G)) (ht2 : 2 ≤ t)
    (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W) {x y : W → A}
    (hx : LargeDefectData pid x (3 / 4 : ℝ)) {q : ℕ → ℕ} {c : ℕ}
    (hu : Theorem923Uniform q c) :
    Nonempty (Line4cdData W A G x y m
      (q m * m ^ (c * t) * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W))) := by
  classical
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  obtain ⟨Vers, hcan, hne, hfin, hcost, hgood, hoff⟩ :=
    exists_canonicalVersions_of_uniform hK pid (le_rfl) (by norm_num) hx hu
  obtain ⟨X', hX'⟩ := hne x hx
  have hqv : (Vers y).ncard ≤ q m * m ^ (c * t) := by
    by_cases hy : LargeDefectData pid y (3 / 4 : ℝ)
    · exact hcost y hy
    · rw [hoff y hy]; simp
  exact nonempty_alignData_of_versions hG hgiant hvl pid.tPointOf_eq (by omega)
    (by have := pid.four_t; rwa [Fintype.card_fin] at this) hm hmn hK hcan (hfin y) hqv hX'
    (by norm_num) (by norm_num) (by norm_num) (hgood x hx X' hX')

end Core

/-! ### The branch, read on `Ω` -/

section Branch

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]

/-- §15, lines 4c–4d: **the tests the branch is taken after** — lines 1, 2, 4, 4a and 4b
have all failed, and the instance is with respect to a group. -/
def Line4cdTest (i : HintedInstance Ω A) : Prop :=
  IsGroupInstance i.inst ∧ IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize ∧
    IsPrimitiveCase i ∧ ¬ TIsOne i ∧ ¬ SmallDefect i

/-- A round that produces at most `cost` instances produces at most `cost'` for every
`cost' ≥ cost`. -/
def Line4cdData.mono {W : Type*} [Fintype W] [DecidableEq W] {A : Type*}
    {G : Subgroup (Equiv.Perm W)} {x y : W → A} {par cost cost' : ℕ}
    (C : Line4cdData W A G x y par cost) (h : cost ≤ cost') : Line4cdData W A G x y par cost' :=
  { C with calls_length := C.calls_length.trans h }

/-- §15, lines 4c–4d: **the type of one round of Procedure Align on the window**, at an
instance that passes the tests of line 4c.

**The cost.**  The number of instances is bounded by `Babai.line4cdCost q c n` of the window
size `n`, whose version factor is `qMax q(n)·n^{c·log₂ n}`.  Theorem 9.2.3 bounds the
versions by `q(m)·m^{c·t}`, and at every instance that passes the tests `q(m)·m^{c·t} ≤
qMax q(n)·n^{c·log₂ n}` (`Babai.line4cd_versionCost_le`), so the rounds Theorem 9.2.3 gives
are rounds of this type (`Babai.line4cdDataOf`).  The Master only ever uses the bound in
this form (`Babai.line4cd_calls`).  Stating it in the window size lets a round whose versions
are counted in the size of the window, as the RAM's are, be a choice too; see the corrected paper,
the entry on the witness of Theorem 9.2.3 at lines 4c–4d. -/
abbrev Line4cdDataAt (i : HintedInstance Ω A) (h : Line4cdTest i) (q : ℕ → ℕ) (c : ℕ) :=
  Line4cdData i.inst.Δ A
    (restrictTo (johnsonData h.2.1).K i.inst.Δ (johnsonData h.2.1).invariant)
    (restrictStr i.inst.Δ i.inst.x) (restrictStr i.inst.Δ i.inst.y) (johnsonData h.2.1).m
    (line4cdCost q c (Fintype.card i.inst.Δ))

/-- §15, lines 4c–4d: **the bound of Theorem 9.2.3 in the window size.**  At an instance that
passes the tests, `m ≤ n` (the Johnson parameter is at most the window size) and
`t ≤ log₂ n` (`n = C(m,t) ≥ 2^t`, since `4t < m`), so the count of Theorem 9.2.3 and the
factors of Eq. (71) are at most `Babai.line4cdCost q c n`. -/
theorem line4cd_versionCost_le {i : HintedInstance Ω A} (h : Line4cdTest i) (q : ℕ → ℕ)
    (c : ℕ) :
    q (johnsonData h.2.1).m * (johnsonData h.2.1).m ^ (c * (johnsonData h.2.1).t) *
      (Fintype.card i.inst.Δ + 1) *
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card i.inst.Δ) ≤
    line4cdCost q c (Fintype.card i.inst.Δ) := by
  set d := johnsonData h.2.1 with hddef
  have hcard : Fintype.card i.inst.Δ = i.inst.windowSize := card_window d
  have hmn : d.m ≤ i.inst.windowSize := d.param_le
  have hm217 : 217 ≤ d.m := by
    have := le_param_of_line4c h.2.1 h.2.2.1
    rwa [param_eq h.2.1] at this
  have h4t : 4 * d.t < d.m := by
    have := (primitiveCaseId h.2.1 h.2.2.2.1).four_t
    rwa [Fintype.card_fin] at this
  have hchoose : i.inst.windowSize = d.m.choose d.t := by
    have he := Nat.card_congr (primitiveCaseId h.2.1 h.2.2.2.1).label
    rw [card_binom (Fin d.m) d.t] at he
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at he
    rw [← hcard]
    exact he
  have hpow : 2 ^ d.t ≤ i.inst.windowSize := by
    rw [hchoose]; exact two_pow_le_choose (by omega)
  have htlog : d.t ≤ Nat.log 2 i.inst.windowSize :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  rw [line4cdCost, hcard]
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ ?_))
  · exact le_qMax q hmn
  · calc d.m ^ (c * d.t) ≤ i.inst.windowSize ^ (c * d.t) := Nat.pow_le_pow_left hmn _
      _ ≤ i.inst.windowSize ^ (c * Nat.log 2 i.inst.windowSize) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ htlog)

/-- §15, lines 4c–4d: **a round of Procedure Align at every instance that passes the test of
line 4c**.

What is chosen is the *geometric data* of Procedure Align (`Babai.AlignShape`): the
canonical family of versions Theorem 9.2.3 returns, the fixed version of `X(x)`, the color
classes, the round of lines 7–11 on the dominant window.  The reduction is a named function
of that data, so a choice cannot be a program that writes the answer down; see
the corrected paper entry on Finding 1 of the audit of Secs. 14–15.  The Master Algorithm
is stated for every such choice. -/
def Line4cdChoice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] [Fintype A]
    [DecidableEq A] (q : ℕ → ℕ) (c : ℕ) :=
  ∀ (i : HintedInstance Ω A) (h : Line4cdTest i), Line4cdDataAt i h q c

/-- §15, lines 4c–4d: **`Babai.Line4cdChoice` is inhabited** — Theorem 9.2.3 at line 4c,
Procedure Align at line 4d (`Babai.nonempty_line4cdData`).  This is the only place where
`Classical.choice` enters lines 4c–4d. -/
noncomputable def line4cdDataOf {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Line4cdChoice Ω A q c := fun _ h =>
  (Classical.choice (nonempty_line4cdData (johnsonData h.2.1).transitive
    (johnsonData h.2.1).giant (primitiveCaseId h.2.1 h.2.2.2.1)
    (veryLargeK_of_hugeM (johnsonData h.2.1).transitive (hugeM_of_data h.2.1 h.2.2.1))
    (two_le_tParam h.2.1 h.2.2.2.1 h.2.2.2.2.1)
    (by have := le_param_of_line4c h.2.1 h.2.2.1; rwa [param_eq h.2.1] at this)
    (by
      have h1 := (johnsonData h.2.1).param_le
      have h2 := card_window (johnsonData h.2.1)
      omega)
    (largeDefectData_of_not_smallDefect h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
      (by norm_num)) hu)).mono (line4cd_versionCost_le h q c)

/-- §15, **lines 4c and 4d** as a branch of the round: the round on the window, read on
`Ω` (`Babai.liftWindow`).  Outside the tests of line 4c the branch is never taken, and the
leaf `.done I.answer` stands there. -/
noncomputable def line4cdFunCoset {q : ℕ → ℕ} {c : ℕ} (C : Line4cdChoice Ω A q c)
    (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : Line4cdTest i then
    liftWindow (johnsonData h.2.1).K i.inst.Δ (johnsonData h.2.1).invariant i.inst.x
      (C i h).toCosetCore.red
  else cosetLeaf i.inst i.inst.answer

noncomputable def line4cdFun {q : ℕ → ℕ} {c : ℕ} (C : Line4cdChoice Ω A q c)
    (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed i.inst (line4cdFunCoset C i)

/-- §15, lines 4c–4d, **line 11 of Procedure Align**: the hint the branch hands to each of
its calls, read on `Ω` (`Babai.cosetWindowHintLift`). -/
noncomputable def line4cdLift {q : ℕ → ℕ} {c : ℕ} (C : Line4cdChoice Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : HintedInstance Ω A :=
  if h : Line4cdTest i then
    ⟨J, cosetWindowHintLift (johnsonData h.2.1).invariant i.inst.x (C i h).shape.hint J⟩
  else ⟨J, none⟩

@[simp] theorem inst_line4cdLift {q : ℕ → ℕ} {c : ℕ} (C : Line4cdChoice Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : (line4cdLift C i J).inst = J := by
  rw [line4cdLift]
  split <;> rfl

section Fields

variable {q : ℕ → ℕ} {c : ℕ} (C : Line4cdChoice Ω A q c)

/-- §15, lines 4c–4d, **correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem line4cd_run (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i)
    (hs : ¬ SmallDefect i) : (line4cdFun C i).run = i.inst.answer := by
  have h : Line4cdTest i := ⟨hgrp, hJ, hell, hp, ht, hs⟩
  rw [line4cdFun, line4cdFunCoset, dif_pos h]
  exact run_alignLiftWindow_core (C i h).toCosetCore i.inst (johnsonData h.2.1).isGroup
    rfl rfl
    rfl

/-- §15, lines 4c–4d: **every call is a group instance**. -/
theorem line4cd_group (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i)
    (hs : ¬ SmallDefect i) : ∀ J ∈ (line4cdFun C i).calls, IsGroupInstance J := by
  have h : Line4cdTest i := ⟨hgrp, hJ, hell, hp, ht, hs⟩
  rw [line4cdFun, line4cdFunCoset, dif_pos h]
  exact calls_alignLiftWindow_core_group (C i h).toCosetCore i.inst i.inst.x

/-- §15, lines 4c–4d, **the progress**: every call has a window of at most `2n/3` points,
or the same window and a Johnson parameter of at most `m/2` — Eq. (73). -/
theorem line4cd_decreases (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i)
    (hs : ¬ SmallDefect i) : ∀ J ∈ (line4cdFun C i).calls,
    MakesProgress HintedInstance.win param i (line4cdLift C i J) := by
  have h : Line4cdTest i := ⟨hgrp, hJ, hell, hp, ht, hs⟩
  intro J hJmem
  rw [line4cdFun, line4cdFunCoset, dif_pos h] at hJmem
  have hcard : Fintype.card i.inst.Δ = i.inst.Δ.ncard := card_window (johnsonData h.2.1)
  have hwin : HintedInstance.win i = i.inst.Δ.ncard := rfl
  have hwinJ : HintedInstance.win (line4cdLift C i J) = J.windowSize :=
    congrArg SIInstance.windowSize (inst_line4cdLift C i J)
  have hpar : param i = (johnsonData h.2.1).m := param_eq h.2.1
  have h217 : 217 ≤ (johnsonData h.2.1).m := by
    have := le_param_of_line4c h.2.1 h.2.2.1
    rwa [param_eq h.2.1] at this
  have hd := decreases_alignLiftWindow_core (C i h).toCosetCore i.inst i.inst.x hcard J hJmem
  rw [show (C i h).toCosetCore.hint = (C i h).shape.hint from rfl] at hd
  have hliftJ : line4cdLift C i J =
      ⟨J, cosetWindowHintLift (johnsonData h.2.1).invariant i.inst.x
        (C i h).shape.hint J⟩ := by rw [line4cdLift, dif_pos h]
  rcases hd with hsmall | ⟨hle, hpar2⟩
  · exact Or.inl ⟨by rw [hwin]; exact (johnsonData h.2.1).one_le_windowSize,
      by rw [hwinJ, hwin]; exact hsmall⟩
  · refine Or.inr ⟨by rw [hwinJ, hwin]; exact hle, by omega, ?_⟩
    rw [hliftJ]
    omega

/-- §15, lines 4c–4d, **the number of instances one round produces**: Eq. (71). -/
theorem line4cd_calls (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i)
    (hs : ¬ SmallDefect i) :
    ((line4cdFun C i).calls).length ≤ line4cdCost q c i.inst.windowSize := by
  have h : Line4cdTest i := ⟨hgrp, hJ, hell, hp, ht, hs⟩
  rw [line4cdFun, line4cdFunCoset, dif_pos h]
  refine le_trans (calls_length_alignLiftWindow_core (C i h).toCosetCore i.inst i.inst.x) ?_
  rw [← card_window (johnsonData h.2.1)]

end Fields

end Branch

end Babai
