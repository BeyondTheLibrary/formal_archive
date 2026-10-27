/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the Master's round of Procedure Align (§14.1) for the header the round
of Sec. 15, lines 5–7, computes.
-/
import Workspace.Algo.PrimitiveLine4dDomData
import Workspace.Algo.AlignShapeTransport

/-!
# The round of Procedure Align at lines 5–7, from the header

At lines 5–7 of the Master Algorithm (§15) the machine runs Procedure Align (§14.1) on a header
(`Algo.AVHdr`): the action, the fixed version `X'` of `X(x)`, the list of versions of `X(y)`,
the windows (`Algo.alignL57Windows`) and the two strings. The versions are split outcomes at
a threshold `α` with `1/2 < α` and `5α ≤ 4` (Theorem 13.2.1 with Theorem 9.2.3; Line 7a of §15
takes `α = 4/5` at outcome (1)), and what is proved of the list is that every isomorphism
carries `X'` to a listed version.

This file builds the Master's round (`Babai.AlignShape`) the header describes, as
`Algo.exists_line4dData` and `Algo.exists_line4dDomData` do at line 4d, where the threshold is
`3/4` and the versions are the canonical family. The run is proved from the transport of `X'`
(`Babai.AlignShape.run_red_of_transport`). What comes out (`Algo.exists_alignL57Shape`):

* the header describes the round (`Algo.ADDescribes` in case 1 of the repair of lines 7–11,
  `Algo.AVDescribes` otherwise), so the machine walks it;
* every call of the round is a coset instance in `G`;
* without the test of the repair (`Algo.alignRLarge`), every call has at most `4n/5` points
  (Eq. (72));
* with it, the facts the hint of line 11 needs (`Algo.L57LargeFacts`): `G₁ ≤ G`, the dominant
  window is `G₁`-invariant, the other classes have at most `2n/3` points
  (`Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`), and `m*` is large.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-! ## Two facts at a general threshold -/

section Alpha

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

/-- §14.1, line 7, **the trivial case at threshold `α`** (`Algo.four_mul_ncard_domClass_le` at
`α = 3/4`): when line 6 finds a dominant class but `m* < 2`, the dominant class is a single
block of the `α`-partition `X'`, so it has at most `αm` points. -/
theorem ncard_domClass_le_alpha (hA : RawAction.WF n m A ϕ) {o : RawAlignOutcome}
    {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X') {α : ℝ}
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X')
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hms : alignRMs (A, o) < 2) :
    (({γ : Fin m | labAt (alignOutcomeLab (A.2.1, o)) (γ : ℕ) =
      alignRDomColor (alignRColorOf (A, o))}.ncard : ℕ) : ℝ) ≤ α * m := by
  classical
  have hg : A.2.1.length = m := hA.2.1
  set lab := alignOutcomeLab (A.2.1, o) with hlab
  have hhd' : alignRHasDom (A, lab) = true := hhd
  have hq : alignRColorOf (A, o) = (A, lab) := rfl
  rw [hq]
  set dc := alignRDomColor (A, lab) with hdcdef
  set γ₀ : Fin m := ⟨(alignRDomPoints (A, lab)).getD 0 0, alignRDomFirst_lt hg hhd'⟩ with hγ₀
  have hdc : dc = labAt lab (γ₀ : ℕ) := rfl
  rcases decAlignOutcome_cases hX with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩
  · have hlabγ : ∀ γ : Fin m, labAt lab (γ : ℕ) =
        Nat.pair (labAt P.1 (γ : ℕ)) (cpBlockSize ((A.2.1, P), (γ : ℕ))) :=
      labAt_alignOutcomeLab_partition hg P
    have hblk : ∀ γ : Fin m, {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ : ℕ)} ⊆
        {v : Fin m | labAt lab (v : ℕ) = labAt lab (γ : ℕ)} := by
      intro γ v hv
      have hv' : cellOf P (v : ℕ) = cellOf P (γ : ℕ) := hv
      show labAt lab (v : ℕ) = labAt lab (γ : ℕ)
      rw [hlabγ, hlabγ, cpBlockSize_congr P hv', show labAt P.1 (v : ℕ) = labAt P.1 (γ : ℕ) from
        congrArg Prod.fst hv']
    set b := cpBlockSize ((A.2.1, P), (γ₀ : ℕ)) with hb
    have hbB : {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ₀ : ℕ)}.ncard = b :=
      (cpBlockSize_eq hg P γ₀).symm
    have hb1 : 1 ≤ b := by
      rw [← hbB]
      exact (Set.ncard_pos (Set.toFinite _)).2 ⟨γ₀, rfl⟩
    have hms' : alignRMs (A, rawAlignPartition P) =
        {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard / b := by
      rw [← length_alignRDomPoints hg hhd']
      rfl
    have hΔB : {γ : Fin m | labAt lab (γ : ℕ) = dc} =
        {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ₀ : ℕ)} := by
      refine Set.Subset.antisymm ?_ (by rw [hdc]; exact hblk γ₀)
      intro γ hγ
      by_contra hne
      have hγ' : labAt lab (γ : ℕ) = labAt lab (γ₀ : ℕ) := hγ
      have hbγ : cpBlockSize ((A.2.1, P), (γ : ℕ)) = b := by
        have := hγ'
        rw [hlabγ, hlabγ] at this
        exact (Nat.pair_eq_pair.1 this).2
      have hsub : {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ₀ : ℕ)} ∪
          {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ : ℕ)} ⊆
          {γ : Fin m | labAt lab (γ : ℕ) = dc} := by
        rintro v (hv | hv)
        · have := hblk γ₀ hv; exact this.trans hdc.symm
        · have := hblk γ hv; exact (this.trans hγ').trans hdc.symm
      have hdisj : Disjoint {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ₀ : ℕ)}
          {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ : ℕ)} := by
        rw [Set.disjoint_left]
        intro v h1 h2
        exact hne (show cellOf P (γ : ℕ) = cellOf P (γ₀ : ℕ) from
          (h2 : cellOf P (v : ℕ) = _).symm.trans h1)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hbB,
        ← cpBlockSize_eq hg P γ, hbγ] at hle
      have h2 : 2 ≤ {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard / b :=
        (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      rw [← hms'] at h2
      omega
    rw [hΔB, hbB]
    set P' := decAlignPart m P
    have hcolor := (alignColor_inl (Set.univ : Set (Fin m)) P' (Set.mem_univ γ₀)).symm.trans
      (alignColor_decAlignPartition hg P γ₀)
    have hbP : (P'.block ⟨γ₀, Set.mem_univ γ₀⟩).ncard = b :=
      congrArg Prod.snd (Sum.inl_injective hcolor)
    letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
    have hZ' : P'.IsAlphaPartition α := hZ.2
    have hρ := hZ'.2
    have hbρ := P'.ncard_block_le_rho ⟨γ₀, Set.mem_univ γ₀⟩
    have hcard : Fintype.card ↥(Set.univ : Set (Fin m)) = m := by
      rw [Fintype.card_eq_nat_card, Nat.card_congr (Equiv.Set.univ (Fin m)),
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hbP] at hbρ
    rw [hcard] at hρ
    exact le_trans (by exact_mod_cast hbρ) hρ
  · exfalso
    have h1 := hJ.params
    have h2 := hJ.two_le
    have : alignRMs (A, rawAlignJohnson J) = rawJDeg J := rfl
    omega

end Alpha

/-- Theorem 10.5.1 (a), (e): **`Ω(Δ)` is not empty once `Δ` has at least `t` points**, `t` the
common size of the sets `T(u)`: a `t`-subset of `Δ` is `T(y)` for some point `y`
(`Babai.exists_Tpoint_eq`), and then `y ∈ Ω(Δ)`. -/
theorem omegaOf_nonempty_of_tPoint {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G))
    {tt : ℕ} (ht : ∀ u : Fin n, tPoint ϕ u = tt) (u₀ : Fin n) {Δ : Set (Fin m)}
    (h : tt ≤ Δ.ncard) : (omegaOf ϕ Δ).Nonempty := by
  obtain ⟨T, hTΔ, hT⟩ := Set.exists_subset_card_eq h
  obtain ⟨y, -, hy⟩ := exists_Tpoint_eq ϕ hϕ hvl u₀ (T := T) (by rw [hT, ht])
  exact ⟨y, mem_omegaOf.2 (by rw [hy]; exact hTΔ)⟩

/-- The size facts of `t`: `1 ≤ t` and `4t < m` (Theorem 10.5.1 (a), (b)). -/
theorem tt_facts_of_transitive {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
    (hG : IsTransitive G) (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G))
    {tt : ℕ} (ht : ∀ u : Fin n, tPoint ϕ u = tt) (hn : 0 < n) : 1 ≤ tt ∧ 4 * tt < m := by
  have u₀ : Fin n := ⟨0, hn⟩
  exact ⟨ht u₀ ▸ one_le_tPoint_of_transitive hG hϕ hvl u₀,
    ht u₀ ▸ four_mul_tPoint_lt hϕ hvl u₀⟩

/-! ## The facts of the hinted call -/

/-- §14.1, lines 7–11, case 3 of the repair (the test `Algo.alignRLarge` holds): **what the
hint of line 11 needs of the header** (`Algo.masterHintStepOK_masterL57Hint`): the group
`G₁ = ϕ⁻¹(Aut(X'))` lies in `G`, the dominant window is `G₁`-invariant, the other color
classes have at most `2n/3` points each, and `m*` is large. -/
structure L57LargeFacts (n : ℕ) (h : AVHdr) : Prop where
  g1 : decGroup n (alignPairG1 (h.1, h.2.1)) ≤ decGroup n h.1.1.2
  invD : rawIsInvariant (alignPairG1 (h.1, h.2.1), adWindow h) = true
  tail : ∀ S ∈ (alignRWindows (alignRColorOf (h.1, h.2.1))).tail,
    3 * (winSet n S).ncard ≤ 2 * n
  nt : 2 ≤ alignRMs (h.1, h.2.1)
  lp : VeryLargeK (alignRMs (h.1, h.2.1))
    (maxOrbitLength (decGroup n (alignPairG1 (h.1, h.2.1))))

/-! ## The round of Procedure Align the header describes -/

section Shape

variable {n m : ℕ} {h : AVHdr} {ϕ : decGroup n h.1.1.2 →* Perm (Fin m)}
  [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- What comes out of the construction: the header describes the round `S`, whose calls are
coset instances in `G`, of at most `4n/5` points each without the test of the repair, and
the facts of the hinted call with it. -/
def L57ShapeOK (n : ℕ) (h : AVHdr)
    (S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2)) : Prop :=
  (l57Small h = true → ∃ D, ADDescribes n h S D) ∧
    (l57Small h = false → ∃ Ws, AVDescribes n h S Ws) ∧
    S.red.run = strIso (decGroup n h.1.1.2 : Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) ∧
    (∀ J ∈ S.red.calls, IsCosetInstance (decGroup n h.1.1.2) J) ∧
    (alignRLarge (h.1, h.2.1) = false → ∀ J ∈ S.red.calls, 5 * J.windowSize ≤ 4 * n) ∧
    (alignRLarge (h.1, h.2.1) = true → L57LargeFacts n h) ∧
    (∀ k, (∀ u, decStrN n h.2.2.2.2.1 u < k) → (∀ u, decStrN n h.2.2.2.2.2 u < k) →
      ∀ J ∈ S.red.calls, MasterCallLetters k J)

variable (hA : RawAction.WF n m h.1 ϕ) (hG : IsTransitive (decGroup n h.1.1.2))
  (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup n h.1.1.2))) {tt : ℕ}
  (ht : ∀ u : Fin n, tPoint ϕ u = tt) (hK : IsCatAction (SplitOutcomes (Fin m)))
  {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m h.2.1 = some X')
  {α : ℝ} (hα : 1 / 2 < α) (hα45 : 5 * α ≤ 4)
  (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m) (hmn : m ≤ n)
  {Ys : List (Pt (SplitOutcomes (Fin m)))}
  (hYs : h.2.2.1.map (decAlignOutcome m) = Ys.map some)
  (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1)) (hx : h.2.2.2.2.1.length = n)
  (hT : ∀ σ : decGroup n h.1.1.2,
    strAct (decStrN n h.2.2.2.2.1) (σ : Perm (Fin n)) = decStrN n h.2.2.2.2.2 → ϕ σ • X' ∈ Ys)

include hA hG hϕ hvl ht hK hX hα hα45 hZ hm hmn hYs hw hx hT

open scoped Classical in
/-- §14.1, lines 4–6, **no dominant color class**: the round of Procedure Align on the color
classes of `Ω` (`Algo.exists_line4dData_of_noDom` at line 4d). Every class has at most `4n/5`
points (Eq. (72) at `α = 1/2`, since every color class of `Γ` has at most `m/2` points). -/
theorem alignL57Shape_noDom (hnd : alignRHasDom (alignRColorOf (h.1, h.2.1)) = false) :
    ∃ S, L57ShapeOK n h S := by
  obtain ⟨ht1, h4t⟩ := tt_facts_of_transitive hG hϕ hvl ht (by omega)
  have hd : h.1.1.1.length = n := hA.1
  have hlarge : alignRLarge (h.1, h.2.1) = false := by
    unfold alignRLarge; rw [hnd]; rfl
  have hsm : l57Small h = false := l57Small_false_of_noDom hnd
  set q := alignRColorOf (h.1, h.2.1) with hq
  have hWLc : alignRWindows q = alignRClasses q := alignRWindows_eq_classes hnd
  have hw' : h.2.2.2.1 = alignRWindows q := by rw [hw, alignL57Windows_of_not hlarge]
  have hcls : ∀ W ∈ alignRWindows q, ∃ u : Fin n,
      winSet n W = omegaColorClass ϕ (alignIdx X') (omegaColor ϕ (alignIdx X') u) := by
    intro W hW
    rw [hWLc] at hW
    exact winSet_alignRClasses_eq hA hϕ hvl hX hW
  have hnwl : (alignRWindows q).map (winSet n) ≠ [] := by
    obtain ⟨W, hW, -⟩ := alignRWindows_cover (q := q) (u := 0)
      (by show 0 < h.1.1.1.length; omega)
    intro he
    rw [List.map_eq_nil_iff] at he
    rw [he] at hW
    simp at hW
  obtain ⟨S₀, rest, hlist⟩ := List.exists_cons_of_ne_nil hnwl
  have hnd' : (S₀ :: rest).Nodup := by
    rw [← hlist, hWLc]; exact nodup_map_winSet_alignRClasses _ hd
  have hmemW : ∀ Δ ∈ S₀ :: rest, ∃ u : Fin n,
      Δ = omegaColorClass ϕ (alignIdx X') (omegaColor ϕ (alignIdx X') u) := by
    intro Δ hΔ
    rw [← hlist, List.mem_map] at hΔ
    obtain ⟨W, hW, rfl⟩ := hΔ
    exact hcls W hW
  have hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    obtain ⟨u, rfl⟩ := hmemW Δ hΔ
    exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hcover : (⋃ Δ ∈ S₀ :: rest, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hW, hu⟩ := alignRWindows_cover (q := q) (u := u)
      (by show (u : ℕ) < h.1.1.1.length; rw [hd]; exact u.isLt)
    exact Set.mem_iUnion₂.2 ⟨winSet n W, by rw [← hlist]; exact List.mem_map_of_mem hW,
      mem_winSet.2 hu⟩
  have hhalf : ∀ i : AlignColor, ((colorSet (alignColor X') i).card : ℝ) ≤ 1 / 2 * m := by
    intro i
    have h2 := two_mul_card_colorSet_le (A := h.1) (lab := alignOutcomeLab (h.1.2.1, h.2.1))
      hA.2.1 (fun γ γ' => alignOutcomeLab_eq_iff hA.2.1 hX γ γ') hnd i
    have : (2 : ℝ) * (colorSet (alignColor X') i).card ≤ m := by exact_mod_cast h2
    linarith
  have hsizes : ∀ Δ ∈ S₀ :: rest, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, rfl⟩ := hmemW Δ hΔ
    exact five_mul_ncard_omegaColorClasses_le hG ϕ hϕ hvl (by omega) ht ht1 (by omega) X'
      (α := 1 / 2) (by norm_num) (by norm_num) hhalf _ (mem_omegaColorClasses.2 ⟨u, rfl⟩)
  let S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) :=
    { m := m, ϕ := ϕ, act := inst, Vers := fun _ => {Z | Z ∈ Ys}, finY := Ys.finite_toSet,
      X' := X', head := S₀, tail := rest, dom := none, versions := Ys }
  have hne : S.head ∉ S.tail := (List.nodup_cons.1 hnd').1
  have hdd : ∀ D, S.dom = some D → (D.toAlignDominant.Gs = preimageSubgroup ϕ (structAut X') ∧
      D.toAlignDominant.window = S.head) := fun D hD => by simp [S] at hD
  have hee : ∀ D, S.dom = some D → S.domEnum.Spec D := fun D hD => by simp [S] at hD
  have hrun := S.run_red_of_transport hne hcover hinv hdd hee hT
  have hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n := by
    rw [hw']
    intro W hW u hu
    exact lt_of_lt_of_eq (lt_of_mem_of_mem_alignRWindows hW hu) hd
  refine ⟨S, fun hs => absurd (hs.symm.trans hsm) (by simp), fun _ => ⟨_,
    ⟨alignShape_red_of_dom_none S rfl, hA, hϕ, hK, hX, hYs, by rw [hw']; exact hlist,
      List.cons_ne_nil _ _, hlt, hinv, hrun⟩⟩, hrun, S.calls_coset_of_facts hne hinv hdd hee,
    fun _ J hJ => ?_, fun hl => absurd (hl.symm.trans hlarge) (by simp),
    fun k hxk hyk => alignShape_letters_of_dom_none S rfl hxk hyk⟩
  rcases S.calls_progress_of_facts hne hinv hdd hee (fun Δ hΔ _ => hsizes Δ hΔ) J hJ with
    h5 | hh
  · simpa using h5
  · exfalso
    simp [AlignShape.hint, S] at hh

open scoped Classical in
/-- §14.1, lines 6–7, **a dominant class with a trivial structure** (`m* < 2`;
`Algo.exists_line4dData_of_trivDom` at line 4d): the dominant class is one block of the
`α`-partition `X'` (`Algo.ncard_domClass_le_alpha`), line 7 does not apply, and the round of
Procedure Align runs on the window `Ω(Δ_j)` and the other classes as they are. Each has at
most `4n/5` points: `Ω(Δ_j)` by Eq. (72) at `α`, the others at `1/2`. -/
theorem alignL57Shape_trivDom (hhd : alignRHasDom (alignRColorOf (h.1, h.2.1)) = true)
    (hms : alignRMs (h.1, h.2.1) < 2) : ∃ S, L57ShapeOK n h S := by
  obtain ⟨ht1, h4t⟩ := tt_facts_of_transitive hG hϕ hvl ht (by omega)
  have hd : h.1.1.1.length = n := hA.1
  have hg : h.1.2.1.length = m := hA.2.1
  have hlarge : alignRLarge (h.1, h.2.1) = false := by
    unfold alignRLarge rawVeryLarge
    simp only [show ¬ 9 ≤ alignRMs (h.1, h.2.1) by omega, decide_false, Bool.false_and,
      Bool.and_false]
  have hsm : l57Small h = false := by
    unfold l57Small
    simp only [show ¬ 2 ≤ alignRMs (h.1, h.2.1) by omega, decide_false, Bool.and_false]
  have hα34 := ncard_domClass_le_alpha hA hX hZ hhd hms
  set lab := alignOutcomeLab (h.1.2.1, h.2.1) with hlab
  have hhd' : alignRHasDom (h.1, lab) = true := hhd
  set dc := alignRDomColor (h.1, lab) with hdcdef
  set domWin := alignRDomWindow ((h.1, lab), dc) with hdomWin
  have hW : alignRWindows (h.1, lab) =
      domWin :: (alignRClasses (h.1, lab)).filter (fun W => alignRNotDom ((h.1, lab), W)) := by
    rw [alignRWindows, if_pos hhd']
  have hw' : h.2.2.2.1 = alignRWindows (h.1, lab) := by
    rw [hw, alignL57Windows_of_not hlarge]; rfl
  set γ₀ : Fin m := ⟨(alignRDomPoints (h.1, lab)).getD 0 0, alignRDomFirst_lt hg hhd'⟩
  haveI : Nonempty (AlignIdx X') := nonempty_alignIdx (by omega)
  set i₀ := alignIdx X' γ₀ with hi₀
  have hset : {γ : Fin m | labAt lab (γ : ℕ) = dc} = {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ
    simp only [Set.mem_setOf_eq]
    rw [show dc = labAt lab (γ₀ : ℕ) from rfl, hlab, alignOutcomeLab_eq_iff hg hX γ γ₀, hi₀]
    exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩
  have hcs : ((colorSet (alignIdx X') i₀ : Finset (Fin m)) : Set (Fin m)) =
      {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ; simp [colorSet]
  have hcard : (colorSet (alignIdx X') i₀).card = {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard := by
    rw [← Set.ncard_coe_finset, hcs, ← hset]
  have hdomI : m < 2 * (colorSet (alignIdx X') i₀).card := by
    rw [hcard]
    exact alignRDomColor_dominant_of_wf hA hhd'
  have hα' : ((colorSet (alignIdx X') i₀).card : ℝ) ≤ α * m := by
    rw [hcard]; exact hα34
  set v₀ : AlignIdx X' → ℕ := fun j => if j = i₀ then tt else 0 with hv₀def
  have hS₀eq : omegaColorClass (Ω := Fin n) ϕ (alignIdx X') v₀ =
      omegaOf ϕ {γ : Fin m | alignIdx X' γ = i₀} :=
    omegaColorClass_eq_omegaOf ϕ ht (alignIdx X') i₀ v₀ (by simp [hv₀def])
      (fun j hj => by simp [hv₀def, hj])
  have hhead : winSet n domWin = omegaColorClass (Ω := Fin n) ϕ (alignIdx X') v₀ := by
    rw [hS₀eq, hdomWin, winSet_alignRDomWindow_of_wf hA hϕ hvl lab dc, hset]
  set head : Set (Fin n) := winSet n domWin with hheaddef
  set tail : List (Set (Fin n)) :=
    ((alignRClasses (h.1, lab)).filter (fun W => alignRNotDom ((h.1, lab), W))).map (winSet n)
    with htaildef
  have hlist : (alignRWindows (h.1, lab)).map (winSet n) = head :: tail := by
    rw [hW]; rfl
  have htailmem : ∀ Δ ∈ tail, ∃ u : ℕ,
      alignROmegaClass ((h.1, lab), u) ∈ alignRClasses (h.1, lab) ∧
      alignROmegaClass ((h.1, lab), u) ≠ domWin ∧
      Δ = winSet n (alignROmegaClass ((h.1, lab), u)) := by
    intro Δ hΔ
    obtain ⟨W, hW', rfl⟩ := List.mem_map.1 hΔ
    rw [List.mem_filter, alignRNotDom, decide_eq_true_iff] at hW'
    obtain ⟨u, -, rfl⟩ := mem_alignRClasses hW'.1
    exact ⟨u, hW'.1, hW'.2, rfl⟩
  have hne : head ∉ tail := by
    intro hmem
    obtain ⟨u, -, hune, he⟩ := htailmem head hmem
    exact winSet_alignROmegaClass_ne (q := (h.1, lab)) hd hune he.symm
  have hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hWm, hu⟩ := alignRWindows_cover (q := (h.1, lab)) (u := u)
      (by show (u : ℕ) < h.1.1.1.length; rw [hd]; exact u.isLt)
    refine Set.mem_iUnion₂.2 ⟨winSet n W, ?_, mem_winSet.2 hu⟩
    rw [← hlist]
    exact List.mem_map_of_mem hWm
  have hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · rw [hhead]
      exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
    · obtain ⟨u, hcl, -, rfl⟩ := htailmem Δ hΔ
      obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hA hϕ hvl hX hcl
      rw [hv]
      exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hsizes : ∀ Δ ∈ head :: tail, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · rw [hhead]
      refine five_mul_ncard_omegaColorClass_le_of_le_at hG ϕ hϕ hvl (by omega) ht ht1
        (by omega) (alignIdx X') (α := α) (by linarith) hα45 v₀ ?_
      intro i hi
      by_cases hii : i = i₀
      · rw [hii]; exact hα'
      · simp only [hv₀def, hii, if_false] at hi
        omega
    · obtain ⟨u, hcl, hune, rfl⟩ := htailmem Δ hΔ
      obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hA hϕ hvl hX hcl
      rw [hv]
      refine five_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) ht ht1
        (by omega) (alignIdx X') hdomI _ ?_
      rw [← hv, ← hS₀eq, ← hhead]
      exact winSet_alignROmegaClass_ne (q := (h.1, lab)) hd hune
  let S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) :=
    { m := m, ϕ := ϕ, act := inst, Vers := fun _ => {Z | Z ∈ Ys}, finY := Ys.finite_toSet,
      X' := X', head := head, tail := tail, dom := none, versions := Ys }
  have hdd : ∀ D, S.dom = some D → (D.toAlignDominant.Gs = preimageSubgroup ϕ (structAut X') ∧
      D.toAlignDominant.window = S.head) := fun D hD => by simp [S] at hD
  have hee : ∀ D, S.dom = some D → S.domEnum.Spec D := fun D hD => by simp [S] at hD
  have hrun := S.run_red_of_transport hne hcover hinv hdd hee hT
  have hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n := by
    rw [hw']
    intro W hW u hu
    exact lt_of_lt_of_eq (lt_of_mem_of_mem_alignRWindows hW hu) hd
  refine ⟨S, fun hs => absurd (hs.symm.trans hsm) (by simp), fun _ => ⟨_,
    ⟨alignShape_red_of_dom_none S rfl, hA, hϕ, hK, hX, hYs, by rw [hw']; exact hlist,
      List.cons_ne_nil _ _, hlt, hinv, hrun⟩⟩, hrun, S.calls_coset_of_facts hne hinv hdd hee,
    fun _ J hJ => ?_, fun hl => absurd (hl.symm.trans hlarge) (by simp),
    fun k hxk hyk => alignShape_letters_of_dom_none S rfl hxk hyk⟩
  rcases S.calls_progress_of_facts hne hinv hdd hee (fun Δ hΔ _ => hsizes Δ hΔ) J hJ with
    h5 | hh
  · simpa using h5
  · exfalso
    simp [AlignShape.hint, S] at hh

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- §14.1, lines 6–11, **a dominant class with a nontrivial structure** (`2 ≤ m*`;
`Algo.exists_line4dDomData` at line 4d): the data `Dd` of lines 7–11
(`Algo.exists_domRoundData_alpha`), the dominant window first, the enumerations the machine
computes (`Algo.line4dDomEnum`). In case 1 of the repair the header describes the descent over
the cosets of `ker ϕ*`; otherwise (the test `Algo.alignRLarge` holds) Eq. (71) over the orbits
of `G*` in the window and the other classes, each of at most `2n/3` points
(`Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`). -/
theorem alignL57Shape_dom (hhd : alignRHasDom (alignRColorOf (h.1, h.2.1)) = true)
    (hnt : 2 ≤ alignRMs (h.1, h.2.1)) : ∃ S, L57ShapeOK n h S := by
  obtain ⟨ht1, h4t⟩ := tt_facts_of_transitive hG hϕ hvl ht (by omega)
  obtain ⟨Dd, hDm, hDGs, hDwin, hDms, hDker, -⟩ :=
    exists_domRoundData_alpha hA hG hϕ hvl ht hK hX hα hZ hm hmn hhd hnt
  have hd : h.1.1.1.length = n := hA.1
  have hg : h.1.2.1.length = m := hA.2.1
  set lab := alignOutcomeLab (h.1.2.1, h.2.1) with hlab
  have hhd' : alignRHasDom (h.1, lab) = true := hhd
  set dc := alignRDomColor (h.1, lab) with hdcdef
  set domWin := alignRDomWindow ((h.1, lab), dc) with hdomWin
  have hW : alignRWindows (h.1, lab) =
      domWin :: (alignRClasses (h.1, lab)).filter (fun W => alignRNotDom ((h.1, lab), W)) := by
    rw [alignRWindows, if_pos hhd']
  set γ₀ : Fin m := ⟨(alignRDomPoints (h.1, lab)).getD 0 0, alignRDomFirst_lt hg hhd'⟩
  haveI : Nonempty (AlignIdx X') := nonempty_alignIdx (by omega)
  set i₀ := alignIdx X' γ₀ with hi₀
  have hset : {γ : Fin m | labAt lab (γ : ℕ) = dc} = {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ
    simp only [Set.mem_setOf_eq]
    rw [show dc = labAt lab (γ₀ : ℕ) from rfl, hlab, alignOutcomeLab_eq_iff hg hX γ γ₀, hi₀]
    exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩
  have hdomR : m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard :=
    alignRDomColor_dominant_of_wf hA hhd'
  have hhead : winSet n domWin = omegaOf ϕ {γ : Fin m | alignIdx X' γ = i₀} := by
    rw [hdomWin, winSet_alignRDomWindow_of_wf hA hϕ hvl lab dc, hset]
  have hdomI : m < 2 * (colorSet (alignIdx X') i₀).card := by
    have : ((colorSet (alignIdx X') i₀ : Finset (Fin m)) : Set (Fin m)) =
        {γ : Fin m | alignIdx X' γ = i₀} := by
      ext γ; simp [colorSet]
    rw [← Set.ncard_coe_finset, this, ← hset]
    exact hdomR
  set head : Set (Fin n) := winSet n domWin with hheaddef
  set tail : List (Set (Fin n)) :=
    ((alignRClasses (h.1, lab)).filter (fun W => alignRNotDom ((h.1, lab), W))).map (winSet n)
    with htaildef
  have htailmem : ∀ Δ ∈ tail, ∃ u : ℕ,
      alignROmegaClass ((h.1, lab), u) ∈ alignRClasses (h.1, lab) ∧
      alignROmegaClass ((h.1, lab), u) ≠ domWin ∧
      Δ = winSet n (alignROmegaClass ((h.1, lab), u)) := by
    intro Δ hΔ
    obtain ⟨W, hW', rfl⟩ := List.mem_map.1 hΔ
    rw [List.mem_filter, alignRNotDom, decide_eq_true_iff] at hW'
    obtain ⟨u, -, rfl⟩ := mem_alignRClasses hW'.1
    exact ⟨u, hW'.1, hW'.2, rfl⟩
  have hne : head ∉ tail := by
    intro hmem
    obtain ⟨u, -, hune, he⟩ := htailmem head hmem
    exact winSet_alignROmegaClass_ne (q := (h.1, lab)) hd hune he.symm
  have hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hWm, hu⟩ := alignRWindows_cover (q := (h.1, lab)) (u := u)
      (by show (u : ℕ) < h.1.1.1.length; rw [hd]; exact u.isLt)
    refine Set.mem_iUnion₂.2 ⟨winSet n W, ?_, mem_winSet.2 hu⟩
    rw [hW] at hWm
    rcases List.mem_cons.1 hWm with rfl | hWm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hWm)
  have hG1 : decGroup n (alignPairG1 (h.1, h.2.1)) = preimageSubgroup ϕ (structAut X') :=
    decGroup_alignPairG1 hA hϕ hK hX
  have hinvTail : ∀ Δ ∈ tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    obtain ⟨u, hcl, -, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hA hϕ hvl hX hcl
    rw [hv]
    exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · have := Dd.isInvariant_window
      rw [hDGs, hDwin] at this
      exact this
    · exact hinvTail Δ hΔ
  have hsizes : ∀ Δ ∈ tail, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, hcl, hune, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hA hϕ hvl hX hcl
    rw [hv]
    refine five_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) ht ht1
      (by omega) (alignIdx X') hdomI _ ?_
    rw [← hv, ← hhead]
    exact winSet_alignROmegaClass_ne (q := (h.1, lab)) hd hune
  have hsizes3 : ∀ Δ ∈ tail, 3 * Δ.ncard ≤ 2 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, hcl, hune, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hA hϕ hvl hX hcl
    rw [hv]
    refine three_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) ht ht1
      (by omega) (alignIdx X') hdomI _ ?_
    rw [← hv, ← hhead]
    exact winSet_alignROmegaClass_ne (q := (h.1, lab)) hd hune
  have hG1' : decGroup n (alignPairG1 (h.1, h.2.1)) = Dd.toAlignDominant.Gs := hG1.trans hDGs.symm
  have hker : decGroup n (adKG h) = Dd.ker := hDker.symm
  have hwin : winSet n (adWindow h) = Dd.toAlignDominant.window := hDwin.symm
  have hmsm : alignRMs (h.1, h.2.1) ≤ h.1.2.1.length := by
    have := Dd.toAlignDominant.param_halved
    rw [hDm, hDms] at this
    rw [hg]
    omega
  have hspec := line4dDomEnum_spec (h := h) hd (by omega) hG1' hker hwin hDms hmsm
  let S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) :=
    { m := m, ϕ := ϕ, act := inst, Vers := fun _ => {Z | Z ∈ Ys}, finY := Ys.finite_toSet,
      X' := X', head := head, tail := tail, dom := some Dd, versions := Ys,
      domEnum := line4dDomEnum n h Dd }
  have hdd : ∀ D, S.dom = some D → (D.toAlignDominant.Gs = preimageSubgroup ϕ (structAut X') ∧
      D.toAlignDominant.window = S.head) := fun D' hD' => by
    have he : D' = Dd := (Option.some.inj hD').symm
    subst he
    exact ⟨hDGs, by rw [hDwin]; rfl⟩
  have hee : ∀ D, S.dom = some D → S.domEnum.Spec D := fun D' hD' => by
    have he : D' = Dd := (Option.some.inj hD').symm
    subst he
    exact hspec
  have hrun := S.run_red_of_transport hne hcover hinv hdd hee hT
  have hwne : Dd.toAlignDominant.window.Nonempty := by
    rw [← hwin]
    show (winSet n domWin).Nonempty
    rw [← hheaddef, hhead, ← hset]
    exact omegaOf_nonempty_of_tPoint hϕ hvl ht ⟨0, by omega⟩ (by omega)
  have htailW : ((alignRWindows (alignRColorOf (h.1, h.2.1))).tail).map (winSet n) = tail := by
    show ((alignRWindows (h.1, lab)).tail).map (winSet n) = tail
    rw [hW]
    rfl
  have hlargeOf : l57Small h = false → alignRLarge (h.1, h.2.1) = true := by
    intro hs
    have hs' : alignRSmall (h.1, h.2.1) = false := by
      rw [← l57Small_eq_of_two_le (h := h) hnt]; exact hs
    unfold alignRSmall at hs'
    unfold alignRLarge
    rw [hhd] at hs' ⊢
    simpa using hs'
  refine ⟨S, fun hs => ?_, fun hs => ?_, hrun, S.calls_coset_of_facts hne hinv hdd hee,
    fun hl J hJ => ?_, fun hl => ?_, fun k hxk hyk => ?_⟩
  · -- case 1
    have hsmall : ¬ Dd.LargeParam := (l57Small_iff (h := h) hd hhd hDms hG1' hnt).1 hs
    have hnl := alignRLarge_false_of_l57Small hs
    refine ⟨Dd, ADDescribes.mk' (h := h) (S := S) hd hw hs hwin hwne rfl hsmall hne hDGs hspec
      hker rfl ?_ ?_ hinvTail hA hϕ hK hX hYs hrun⟩
    · show (h.2.2.2.1.tail).map (winSet n) = tail
      rw [hw, alignL57Windows_of_not hnl]
      exact htailW
    · exact line4dDomEnum_reps (h := h) (Ys := Ys) hA hϕ hK hX hYs hx hs Dd
  · -- cases 2 and 3
    have hlarge := hlargeOf hs
    have hL' : Dd.LargeParam :=
      (largeParam_iff (n := n) (p := (h.1, h.2.1)) (D := Dd) hd hhd hDms hG1').2 hlarge
    refine ⟨_, avDescribes_of_domLarge (h := h) (S := S) hw hlarge rfl hL' hne hDGs hG1' hwin
      hspec rfl htailW ?_ hd ?_ hA hϕ hK hX hYs hinvTail hrun⟩
    · obtain ⟨u, hu⟩ := hwne
      have hmem := orbit_mem_orbitListOn Dd.isInvariant_window hu
      have hmem' := hspec.orbits.symm.subset hmem
      intro he
      have he1 : (line4dDomEnum n h Dd).orbits = [] := (List.append_eq_nil_iff.1 he).1
      rw [he1] at hmem'
      exact List.not_mem_nil hmem'
    · intro W hWm u hu
      have := lt_of_mem_of_mem_alignRWindows hWm hu
      rw [← hd]
      exact this
  · -- no test: case 1, whose calls carry no hint
    have hs : l57Small h = true := by
      cases hs : l57Small h
      · exact absurd ((hlargeOf hs).symm.trans hl) (by simp)
      · rfl
    have hsmall : ¬ Dd.LargeParam := (l57Small_iff (h := h) hd hhd hDms hG1' hnt).1 hs
    rcases S.calls_progress_of_facts hne hinv hdd hee (fun Δ hΔ hne' => by
      rcases hne' with hne' | hne'
      · rcases List.mem_cons.1 hΔ with rfl | hΔ
        · exact absurd rfl hne'
        · exact hsizes Δ hΔ
      · simp [S] at hne') J hJ with h5 | hh
    · simpa using h5
    · exfalso
      rw [alignShape_hint_eq_none_of_dom_small S rfl hsmall] at hh
      simp at hh
  · -- the test: the facts of the hinted call
    have hgs : RawGens.WF n (alignPairG1 (h.1, h.2.1)) := alignPairG1_wf hd
    have hlt : ∀ j ∈ adWindow h, j < n := fun j hj => adWindow_lt hd hj
    refine ⟨by rw [hG1]; exact preimageSubgroup_le _ _, ?_, ?_, hnt,
      ((alignRLarge_iff hgs hd).1 hl).2⟩
    · rw [rawIsInvariant_eq_true_iff hgs hlt]
      have := Dd.isInvariant_window
      rw [← hwin, ← hG1'] at this
      exact this
    · intro W hWm
      have hmem : winSet n W ∈ tail := by
        rw [← htailW]; exact List.mem_map_of_mem hWm
      simpa using hsizes3 _ hmem
  · -- the letters
    cases hs : l57Small h
    · have hL' : Dd.LargeParam :=
        (largeParam_iff (n := n) (p := (h.1, h.2.1)) (D := Dd) hd hhd hDms hG1').2 (hlargeOf hs)
      exact alignShape_letters_of_dom_large S hne rfl hL' hxk hyk
    · exact alignShape_letters_of_dom_small S hne rfl
        ((l57Small_iff (h := h) hd hhd hDms hG1' hnt).1 hs) hxk hyk

/-- §14.1 at lines 5–7 of §15, **the round of Procedure Align the header describes**, in all
three cases of line 6 and line 7 (`Algo.alignL57Shape_noDom`, `Algo.alignL57Shape_trivDom`,
`Algo.alignL57Shape_dom`). -/
theorem exists_alignL57Shape : ∃ S, L57ShapeOK n h S := by
  cases hhd : alignRHasDom (alignRColorOf (h.1, h.2.1))
  · exact alignL57Shape_noDom hA hG hϕ hvl ht hK hX hα hα45 hZ hm hmn hYs hw hx hT hhd
  · rcases Nat.lt_or_ge (alignRMs (h.1, h.2.1)) 2 with hms | hnt
    · exact alignL57Shape_trivDom hA hG hϕ hvl ht hK hX hα hα45 hZ hm hmn hYs hw hx hT hhd hms
    · exact alignL57Shape_dom hA hG hϕ hvl ht hK hX hα hα45 hZ hm hmn hYs hw hx hT hhd hnt

end Shape

end Algo
