/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 7–11, item 3 of the repair (§14.1) — the
Johnson hint of the dominant-orbit call, and its meaning.
-/
import Workspace.Algo.PrimitiveLine4dDomData
import Workspace.Algo.TopMasterRecursionCameron
import Workspace.Algo.TopMasterStandardLink

/-!
# The Johnson hint of the dominant-orbit call has its meaning

In case 3 of the repair of lines 7–11 of Procedure Align (`m*` above the threshold of
Theorem 10.5.1), the round is the Chain Rule over the orbits of `G*` in the dominant window,
the dominant orbit `Δ₁` first, and the first call carries the Johnson case data
`Babai.AlignDominantOrbit.johnsonCaseData`: the giant representation `ϕ* : G*^{Δ₁} → S(Γ*)`
and the standard blocks of Theorem 10.5.1 (e).

On the machine the hint of that call is `Algo.alignDomHint` (`Workspace/Algo/AlignDomHint.lean`):
the rows `ψ(σ)` of the generators of `G*` and the size of `T(x)` at the first point of the
window.  This file proves that the hint has the meaning the Master Algorithm reads off a
hinted node (`Algo.MasterHintGood`):

* `Algo.masterHintGoodAt_of_giant` — a raw action whose rows are the images of a giant
  representation of a transitive group, with the numeric hypothesis of Theorem 10.5.1 and an
  affected point, is a good hint at that point, with the standard blocks of Theorem 10.5.1 (e);
* `Algo.exists_transportRep` — a representation of a group `K ≤ S(β)` read on its copy in
  `S(Fin N)` through a bijection `Fin N ≃ β`;
* `Algo.alignDomHint_good` — **the main statement**: the hint the machine builds for the
  dominant orbit is good, its parameter is the machine's `m*`, and `2m* ≤ m` (Eq. (73)).

The representation of the hint is `ϕ*` read on `G*^{Δ₁}` (`Babai.restrictFactor`), with `Γ*`
numbered by the machine's list of its points: the machine's `ψ` is `ϕ*` up to that numbering
(`Algo.exists_domRoundData`), and `Algo.MasterHintGood` asks only for some giant
representation with the stored rows.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-! ## Relabelling the target of a representation -/

section Relabel

/-- Relabelling `S(Fin a)` as `S(Fin b)` along `f : Fin a ≃ Fin b` carries the alternating
group onto the alternating group: it keeps the sign. -/
theorem map_alternatingGroup_permCongrHom {a b : ℕ} (f : Fin a ≃ Fin b) :
    (alternatingGroup (Fin a)).map (permCongrHom f).toMonoidHom = alternatingGroup (Fin b) := by
  ext σ
  simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [permCongrHom_coe, Equiv.Perm.sign_permCongr, hτ]
  · intro hσ
    refine ⟨f.symm.permCongr σ, ?_, ?_⟩
    · rw [Equiv.Perm.sign_permCongr, hσ]
    · rw [permCongrHom_coe]
      exact f.permCongr.apply_symm_apply σ

variable {Ω : Type*} {G : Subgroup (Perm Ω)} {a b : ℕ} (f : Fin a ≃ Fin b)
  (ρ : G →* Perm (Fin a))

/-- A giant representation stays one when its target is relabelled. -/
theorem isGiantRep_permCongr (h : IsGiantRep ρ) :
    IsGiantRep ((permCongrHom f).toMonoidHom.comp ρ) := by
  unfold IsGiantRep at h ⊢
  rw [MonoidHom.range_comp, ← map_alternatingGroup_permCongrHom f]
  exact Subgroup.map_mono h

/-- A point is affected by a representation exactly when it is affected by its relabelling. -/
theorem affected_permCongr (x : Ω) :
    Affected ((permCongrHom f).toMonoidHom.comp ρ) x ↔ Affected ρ x := by
  unfold Affected
  rw [← Subgroup.map_map, ← map_alternatingGroup_permCongrHom f,
    Subgroup.map_le_map_iff_of_injective (permCongrHom f).injective]

end Relabel

/-! ## A representation read through a bijection of the domains -/

section Transport

variable {β : Type*} [Fintype β] [DecidableEq β] {N M : ℕ}

/-- **A representation of `K ≤ S(β)` read on its copy in `S(Fin N)`.**  If `H` is the image of
`K` under the relabelling along `e : Fin N ≃ β`, a representation `ψ` of `K` gives one of `H`
that agrees with `ψ` on relabelled elements, is giant if `ψ` is, has the affected points of `ψ`
(read through `e`), and `H` is transitive if `K` is. -/
theorem exists_transportRep (e : Fin N ≃ β) (K : Subgroup (Perm β))
    (ψ : K →* Perm (Fin M)) (H : Subgroup (Perm (Fin N)))
    (hH : H = K.map (e.symm.permCongrHom).toMonoidHom) :
    ∃ ϕ' : H →* Perm (Fin M),
      (∀ (g : K) (h : e.symm.permCongr (g : Perm β) ∈ H), ϕ' ⟨_, h⟩ = ψ g) ∧
      (IsGiantRep ψ → IsGiantRep ϕ') ∧
      (∀ x : Fin N, Affected ψ (e x) → Affected ϕ' x) ∧
      (IsTransitive K → IsTransitive H) := by
  subst hH
  have hinj : Function.Injective (e.symm.permCongrHom).toMonoidHom :=
    (e.symm.permCongrHom).injective
  set E := K.equivMapOfInjective _ hinj with hE
  have hEg : ∀ g : K, ((E g : K.map (e.symm.permCongrHom).toMonoidHom) : Perm (Fin N)) =
      e.symm.permCongr (g : Perm β) := fun g => rfl
  refine ⟨ψ.comp E.symm.toMonoidHom, fun g h => ?_, fun hg => ?_, fun x hx => ?_,
    fun ht => isTransitive_map_permCongrHom e.symm ht⟩
  · have : (⟨e.symm.permCongr (g : Perm β), h⟩ : K.map (e.symm.permCongrHom).toMonoidHom) =
        E g := Subtype.ext (hEg g).symm
    rw [MonoidHom.comp_apply, this, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  · exact isGiantRep_comp_mulEquiv E.symm hg
  · intro hle
    apply hx
    refine hle.trans ?_
    rintro _ ⟨h', hh', rfl⟩
    refine ⟨E.symm h', ?_, rfl⟩
    have hh'' : h' ∈ stabilizer (K.map (e.symm.permCongrHom).toMonoidHom) x := hh'
    show E.symm h' ∈ stabilizer K (e x)
    rw [mem_stabilizer_iff] at hh'' ⊢
    have h1 : ((h' : Perm (Fin N))) x = x := hh''
    have h2 : (h' : Perm (Fin N)) = e.symm.permCongr ((E.symm h' : K) : Perm β) := by
      rw [← hEg, MulEquiv.apply_symm_apply]
    rw [h2, Equiv.permCongr_apply, Equiv.symm_symm] at h1
    show ((E.symm h' : K) : Perm β) (e x) = e x
    have h3 := congrArg e h1
    rwa [Equiv.apply_symm_apply] at h3

end Transport

/-! ## A good hint from a giant representation -/

/-- §11.4 and Theorem 10.5.1 (a), (b), (e): **a good Johnson hint.**  Let the raw action `A`
carry a giant representation `ϕ` of a transitive group `G` on the window, with its rows, and
let the numeric hypothesis of Theorem 10.5.1 hold.  At an affected point `x`, the standard
blocks of Theorem 10.5.1 (e) make the hint `(A, t(x))` good: they are a system of
imprimitivity labelled by the `t`-subsets of `[m]` compatibly with `ϕ`
(`Algo.masterHintBlockLink_standard`), there are at least two of them, `1 ≤ t` (item (b)),
`4t < m` (item (a)), and `m ≤ |Δ|` because there are `C(m,t) ≥ m` disjoint nonempty blocks. -/
theorem masterHintGoodAt_of_giant {A : RawAction} {M : ℕ}
    (ϕ : decGroup A.1.1.length A.1.2 →* Perm (Fin M))
    (hwf : RawAction.WF A.1.1.length M A ϕ) (htr : IsTransitive (decGroup A.1.1.length A.1.2))
    (hg : IsGiantRep ϕ) (hvl : VeryLargeK M (maxOrbitLength (decGroup A.1.1.length A.1.2)))
    (x : Fin A.1.1.length) (haff : Affected ϕ x) (h64 : 64 ≤ A.1.1.length) :
    MasterHintGoodAt A (tPoint ϕ x) := by
  classical
  haveI : Nonempty (Fin A.1.1.length) := ⟨x⟩
  let G := decGroup A.1.1.length A.1.2
  have horb : orbit G x = Set.univ := (isTransitive_iff_orbit_eq_univ G).1 htr x
  have hsys := theorem_10_5_1_e_isSystem ϕ hg hvl x
  have hB : IsSystemOfImprimitivity G Set.univ (standardBlocks ϕ (orbit G x)) := by
    have h := hsys
    rw [horb] at h ⊢
    exact h
  have ht1 : 1 ≤ tPoint ϕ x := (theorem_10_5_1_b ϕ hg hvl x).1 haff
  have ht4 : 4 * tPoint ϕ x < M := (theorem_10_5_1_a ϕ hg hvl x).1.1
  have ht2 : 2 * tPoint ϕ x < M := by omega
  have hj : ActsAsJohnsonS G (standardBlocks ϕ (orbit G x)) hB.permutes M (tPoint ϕ x) ∨
      ActsAsJohnsonA G (standardBlocks ϕ (orbit G x)) hB.permutes M (tPoint ϕ x) := by
    obtain ⟨e, -, he⟩ := theorem_10_5_1_e_johnson ϕ hg hvl x
    exact he.symm.imp (fun h => ⟨e, h⟩) (fun h => ⟨e, h⟩)
  have hMN : M ≤ A.1.1.length := by
    have h := johnson_param_le_or ht1 ht2 hB hj
    rwa [Fintype.card_fin] at h
  exact ⟨M, ϕ, standardBlocks ϕ (orbit G x), hB, hwf, htr, hg,
    masterHintBlockLink_standard ϕ hg hvl x, two_blocks_of_actsAsJohnson_or ht1 ht2 hB hj,
    ht1, ht2, hMN, h64⟩

/-! ## The hint of the dominant-orbit call -/

section Main

theorem isTransitive_restrictTo_of_eq_orbit {n : ℕ} {G : Subgroup (Perm (Fin n))}
    {Δ : Set (Fin n)} {u : Fin n} (h : Δ = orbit G u) (hi : IsInvariant G Δ) :
    IsTransitive (restrictTo G Δ hi) := by
  subst h
  exact isTransitive_restrictTo_orbit hi

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}
  [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- §14.1, lines 7–11, item 3 of the repair, on the machine: **the Johnson hint of the
dominant-orbit call is good.**  Let line 6 find a dominant class with nontrivial structure
(`2 ≤ m*`), let `m*` be above the threshold of Theorem 10.5.1 (case 3), and let the call
window `W` be an orbit `Δ₁ = u^{G*}` of `G*` (the group of the machine's generators
`Algo.alignPairG1`) with `u` in the dominant window and `|Δ₁| > 2n/3`.  Then the hint
`Algo.alignDomHint` the machine builds for `W` has the meaning `Algo.MasterHintGood`; its
Johnson parameter is the machine's `m*`, and `2m* ≤ m` (Eq. (73)).

The representation of the hint is `ϕ*` read on `G*^{Δ₁}` (`Babai.restrictFactor`, possible
because the pointwise stabilizer of `Δ₁` lies in `ker ϕ*`), with `Γ*` numbered by the machine's
list of its points; the standard blocks of Theorem 10.5.1 (e) give the rest
(`Algo.masterHintGoodAt_of_giant`). -/
theorem alignDomHint_good (hA : RawAction.WF n m A ϕ) (hG : IsTransitive (decGroup n A.1.2))
    (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup n A.1.2))) {t : ℕ}
    (ht : ∀ u : Fin n, tPoint ϕ u = t) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    (hZ : IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m) (hmn : m ≤ n)
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hnt : 2 ≤ alignRMs (A, o))
    (hLP : VeryLargeK (alignRMs (A, o)) (maxOrbitLength (decGroup n (alignPairG1 (A, o)))))
    {W : RawWinSI} (hWg : W.2.1 = alignPairG1 (A, o))
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n) {u : Fin n}
    (hu : u ∈ winSet n (alignRDomWindow (alignRColorOf (A, o),
      alignRDomColor (alignRColorOf (A, o)))))
    (horb : winSet n W.1 = orbit (decGroup n (alignPairG1 (A, o))) u)
    (hbig : 2 * n < 3 * W.1.length) :
    MasterHintGood (W, alignDomHint ((A, o), W)) ∧
      (alignDomHint ((A, o), W)).1.1.length = alignRMs (A, o) ∧
      2 * alignRMs (A, o) ≤ m := by
  obtain ⟨Dd, hDm, hDGs, hDwin, hDms, -, f, hf⟩ :=
    exists_domRoundData hA hG hϕ hvl ht hK hX hZ hm hmn hhd hnt
  have hd : A.1.1.length = n := hA.1
  have hGs : decGroup n (alignPairG1 (A, o)) = Dd.toAlignDominant.Gs :=
    (decGroup_alignPairG1 hA hϕ hK hX).trans hDGs.symm
  have hGsW : decGroup n W.2.1 = Dd.toAlignDominant.Gs := by rw [hWg]; exact hGs
  have hwfW : RawGens.WF n W.2.1 := by rw [hWg]; exact alignPairG1_wf hd
  have hinv0 : IsInvariant (decGroup n W.2.1) (winSet n W.1) := by
    rw [horb, hWg]; exact isInvariant_orbit' _ u
  have hinv : IsInvariant Dd.toAlignDominant.Gs (winSet n W.1) := by
    rw [← hGsW]; exact hinv0
  have hLP' : Dd.LargeParam := by
    show VeryLargeK Dd.toAlignDominant.ms (maxOrbitLength Dd.toAlignDominant.Gs)
    rw [hDms, ← hGs]; exact hLP
  have hu' : u ∈ Dd.toAlignDominant.window := by rw [hDwin]; exact hu
  have horb' : winSet n W.1 = orbit Dd.toAlignDominant.Gs u := by rw [horb, hGs]
  have hN : W.1.length = (orbit Dd.toAlignDominant.Gs u).ncard := by
    rw [← horb', ncard_winSet W.1 hnd hlt]
  have hbig' : 2 * Fintype.card (Fin n) < 3 * (orbit Dd.toAlignDominant.Gs u).ncard := by
    rw [Fintype.card_fin, ← hN]; exact hbig
  let c := Dd.dominantOrbit hLP' hu' hbig'
  have hstab : pointwiseStab Dd.toAlignDominant.Gs (winSet n W.1) ≤
      Dd.toAlignDominant.phis.ker := by
    rw [horb']; exact c.stab_le
  have hMs : (alignDomKeys (A, o)).length = Dd.toAlignDominant.ms := by
    simpa using Fintype.card_congr f
  let K := restrictTo Dd.toAlignDominant.Gs (winSet n W.1) hinv
  let ψ : K →* Perm (Fin (alignDomKeys (A, o)).length) :=
    (permCongrHom f.symm).toMonoidHom.comp (restrictFactor hinv Dd.toAlignDominant.phis hstab)
  let e := winEquiv n W.1 hnd hlt
  have hH : decGroup W.1.length (primitiveWindowInput W).1 =
      K.map (e.symm.permCongrHom).toMonoidHom := by
    have h1 := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hwfW hnd hlt hinv0
    rw [range_winRestrictHom, restrictTo_congr hGsW hinv0 hinv] at h1
    exact h1
  obtain ⟨ϕ', hϕ'1, hϕ'2, hϕ'3, hϕ'4⟩ := exists_transportRep e K ψ _ hH
  -- the generators of the call
  have hτ0 : ∀ r ∈ W.2.1, decPerm n r ∈ decGroup n W.2.1 := fun r hr =>
    Subgroup.subset_closure (List.mem_map_of_mem hr)
  have hτGs : ∀ r ∈ W.2.1, decPerm n r ∈ Dd.toAlignDominant.Gs := fun r hr => by
    rw [← hGsW]; exact hτ0 r hr
  have hτG : ∀ r ∈ W.2.1, decPerm n r ∈ decGroup n A.1.2 := fun r hr => by
    have h := hτGs r hr
    rw [hDGs] at h
    exact (mem_preimageSubgroup.1 h).1
  have hrow : ∀ r (hr : r ∈ W.2.1), alignDomPsi ((A, o), rawImgOf (A, r)) =
      encPerm _ (Equiv.permCongr f.symm
        (Dd.toAlignDominant.phis ⟨decPerm n r, hτGs r hr⟩)) := fun r hr => by
    rw [aggnRawImgOf_spec hA (hwfW r hr) (hτG r hr)]
    exact hf _ (hτGs r hr) (hτG r hr)
  have hres : ∀ r (hr : r ∈ W.2.1), rawRestrictPerm (W.1, r) = encPerm W.1.length
      (e.symm.permCongr ((restrictOnto hinv ⟨decPerm n r, hτGs r hr⟩ : K) :
        Perm ↥(winSet n W.1))) := fun r hr => by
    have h := rawRestrictPerm_spec hnd hlt hinv0 (hτ0 r hr)
    rw [encPerm_decPerm (hwfW r hr)] at h
    exact h
  have hψ : ∀ g : Dd.toAlignDominant.Gs, ψ (restrictOnto hinv g) =
      Equiv.permCongr f.symm (Dd.toAlignDominant.phis g) := fun g => by
    show (permCongrHom f.symm) (restrictFactor hinv Dd.toAlignDominant.phis hstab
      (restrictOnto hinv g)) = _
    rw [restrictFactor_restrictOnto]
    rfl
  have key : ∀ r (hr : r ∈ W.2.1)
      (hmem : decPerm W.1.length (rawRestrictPerm (W.1, r)) ∈
        decGroup W.1.length (primitiveWindowInput W).1),
      decPerm (alignDomKeys (A, o)).length (alignDomPsi ((A, o), rawImgOf (A, r))) =
        ϕ' ⟨_, hmem⟩ := fun r hr hmem => by
    rw [hrow r hr, decPerm_encPerm]
    have e1 : decPerm W.1.length (rawRestrictPerm (W.1, r)) =
        e.symm.permCongr ((restrictOnto hinv ⟨decPerm n r, hτGs r hr⟩ : K) :
          Perm ↥(winSet n W.1)) := by
      rw [hres r hr, decPerm_encPerm]
    have e2 : (⟨_, hmem⟩ : decGroup W.1.length (primitiveWindowInput W).1) =
        ⟨_, e1 ▸ hmem⟩ := Subtype.ext e1
    rw [e2, hϕ'1, hψ]
  -- the action of the hint is well formed
  have hrg : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hwfW hnd hlt hinv0
  have hrows : RawGens.WF (alignDomKeys (A, o)).length (alignDomHintRows ((A, o), W.2.1)) := by
    intro r' hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    rw [hrow r hr]
    exact wf_encPerm _ _
  have hI : ImgsOf (((primitiveWindowInput W).1).map (decPerm W.1.length))
      ((alignDomHintRows ((A, o), W.2.1)).map (decPerm (alignDomKeys (A, o)).length)) ϕ' := by
    refine ⟨by simp [primitiveWindowInput, rawRestrictGens, alignDomHintRows], ?_⟩
    intro i hi hi'
    have hiW : i < W.2.1.length := by
      simpa [primitiveWindowInput, rawRestrictGens] using hi
    simp only [primitiveWindowInput, rawRestrictGens, alignDomHintRows, List.getElem_map]
    exact key _ (List.getElem_mem hiW) _
  have hwf : RawAction.WF W.1.length (alignDomKeys (A, o)).length
      (alignDomHintAction ((A, o), W)) ϕ' := ⟨rfl, rfl, hrg, hrows, hI⟩
  -- the numeric facts
  have hgiant : IsGiantRep ϕ' := hϕ'2 (isGiantRep_permCongr f.symm _
    (isGiantRep_restrictFactor hinv _ hstab Dd.toAlignDominant.isGiantRep_phis))
  have htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) :=
    hϕ'4 (isTransitive_restrictTo_of_eq_orbit horb' hinv)
  have hvl' : VeryLargeK (alignDomKeys (A, o)).length
      (maxOrbitLength (decGroup W.1.length (primitiveWindowInput W).1)) := by
    rw [hMs]
    refine VeryLargeK.mono hLP' (maxOrbitLength_le fun x => ?_)
    refine (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hN, ← Nat.card_coe_set_eq]
    exact card_orbit_le_maxOrbitLength _ u
  have hpos : 0 < W.1.length := by omega
  let x0 : Fin W.1.length := ⟨0, hpos⟩
  have haff : Affected ϕ' x0 := by
    apply hϕ'3 x0
    rw [affected_permCongr, affected_restrictFactor]
    have hmem : ((e x0 : ↥(winSet n W.1)) : Fin n) ∈ orbit Dd.toAlignDominant.Gs u := by
      rw [← horb']; exact (e x0).2
    exact c.affected _ hmem
  have h64 : 64 ≤ W.1.length := by omega
  have hgood := masterHintGoodAt_of_giant (A := alignDomHintAction ((A, o), W)) ϕ' hwf htr
    hgiant hvl' x0 haff h64
  -- the parameter the machine computes is `t(x₀)`
  have htx : (alignDomHint ((A, o), W)).2 = tPoint ϕ' x0 := by
    have h := length_filter_rawTpoint (dom := W.1) (gdom := alignDomKeys (A, o)) rfl rfl hI
      hgiant hvl' x0 (fun _ => true)
    rw [map_encPerm_decPerm hrg, map_encPerm_decPerm hrows, List.filter_true] at h
    show (rawTpoint (alignDomHintAction ((A, o), W), 0)).length = _
    rw [tPoint]
    convert h using 2
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
    exact Iff.rfl
  refine ⟨?_, hMs.trans hDms, ?_⟩
  · show MasterHintGoodAt (alignDomHintAction ((A, o), W)) (alignDomHint ((A, o), W)).2
    rw [htx]
    exact hgood
  · rw [← hDms, ← hDm]
    exact Dd.toAlignDominant.param_halved

end Main

end Algo
