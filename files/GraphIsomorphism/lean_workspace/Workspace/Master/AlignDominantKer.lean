/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, lines 7–10: `m*` and `ker ϕ*` of the data of lines 7–11, read off the outcome of
Theorem 9.2.3.
-/
import Workspace.Master.Line4cd

/-!
# `m*` and `ker ϕ*` of the round of lines 7–11

> 7. (A) … `Γ*` the set of blocks
>    (B) … identify `Δ_j` with `(Γ* choose t*)`, `|Γ*| = m*`
> 8. let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural epimorphism
> 9. let `G* = ϕ⁻¹(H)`
> 10. let `ϕ* = ψ ∘ ϕ|_{G*}`

`Babai.exists_alignDominantRoundData` builds the data of lines 7–11 and says what its group
`G*` and its window are. The machine (`Workspace/Algo/AlignDom*.lean`) also computes `m*` and
generators of `ker ϕ*`, and to compare its round with the Master's it needs these two
quantities of the Master's data. This file states them, one theorem per case of line 7:

* case (A) (`Babai.exists_alignDominantRoundData_A`): `m*` blocks of a common size make up the
  dominant class, and `τ ∈ ker ϕ*` exactly when `ϕ(τ) ∈ Aut(X')` maps every block inside the
  dominant class to itself;
* case (B) (`Babai.exists_alignDominantRoundData_B`): `m*` is the degree `k` of the given
  identification `Δ_j ≅ ([k] choose t*)`, and `τ ∈ ker ϕ*` exactly when `ϕ(τ) ∈ Aut(X')` fixes
  every point of `Δ_j`.

Both rest on `Babai.AlignDominant.mem_kerSubgroup_phis`: `τ ∈ ker ϕ*` exactly when
`τ ∈ G`, `ϕ(τ) ∈ H` and `ψ(ϕ(τ)) = 1`. The statements add clauses to
`Babai.exists_alignDominantRoundData`; they change no statement of the paper.
-/

universe u

namespace Babai

open Equiv MulAction

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- §14.1, line 10: **`ker ϕ*`**, with `ϕ* = ψ ∘ ϕ|_{G*}`: `τ ∈ ker ϕ*` exactly when `τ ∈ G`,
`ϕ(τ) ∈ H` and `ψ(ϕ(τ)) = 1`. -/
theorem AlignDominant.mem_kerSubgroup_phis (D : AlignDominant Ω) {τ : Perm Ω} :
    τ ∈ kerSubgroup D.phis ↔ ∃ h : τ ∈ D.G, ∃ hH : D.ϕ ⟨τ, h⟩ ∈ D.H, D.ψ ⟨_, hH⟩ = 1 := by
  rw [mem_kerSubgroup]
  constructor
  · rintro ⟨hs, h1⟩
    obtain ⟨hG, hH⟩ := mem_preimageSubgroup.1 hs
    exact ⟨hG, hH, h1⟩
  · rintro ⟨hG, hH, h1⟩
    exact ⟨mem_preimageSubgroup.2 ⟨hG, hH⟩, h1⟩

/-! ## Case (A) -/

section CaseA

variable {m : ℕ} {κ : Type}

/-- §14.1, line 8, case (A): **`ψ(h) = 1` exactly when `h` maps every block inside the
dominant class to itself.** -/
theorem domPsi_eq_one_iff {R : ColoredPartition (Fin m) κ} {j : κ} {γ₀ : Fin m}
    (h₀ : R.color γ₀ = j) {h : Perm (Fin m)} (hh : h ∈ partAut R) :
    domPsi h₀ ⟨h, hh⟩ = 1 ↔ ∀ γ, R.color γ = j → R.part (h γ) γ := by
  rw [domPsi_apply h₀ hh]
  constructor
  · intro h1 γ hγ
    have hhγ : R.color (h γ) = j := by rw [(mem_partAut.1 hh).1 γ]; exact hγ
    have he := domBlockMap_apply_perm h₀ hh hγ
    rw [h1, Equiv.Perm.one_apply] at he
    exact (part_iff_domBlockMap_eq h₀ hhγ hγ).2 he
  · intro hfix
    refine Equiv.ext fun b => Subtype.ext ?_
    obtain ⟨S, δ, hδ, rfl⟩ := b
    show h '' R.block δ = R.block δ
    rw [image_block_partAut hh δ]
    exact R.block_eq_of_part (hfix δ hδ)

variable {G : Subgroup (Perm Ω)}

/-- §14.1, lines 7–10, case (A): `m*` and `ker ϕ*` of `Babai.alignDominantABlocks_of`. -/
theorem alignDominantABlocks_of_ms_ker (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hgiant : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ)
    (ht : ∀ u : Ω, tPoint ϕ u = t)
    {R : ColoredPartition (Fin m) κ} (hequi : R.IsEquipartition) {j : κ} {γ₀ : Fin m}
    (h₀ : R.color γ₀ = j) (hdom : m < 2 * (R.colorClass j).ncard)
    (hblk2 : 2 ≤ (R.block γ₀).ncard)
    (htwo : ∃ γ δ, R.color γ = j ∧ R.color δ = j ∧ ¬ R.part δ γ) :
    letI D := (alignDominantABlocks_of G hG ϕ hgiant hvl t ht hequi h₀ hdom hblk2
      htwo).toAlignDominantA.toAlignDominant
    D.ms * (R.block γ₀).ncard = (R.colorClass j).ncard ∧
      ∀ τ : Perm Ω, τ ∈ kerSubgroup D.phis ↔
        ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ ∈ partAut R ∧ ∀ γ, R.color γ = j → R.part (ϕ ⟨τ, h⟩ γ) γ := by
  refine ⟨?_, fun τ => ?_⟩
  · show Fintype.card (domBlocks R j) * _ = _
    rw [ncard_colorClass_eq_mul h₀ hequi]
  · rw [AlignDominant.mem_kerSubgroup_phis]
    constructor
    · rintro ⟨hG', hH, h1⟩
      refine ⟨hG', hH, ?_⟩
      have h2 : domPsi h₀ ⟨_, hH⟩ = 1 :=
        (MulEquiv.map_eq_one_iff (Equiv.permCongrHom (Fintype.equivFin (domBlocks R j)))).1 h1
      exact (domPsi_eq_one_iff h₀ hH).1 h2
    · rintro ⟨hG', hH, hfix⟩
      refine ⟨hG', hH, ?_⟩
      show (Equiv.permCongrHom (Fintype.equivFin (domBlocks R j))) (domPsi h₀ ⟨_, hH⟩) = 1
      rw [(domPsi_eq_one_iff h₀ hH).2 hfix, map_one]

variable [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- §14.1, **lines 6–10, case (A)**, built from the outcome of Theorem 9.2.3: the data of
`Babai.exists_alignDominantRoundData`, together with **`m*`** (the dominant class is the union
of `m*` blocks of the size of the block of `x`) and **`ker ϕ*`** (the `τ ∈ G` with
`ϕ(τ) ∈ Aut(X')` mapping every block inside the dominant class to itself). -/
theorem exists_alignDominantRoundData_A (hK : IsCatAction (SplitOutcomes (Fin m)))
    (hG : IsTransitive G) (ϕ : G →* Perm (Fin m)) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ) (ht : ∀ u : Ω, tPoint ϕ u = t)
    {s : Set (Fin m)} (hs : s = Set.univ) (P : ColoredPartition ↥s ℕ) {j : ℕ × ℕ}
    (hdom : m < 2 * (colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inl j)).card)
    {x y : ↥s} (hx : P.equipartRefine.color x = j) (hy : P.equipartRefine.color y = j)
    (hxy : ¬ P.part y x)
    (hblk : ∀ z : ↥s, P.equipartRefine.color z = j → 2 ≤ (P.block z).ncard)
    (hn : 96 ≤ Fintype.card Ω) :
    ∃ D : AlignDominantRoundData Ω,
      D.toAlignDominant.m = m ∧
      D.toAlignDominant.Gs
        = preimageSubgroup ϕ (structAut (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))) ∧
      D.toAlignDominant.window = omegaOf ϕ ((colorSet (alignColor
        (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))) (Sum.inl j) : Finset (Fin m)) :
          Set (Fin m)) ∧
      D.toAlignDominant.ms * (P.block x).ncard = (colorSet (alignColor
        (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))) (Sum.inl j)).card ∧
      (∃ blk : Fin m → Fin D.toAlignDominant.ms,
        (∀ γ δ, (alignPart hs P).color γ = j → (alignPart hs P).color δ = j →
          (blk γ = blk δ ↔ (alignPart hs P).part γ δ)) ∧
        (∀ i, ∃ γ, (alignPart hs P).color γ = j ∧ blk γ = i) ∧
        ∀ τ (hτ : τ ∈ D.toAlignDominant.Gs) (hG : τ ∈ G) γ, (alignPart hs P).color γ = j →
          blk (ϕ ⟨τ, hG⟩ γ) = D.toAlignDominant.phis ⟨τ, hτ⟩ (blk γ)) ∧
      ∀ τ : Perm Ω, τ ∈ D.ker ↔ ∃ h : τ ∈ G,
        ϕ ⟨τ, h⟩ ∈ structAut (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))) ∧
        ∀ γ, (alignPart hs P).color γ = j → (alignPart hs P).part (ϕ ⟨τ, h⟩ γ) γ := by
  classical
  have hspec := alignDominantABlocks_ofOutcome_spec hK G hG ϕ hgiant hvl t ht hs P hdom
    hx hy hxy hblk
  refine ⟨(alignDominantABlocks_ofOutcome G hG ϕ hgiant hvl t ht hs P hdom hx hy hxy
    hblk).toAlignDominantA.roundData hn, rfl, hspec.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · show omegaOf _ _ = _
    congr 1
    exact hspec.2.2.2.2.1
  · -- `alignDominantABlocks_ofOutcome` is `alignDominantABlocks_of` at `alignPart hs P`
    have hx' : (alignPart hs P).color (x : Fin m) = j := by
      rw [alignPart_color hs P (x : Fin m) x.2,
        show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
      exact hx
    have hmk := (alignDominantABlocks_of_ms_ker hG ϕ hgiant hvl t ht
      (isEquipartition_alignPart hs P) hx' (by
        rw [← colorSet_alignColor_eq_colorClass hs P j, Set.ncard_coe_finset]; exact hdom)
      (by rw [ncard_block_alignPart hs P (x : Fin m) x.2,
            show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]; exact hblk x hx)
      (by
        refine ⟨(x : Fin m), (y : Fin m), hx', ?_, ?_⟩
        · rw [alignPart_color hs P (y : Fin m) y.2,
            show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl]
          exact hy
        · rw [alignPart_part hs P y.2 x.2, show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl,
            show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
          exact hxy)).1
    have hb : (P.block x).ncard = ((alignPart hs P).block (x : Fin m)).ncard := by
      rw [ncard_block_alignPart hs P (x : Fin m) x.2]
    rw [hb, ← Set.ncard_coe_finset, colorSet_alignColor_eq_colorClass hs P j]
    exact hmk
  · -- the block map, numbered: `ψ` is the action on the blocks (line 8)
    set XA := (alignDominantABlocks_ofOutcome G hG ϕ hgiant hvl t ht hs P hdom hx hy hxy
      hblk) with hXA
    have hx' : (alignPart hs P).color (x : Fin m) = j := by
      rw [alignPart_color hs P (x : Fin m) x.2,
        show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
      exact hx
    refine ⟨XA.toAlignDominantA.block, fun γ δ hγ hδ => ?_, fun i => ?_,
      fun τ hτ hG γ hγ => ?_⟩
    · show XA.enum (domBlockMap hx' γ) = XA.enum (domBlockMap hx' δ) ↔ _
      rw [XA.enum.injective.eq_iff]
      exact (part_iff_domBlockMap_eq hx' hγ hδ).symm
    · obtain ⟨⟨S, δ, hδ, rfl⟩, hb⟩ : ∃ b, XA.enum b = i := ⟨XA.enum.symm i, by simp⟩
      refine ⟨δ, hδ, ?_⟩
      rw [← hb]
      show XA.enum (domBlockMap hx' δ) = _
      congr 1
      exact Subtype.ext (domBlockMap_of_mem hx' hδ)
    · exact XA.toAlignDominantA.psi_block (phiStar ϕ XA.H ⟨τ, hτ⟩) γ hγ
  · intro τ
    have hx' : (alignPart hs P).color (x : Fin m) = j := by
      rw [alignPart_color hs P (x : Fin m) x.2,
        show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
      exact hx
    have hmk := (alignDominantABlocks_of_ms_ker hG ϕ hgiant hvl t ht
      (isEquipartition_alignPart hs P) hx' (by
        rw [← colorSet_alignColor_eq_colorClass hs P j, Set.ncard_coe_finset]; exact hdom)
      (by rw [ncard_block_alignPart hs P (x : Fin m) x.2,
            show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]; exact hblk x hx)
      (by
        refine ⟨(x : Fin m), (y : Fin m), hx', ?_, ?_⟩
        · rw [alignPart_color hs P (y : Fin m) y.2,
            show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl]
          exact hy
        · rw [alignPart_part hs P y.2 x.2, show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl,
            show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
          exact hxy)).2 τ
    rw [← structAut_eq_partAut hK hs P] at hmk
    exact hmk

end CaseA

/-! ## Case (B) -/

section CaseB

variable {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))] {s : Set (Fin m)}
  {G : Subgroup (Perm Ω)}

/-- §14.1, line 8, case (B): **`ψ(π) = 1` exactly when `π` fixes every point of `Δ_j`.** -/
theorem johnsonPsiOf_eq_one_iff (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) {k ts : ℕ} (φ : ↥s ≃ binom (Fin k) ts)
    (hts : 2 ≤ ts) (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (π : structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) :
    johnsonPsiOf hK J φ hts hk hφ π = 1 ↔ ∀ γ ∈ s, (π : Perm (Fin m)) γ = γ := by
  have htA := tAction_johnsonPsiOf hK J φ hts hk hφ π
  constructor
  · intro h1 γ hγ
    rw [h1, map_one] at htA
    -- the restriction of `π` to `s` is the identity
    have hr : restrictHom _ s (isInvariant_structAut_inr hK J) π = 1 :=
      (MulEquiv.map_eq_one_iff (Equiv.permCongrHom φ)).1 htA.symm
    have := congrArg (fun f : Perm ↥s => ((f ⟨γ, hγ⟩ : ↥s) : Fin m)) hr
    exact this
  · intro hfix
    have hr : restrictHom _ s (isInvariant_structAut_inr hK J) π = 1 := by
      refine Equiv.ext fun z => Subtype.ext ?_
      exact hfix z z.2
    have ht1 : tAction ts (johnsonPsiOf hK J φ hts hk hφ π) = tAction ts 1 := by
      rw [htA, hr, map_one, map_one]
    have hmem : tAction ts (johnsonPsiOf hK J φ hts hk hφ π) ∈ (johnsonScheme (Fin k) ts).Aut :=
      htA ▸ mem_aut_johnsonScheme_of_structAut hK J φ hφ π
    have hmem1 : tAction ts (1 : Perm (Fin k)) ∈ (johnsonScheme (Fin k) ts).Aut := ht1 ▸ hmem
    have e1 := johnsonSchemePsi_tAction ts (isJohnsonGraphParams_of hts hk) _ hmem
    have e2 := johnsonSchemePsi_tAction ts (isJohnsonGraphParams_of hts hk) 1 hmem1
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext ht1

/-- §14.1, line 8, case (B): **a permutation of `Γ` that fixes every point of `Δ_j` is an
automorphism of the Johnson scheme on `Δ_j`** (it restricts to the identity of `Δ_j`). -/
theorem mem_structAut_inr_of_fix (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) {f : Perm (Fin m)} (hf : ∀ γ ∈ s, f γ = γ) :
    f ∈ structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) := by
  have hcar : (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))).car
      = f '' (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))).car := by
    show s = f '' s
    ext γ
    constructor
    · intro hγ
      exact ⟨γ, hγ, hf γ hγ⟩
    · rintro ⟨δ, hδ, rfl⟩
      rw [hf δ hδ]
      exact hδ
  have hiso : permHom f (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ⟨s, Sum.inr J⟩ hcar ∈
      (SplitOutcomes (Fin m)).IsoP ⟨s, Sum.inr J⟩ ⟨s, Sum.inr J⟩ := by
    intro x y
    have hx : permHom f (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ⟨s, Sum.inr J⟩ hcar x
        = x := Subtype.ext (by show f (x : Fin m) = _; exact hf x x.2)
    have hy : permHom f (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ⟨s, Sum.inr J⟩ hcar y
        = y := Subtype.ext (by show f (y : Fin m) = _; exact hf y y.2)
    show J.1 _ _ = J.1 x y
    rw [hx, hy]
  exact mem_structAut.2 (hK.eq_smul hcar hiso).symm

/-- §14.1, **lines 6–10, case (B)**, built from the outcome of Theorem 9.2.3 and an
identification `φ : Δ_j ≃ ([k] choose t*)`: the data of `Babai.exists_alignDominantRoundData`,
together with **`m* = k`** and **`ker ϕ*`** (the `τ ∈ G` with `ϕ(τ) ∈ Aut(X')` fixing every
point of `Δ_j`). -/
theorem exists_alignDominantRoundData_B (hK : IsCatAction (SplitOutcomes (Fin m)))
    (hG : IsTransitive G) (ϕ : G →* Perm (Fin m)) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ) (ht : ∀ u : Ω, tPoint ϕ u = t)
    (J : (JohnsonSchemes (Fin m)).Obj s) {k ts : ℕ}
    (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts) (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (hdom : m < 2 * s.ncard) (hm12 : 12 ≤ m) (hn : 96 ≤ Fintype.card Ω) :
    ∃ D : AlignDominantRoundData Ω,
      D.toAlignDominant.m = m ∧
      D.toAlignDominant.Gs
        = preimageSubgroup ϕ (structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) ∧
      D.toAlignDominant.window = omegaOf ϕ s ∧
      D.toAlignDominant.ms = k ∧
      (∃ e : Fin k → Fin D.toAlignDominant.ms, Function.Bijective e ∧
        ∀ τ (hτ : τ ∈ D.toAlignDominant.Gs) (hG : τ ∈ G) γ, γ ∈ s →
          e '' johnsonLabel φ (ϕ ⟨τ, hG⟩ γ) =
            D.toAlignDominant.phis ⟨τ, hτ⟩ '' (e '' johnsonLabel φ γ)) ∧
      ∀ τ : Perm Ω, τ ∈ D.ker ↔ ∃ h : τ ∈ G,
        ϕ ⟨τ, h⟩ ∈ structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ∧
        ∀ γ ∈ s, ϕ ⟨τ, h⟩ γ = γ := by
  refine ⟨(alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J φ hts hk hφ hdom
    hm12).toAlignDominantB.roundData hn, rfl, rfl, rfl, Fintype.card_fin k, ?_, fun τ => ?_⟩
  · -- the identification, numbered: `ψ` is the permutation of `Γ*` inducing the automorphism
    exact ⟨(alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J φ hts hk hφ hdom hm12).enum,
      Equiv.bijective _, fun τ hτ hG' γ hγ =>
        (alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J φ hts hk hφ hdom
          hm12).toAlignDominantB.psi_label (phiStar ϕ _ ⟨τ, hτ⟩) γ hγ⟩
  change τ ∈ kerSubgroup (alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J φ hts hk hφ hdom
    hm12).toAlignDominantB.toAlignDominant.phis ↔ _
  rw [AlignDominant.mem_kerSubgroup_phis]
  constructor
  · rintro ⟨hG', hH, h1⟩
    refine ⟨hG', hH, ?_⟩
    have h2 : johnsonPsiOf hK J φ hts hk hφ ⟨_, hH⟩ = 1 :=
      (MulEquiv.map_eq_one_iff (Equiv.permCongrHom (Fintype.equivFin (Fin k)))).1 h1
    exact (johnsonPsiOf_eq_one_iff hK J φ hts hk hφ ⟨_, hH⟩).1 h2
  · rintro ⟨hG', hH, hfix⟩
    refine ⟨hG', hH, ?_⟩
    show (Equiv.permCongrHom (Fintype.equivFin (Fin k))) (johnsonPsiOf hK J φ hts hk hφ ⟨_, hH⟩)
      = 1
    rw [(johnsonPsiOf_eq_one_iff hK J φ hts hk hφ ⟨_, hH⟩).2 hfix, map_one]

end CaseB

/-! ## The classes other than the dominant window are small -/

section OtherClasses

variable {m : ℕ} {G : Subgroup (Perm Ω)} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- §14.1, lines 5–6 and Eq. (72): **with a dominant color class `Δ_{i₀}`, every color class of
`Ω` other than the window `Ω(Δ_{i₀})` has at most `4n/5` points.** A class `Ω_v` whose label
lies inside one color class `Δ_j` of `Γ` has `j ≠ i₀` (else it is the window), and `Δ_j` is
disjoint from `Δ_{i₀}`, so it has at most `m/2` points; Eq. (72) at `α = 1/2` does the rest.
This is the argument of `Babai.nonempty_alignData_of_versions`, stated on its own. -/
theorem five_mul_ncard_omegaColorClass_le_of_ne_dom (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (hm3 : 3 ≤ m) {t : ℕ} (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m)
    (c : Fin m → ι) {i₀ : ι} (hdom : m < 2 * (colorSet c i₀).card) (v : ι → ℕ)
    (hv : omegaColorClass (Ω := Ω) ϕ c v ≠ omegaOf ϕ {γ : Fin m | c γ = i₀}) :
    5 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 4 * Fintype.card Ω := by
  by_cases hemp : (omegaColorClass (Ω := Ω) ϕ c v).ncard = 0
  · rw [hemp]; omega
  obtain ⟨u, hu⟩ : (omegaColorClass (Ω := Ω) ϕ c v).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, Set.ncard_empty] at hemp
    exact hemp rfl
  set v₀ : ι → ℕ := fun j => if j = i₀ then t else 0 with hv₀def
  have hS₀eq : omegaColorClass (Ω := Ω) ϕ c v₀ = omegaOf ϕ {γ : Fin m | c γ = i₀} :=
    omegaColorClass_eq_omegaOf ϕ ht c i₀ v₀ (by simp [hv₀def])
      (fun j hj => by simp [hv₀def, hj])
  refine five_mul_ncard_omegaColorClass_le_of_le_at hG ϕ hϕ hk hm3 ht ht1 h2t c
    (α := 1 / 2) (by norm_num) (by norm_num) v ?_
  intro j hj
  have hjne : j ≠ i₀ := by
    rintro rfl
    refine hv ?_
    have hvu : omegaColor ϕ c u = v := hu
    have hnc : (Tpoint ϕ u ∩ {γ : Fin m | c γ = j}).ncard = t := by
      have h := congrFun hvu j
      rw [hj] at h
      exact h
    have htot : (Tpoint ϕ u).ncard = t := ht u
    have hsub : Tpoint ϕ u ⊆ {γ : Fin m | c γ = j} := by
      have h1 : Tpoint ϕ u ∩ {γ : Fin m | c γ = j} = Tpoint ϕ u :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hnc, htot])
          (Set.toFinite _)
      rw [← h1]
      exact Set.inter_subset_right
    have huS : u ∈ omegaColorClass (Ω := Ω) ϕ c v₀ := by
      rw [hS₀eq, mem_omegaOf]; exact hsub
    have hvv : v = v₀ := hvu.symm.trans huS
    rw [hvv, hS₀eq]
  have hdisj : Disjoint (colorSet c j) (colorSet c i₀) := by
    rw [Finset.disjoint_left]
    intro γ h1 h2
    simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hjne (h1.symm.trans h2)
  have hsum : (colorSet c j).card + (colorSet c i₀).card ≤ m := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have h := Finset.card_le_univ ((colorSet c j) ∪ (colorSet c i₀))
    rwa [Fintype.card_fin] at h
  have h2 : 2 * (colorSet c j).card ≤ m := by omega
  have h2R : (2 : ℝ) * ((colorSet c j).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
  linarith

end OtherClasses

end Babai
