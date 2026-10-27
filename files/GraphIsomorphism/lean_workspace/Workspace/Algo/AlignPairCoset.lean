/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), lines 1–3, for one pair of versions.
-/
import Workspace.Algo.AlignG1
import Workspace.Algo.AlignJohnsonG1
import Workspace.Algo.AlignJohnsonLine2
import Workspace.Algo.SplitOutcomeTransport
import Workspace.Master.CosetAlign

/-!
# §14.1, Procedure Align, lines 1–3, on one pair of versions

> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit.
> 2. Else, let (i) `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`, (ii) `σ ∈ ϕ⁻¹(σ̄)`, …
>    (iv) `G₁ = ϕ⁻¹(Aut(X(x)))`.
> 3. Update: `G ← G₁`, `y ← y^{σ⁻¹}`.

Eq. (71) runs these lines once for every pair `(X', Y)` of the fixed version `X'` of `x` and a
version `Y` of `y`. The versions are outcomes of Theorem 9.2.3, colored partitions or Johnson
schemes, stored as `Algo.RawAlignOutcome`. In coset form (`Babai.cosetAlignChain`) the three
lines give the candidate set `Babai.alignTransporter ϕ X' Y`: the `τ ∈ G` with
`ϕ(τ) • X' = Y`. By Eq. (70) it is `σ G₁` when `σ̄` exists and `∅` otherwise.

`Algo.alignPairCoset` computes it from the pieces of Procedure Align already on the RAM:
`Algo.alignColPartIso` and `Algo.alignJIso` (line 2 (i), with the parity correction when
`G^ϕ = A(Γ)`), `Algo.actPreimage` (line 2 (ii)), and `Algo.alignG1`, `Algo.alignJG1`
(line 2 (iv)). Two versions of different kinds are never isomorphic, since `SplitOutcomes` is
a sum of two categories, so the routine answers `none` for them.

## Main results

* `Algo.decCoset_alignPairCoset` — **the computed coset is the transporter**, for every action
  of `S(Γ)` on the outcomes that is the category action (`Babai.IsCatAction`);
* `Algo.polyFun_alignPairCoset` — polynomial time.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- A colored partition read at the points `0, …, m-1` of `Γ`, where `m` is the length of the
domain witness. The decoding reads only these points, so it does not change
(`Algo.decAlignPartition_cpNorm`); it makes the lengths the ones Procedure Align's routines
ask for. -/
def cpNorm (p : List ℕ × RawColPart) : RawColPart :=
  ((rawOne p.1).map (labAt p.2.1), (rawOne p.1).map (labAt p.2.2))

/-- §14.1, **lines 1 and 2 (i)** for two versions: `σ̄ ∈ Iso_{G^ϕ}(X', Y)`, or `none`. The
Boolean passed to the two routines says whether the giant `G^ϕ` is `A(Γ)`. -/
def alignPairIso (p : RawAction × RawAlignOutcome × RawAlignOutcome) : Option RawPerm :=
  p.2.1.1.elim
    (p.2.1.2.elim none fun J => p.2.2.2.elim none fun J' =>
      alignJIso (topAllEven p.1, (p.1.2.1, (J, J'))))
    (fun P => p.2.2.1.elim none fun Q =>
      alignColPartIso (topAllEven p.1, (cpNorm (p.1.2.1, P), cpNorm (p.1.2.1, Q))))

/-- §14.1, **line 2 (iv)**: `G₁ = ϕ⁻¹(Aut(X'))` for the fixed version. -/
def alignPairG1 (p : RawAction × RawAlignOutcome) : RawGens :=
  p.2.1.elim (p.2.2.elim [] fun J => alignJG1 (p.1, J)) (fun P => alignG1 (p.1, cpNorm (p.1.2.1, P)))

/-- §14.1, **lines 1–3** for one pair of versions, in coset form: the coset `σ G₁`, or the
empty answer when line 1 rejects. -/
def alignPairCoset (p : RawAction × RawAlignOutcome × RawAlignOutcome) : RawCoset :=
  (alignPairIso p).bind fun s =>
    (actPreimage (p.1, s)).map fun σ => (alignPairG1 (p.1, p.2.1), σ)

/-! ## The two kinds of versions -/

section Kinds

variable {m : ℕ}

theorem labAt_cpNorm_fst {dom : List ℕ} (hd : dom.length = m) (P : RawColPart) {u : ℕ}
    (hu : u < m) : labAt (cpNorm (dom, P)).1 u = labAt P.1 u := by
  have hu' : u < (rawOne dom).length := by rw [rawOne, List.length_range, hd]; exact hu
  simp only [cpNorm, labAt]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hu'), List.getElem_map]
  simp only [rawOne, List.getElem_range]
  rfl

theorem labAt_cpNorm_snd {dom : List ℕ} (hd : dom.length = m) (P : RawColPart) {u : ℕ}
    (hu : u < m) : labAt (cpNorm (dom, P)).2 u = labAt P.2 u := by
  have hu' : u < (rawOne dom).length := by rw [rawOne, List.length_range, hd]; exact hu
  simp only [cpNorm, labAt]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hu'), List.getElem_map]
  simp only [rawOne, List.getElem_range]
  rfl

theorem cpNorm_length {dom : List ℕ} (hd : dom.length = m) (P : RawColPart) :
    (cpNorm (dom, P)).1.length = m := by
  simp only [cpNorm, List.length_map, rawOne, List.length_range, hd]

/-- Reading a partition at the points of `Γ` does not change the version it describes. -/
theorem decAlignPartition_cpNorm {dom : List ℕ} (hd : dom.length = m) (P : RawColPart) :
    decAlignPartition m (cpNorm (dom, P)) = decAlignPartition m P := by
  have hl : ∀ u : Fin m, labAt (cpNorm (dom, P)).1 (u : ℕ) = labAt P.1 (u : ℕ) :=
    fun u => labAt_cpNorm_fst hd P u.isLt
  have hc : ∀ u : Fin m, cellOf (cpNorm (dom, P)) (u : ℕ) = cellOf P (u : ℕ) := fun u => by
    simp only [cellOf, labAt_cpNorm_fst hd P u.isLt, labAt_cpNorm_snd hd P u.isLt]
  have hdc : decColPartition m (cpNorm (dom, P)) = decColPartition m P := by
    simp only [decColPartition, hl, hc]
  exact congrArg (fun C : ColoredPartition (Fin m) ℕ => (⟨Set.univ, Sum.inl
    { color := fun u => C.color u.val
      part := Setoid.comap Subtype.val C.part
      part_le_color := fun h => C.part_le_color h }⟩ : Pt (SplitOutcomes (Fin m)))) hdc

/-- Moving an outcome is being carried by the permutation, for the category action. -/
theorem smul_eq_iff_splitOutcomeIso [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (π : Perm (Fin m))
    (Z Z' : Pt (SplitOutcomes (Fin m))) :
    π • Z = Z' ↔ SplitOutcomeIso π Z Z' :=
  ⟨fun h => SplitOutcomeIso.of_eq_smul hK h.symm, fun h => (h.eq_smul hK).symm⟩

/-- The two-structure form of `Algo.mem_structAut_decJohnson_iff`. -/
theorem smul_decJohnson_iff {r r' : RawJohnson} {f : Perm (Fin m)} :
    f • decJohnson m r = decJohnson m r' ↔
      (∀ u : Fin m, ((f u : Fin m) : ℕ) ∈ r'.1 ↔ (u : ℕ) ∈ r.1) ∧
        (∀ u v : Fin m, (u : ℕ) ∈ r.1 → (v : ℕ) ∈ r.1 →
          rawJDiff (r', (((f u : Fin m) : ℕ), ((f v : Fin m) : ℕ)))
            = rawJDiff (r, ((u : ℕ), (v : ℕ)))) := by
  constructor
  · intro hf
    have hv : ∀ u : Fin m, (decJohnson m r').vcol (f u) = (decJohnson m r).vcol u := by
      intro u
      rw [← hf]
      show (decJohnson m r).vcol (f⁻¹ (f u)) = _
      rw [show f⁻¹ (f u) = u from Equiv.symm_apply_apply f u]
    have he : ∀ u v : Fin m,
        (decJohnson m r').ecol (f u) (f v) = (decJohnson m r).ecol u v := by
      intro u v
      rw [← hf]
      show (decJohnson m r).ecol (f⁻¹ (f u)) (f⁻¹ (f v)) = _
      rw [show f⁻¹ (f u) = u from Equiv.symm_apply_apply f u,
        show f⁻¹ (f v) = v from Equiv.symm_apply_apply f v]
    have hmem : ∀ u : Fin m, ((f u : Fin m) : ℕ) ∈ r'.1 ↔ (u : ℕ) ∈ r.1 := by
      intro u
      have h := hv u
      simp only [decJohnson_vcol] at h
      by_cases hu : (u : ℕ) ∈ r.1
      · rw [if_pos hu] at h
        exact ⟨fun _ => hu, fun _ => by by_contra hc; rw [if_neg hc] at h; exact absurd h (by decide)⟩
      · rw [if_neg hu] at h
        exact ⟨fun hc => by rw [if_pos hc] at h; exact absurd h (by decide), fun hc => absurd hc hu⟩
    refine ⟨hmem, fun u v hu hv' => ?_⟩
    have h := he u v
    rwa [decJohnson_ecol_mem m r' ((hmem u).2 hu) ((hmem v).2 hv'),
      decJohnson_ecol_mem m r hu hv'] at h
  · rintro ⟨hmem, hecol⟩
    refine colStruct_smul_eq (fun u => ?_) (fun u v => ?_)
    · show (if ((f u : Fin m) : ℕ) ∈ r'.1 then 1 else 0) = (if (u : ℕ) ∈ r.1 then 1 else 0)
      by_cases hc : (u : ℕ) ∈ r.1
      · rw [if_pos ((hmem u).2 hc), if_pos hc]
      · rw [if_neg (fun hh => hc ((hmem u).1 hh)), if_neg hc]
    · by_cases hu : (u : ℕ) ∈ r.1
      · by_cases hv : (v : ℕ) ∈ r.1
        · rw [decJohnson_ecol_mem m r' ((hmem u).2 hu) ((hmem v).2 hv),
            decJohnson_ecol_mem m r hu hv]
          exact hecol u v hu hv
        · show (if _ ∈ r'.1 then (if _ ∈ r'.1 then _ else 0) else 0)
            = (if _ ∈ r.1 then (if _ ∈ r.1 then _ else 0) else 0)
          rw [if_pos ((hmem u).2 hu), if_pos hu,
            if_neg (fun hh => hv ((hmem v).1 hh)), if_neg hv]
      · show (if _ ∈ r'.1 then _ else 0) = (if _ ∈ r.1 then _ else 0)
        rw [if_neg (fun hh => hu ((hmem u).1 hh)), if_neg hu]

/-- Two decoded Johnson versions: being carried by `π` in the category of outcomes is being
carried by `π` as colored structures. -/
theorem splitOutcomeIso_johnson_iff (π : Perm (Fin m)) {J J' : RawJohnson}
    (hJ : J.WF m (rawJDeg J) J.2.1) (hJ' : J'.WF m (rawJDeg J') J'.2.1) :
    SplitOutcomeIso π (decAlignJohnson J hJ) (decAlignJohnson J' hJ') ↔
      π • decJohnson m J = decJohnson m J' := by
  rw [smul_decJohnson_iff]
  constructor
  · intro h
    have hcar := h.car
    obtain ⟨e, he, hcol⟩ := h
    have hmem : ∀ u : Fin m, ((π u : Fin m) : ℕ) ∈ J'.1 ↔ (u : ℕ) ∈ J.1 := by
      intro u
      constructor
      · intro hu
        have hu' : π u ∈ (decAlignJohnson J' hJ').car := hu
        rw [hcar] at hu'
        obtain ⟨w, hw, hwu⟩ := hu'
        rw [π.injective hwu] at hw
        exact hw
      · intro hu
        have := (e ⟨u, hu⟩).property
        rw [he] at this
        exact this
    refine ⟨hmem, fun u v hu hv => ?_⟩
    have h := hcol ⟨u, hu⟩ ⟨v, hv⟩
    change rawJDiff (J', ((e ⟨u, hu⟩).val.val, (e ⟨v, hv⟩).val.val)) =
      rawJDiff (J, (u.val, v.val)) at h
    rwa [he, he] at h
  · rintro ⟨hmem, hdiff⟩
    refine ⟨Equiv.subtypeEquiv π (fun u => (hmem u).symm), fun _ => rfl, fun x y => ?_⟩
    change rawJDiff (J', ((π x.val).val, (π y.val).val)) = rawJDiff (J, (x.val.val, y.val.val))
    exact hdiff x.val y.val x.property y.property

/-- Versions of different kinds are never carried to each other. -/
theorem not_splitOutcomeIso_partition_johnson (π : Perm (Fin m)) (P : RawColPart)
    {J : RawJohnson} (hJ : J.WF m (rawJDeg J) J.2.1) :
    ¬ SplitOutcomeIso π (decAlignPartition m P) (decAlignJohnson J hJ) := by
  rintro ⟨e, _, he⟩
  exact he.elim

theorem not_splitOutcomeIso_johnson_partition (π : Perm (Fin m)) (P : RawColPart)
    {J : RawJohnson} (hJ : J.WF m (rawJDeg J) J.2.1) :
    ¬ SplitOutcomeIso π (decAlignJohnson J hJ) (decAlignPartition m P) := by
  rintro ⟨e, _, he⟩
  exact he.elim

end Kinds

/-! ## The computed coset is the transporter -/

section Spec

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

/-- The giant is `A(Γ)` exactly when the computed flag says so, and otherwise it is `S(Γ)`. -/
theorem mem_range_of_flag (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    {f : Perm (Fin m)} (hf : topAllEven A = true → Equiv.Perm.sign f = 1) : f ∈ ϕ.range := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have hspec := topAllEven_spec (n := n) (m := m) A.1.1 A.2.1 hi
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at hspec
  by_cases hg : topAllEven A = true
  · exact hgiant (Equiv.Perm.mem_alternatingGroup.2 (hf hg))
  · have hnot : ¬ ϕ.range ≤ alternatingGroup (Fin m) := fun hh => hg (hspec.2 hh)
    rcases (isGiant_iff_alternating_le ϕ.range).2 hgiant with h1 | h1
    · rw [h1]; exact Subgroup.mem_top f
    · exact absurd (le_of_eq h1) hnot

/-- If the giant is `A(Γ)`, every image is even. -/
theorem sign_of_flag (hA : RawAction.WF n m A ϕ) (hg : topAllEven A = true) (τ : decGroup n A.1.2) :
    Equiv.Perm.sign (ϕ τ) = 1 := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have hspec := topAllEven_spec (n := n) (m := m) A.1.1 A.2.1 hi
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at hspec
  exact Equiv.Perm.mem_alternatingGroup.1 (hspec.1 hg ⟨τ, rfl⟩)

/-- Line 2 (ii): an image in the range has a computed preimage. -/
theorem actPreimage_of_range (hA : RawAction.WF n m A ϕ) {s : RawPerm} (hs : RawPerm.WF m s)
    (hr : decPerm m s ∈ ϕ.range) :
    ∃ σ : Perm (Fin n), ∃ hσ : σ ∈ decGroup n A.1.2,
      actPreimage (A, s) = some (encPerm n σ) ∧ ϕ ⟨σ, hσ⟩ = decPerm m s := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have hnone := actPreimage_eq_none_iff hd hm hi (decPerm m s)
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hs] at hnone
  have hne : actPreimage (A, s) ≠ none := fun h => (hnone.mp h) hr
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
  have hsome := actPreimage_eq_some hd hm hi (decPerm m s) (r := q)
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hs] at hsome
  obtain ⟨σ, hσ, he, himg⟩ := hsome hq
  exact ⟨σ, hσ, he ▸ hq, himg⟩

/-- The partition case of line 2 (iv), in the form of the raw action. -/
theorem decGroup_alignG1_raw (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    {P : RawColPart} (hP : P.1.length = m) :
    decGroup n (alignG1 (A, P)) = preimageSubgroup ϕ (structAut (decColStruct m P)) := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have h := decGroup_alignG1 hd hm hi hgiant hP
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at h
  exact h

/-- The Johnson case of line 2 (iv), in the form of the raw action. -/
theorem decGroup_alignJG1_raw (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    {J : RawJohnson} (hJ : J.WF m (rawJDeg J) J.2.1) :
    decGroup n (alignJG1 (A, J)) = preimageSubgroup ϕ (structAut (decJohnson m J)) := by
  obtain ⟨hd, hm, hgs, his, hi⟩ := hA
  have h := decGroup_alignJG1 hd hm hi hgiant hJ
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at h
  exact h

variable [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- The stabilizer of a decoded partition version is the automorphism group of the colored
partition. -/
theorem structAut_decAlignPartition (hK : IsCatAction (SplitOutcomes (Fin m))) (P : RawColPart) :
    structAut (decAlignPartition m P) = structAut (Γ := Fin m) (decColStruct m P) := by
  ext f
  rw [mem_structAut, mem_structAut, smul_eq_iff_splitOutcomeIso hK,
    splitOutcomeIso_partition_iff, colPartIso_iff_smul]

/-- The stabilizer of a decoded Johnson version is the automorphism group of the Johnson
structure. -/
theorem structAut_decAlignJohnson (hK : IsCatAction (SplitOutcomes (Fin m))) {J : RawJohnson}
    (hJ : J.WF m (rawJDeg J) J.2.1) :
    structAut (decAlignJohnson J hJ) = structAut (Γ := Fin m) (decJohnson m J) := by
  ext f
  rw [mem_structAut, mem_structAut, smul_eq_iff_splitOutcomeIso hK,
    splitOutcomeIso_johnson_iff f hJ hJ]

/-- The coset `σ G₁` is the transporter once `σ` carries `X'` to `Y`. -/
theorem decCoset_eq_alignTransporter {Z Z' : Pt (SplitOutcomes (Fin m))} {g : RawGens}
    (hg : decGroup n g = preimageSubgroup ϕ (structAut Z)) {σ : Perm (Fin n)}
    (hσ : σ ∈ decGroup n A.1.2) (hmove : ϕ ⟨σ, hσ⟩ • Z = Z') :
    decCoset n (some (g, encPerm n σ)) = alignTransporter ϕ Z Z' := by
  rw [alignTransporter_eq_smul ϕ Z Z' ⟨σ, hσ⟩ hmove, ← hg]
  ext τ
  simp only [decCoset, decPerm_encPerm, Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul,
    SetLike.mem_coe]
  constructor
  · rintro ⟨h, hh, rfl⟩; exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩; exact ⟨h, hh, rfl⟩

/-- §14.1, **lines 1–3 for one pair of versions**: the computed coset is the transporter
`{τ ∈ G | ϕ(τ) • X' = Y}` of Eq. (70), for the category action of `S(Γ)` on the outcomes of
Theorem 9.2.3. When line 1 rejects, both sides are empty. -/
theorem decCoset_alignPairCoset (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    (hK : IsCatAction (SplitOutcomes (Fin m))) {o o' : RawAlignOutcome}
    {Z Z' : Pt (SplitOutcomes (Fin m))} (hz : decAlignOutcome m o = some Z)
    (hz' : decAlignOutcome m o' = some Z') :
    decCoset n (alignPairCoset (A, o, o')) = alignTransporter ϕ Z Z' := by
  have hdm : A.2.1.length = m := hA.2.1
  -- the transporter is empty when no image carries `Z` to `Z'`
  have hempty : (∀ τ : decGroup n A.1.2, ¬ ϕ τ • Z = Z') → alignTransporter ϕ Z Z' = ∅ := by
    intro h
    ext τ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hτ, hm⟩
    exact h ⟨τ, hτ⟩ hm
  -- the answer when `σ̄` has been found
  have hfound : ∀ {s : RawPerm} {g : RawGens}, RawPerm.WF m s →
      (topAllEven A = true → Equiv.Perm.sign (decPerm m s) = 1) →
      decPerm m s • Z = Z' → decGroup n g = preimageSubgroup ϕ (structAut Z) →
      decCoset n ((actPreimage (A, s)).map fun σ => (g, σ)) = alignTransporter ϕ Z Z' := by
    intro s g hs hsign hmove hg
    obtain ⟨σ, hσ, hpre, himg⟩ :=
      actPreimage_of_range hA hs (mem_range_of_flag hA hgiant hsign)
    rw [hpre, Option.map_some]
    exact decCoset_eq_alignTransporter hg hσ (by rw [himg]; exact hmove)
  rcases decAlignOutcome_cases hz with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩
  · rcases decAlignOutcome_cases hz' with ⟨Q, rfl, rfl⟩ | ⟨J', hJ', rfl, rfl⟩
    · -- two colored partitions, read at the points of `Γ`
      set P' := cpNorm (A.2.1, P) with hP'
      set Q' := cpNorm (A.2.1, Q) with hQ'
      have hPl : P'.1.length = m := cpNorm_length hdm P
      have hQl : Q'.1.length = m := cpNorm_length hdm Q
      have hZ : decAlignPartition m P = decAlignPartition m P' :=
        (decAlignPartition_cpNorm hdm P).symm
      have hZ' : decAlignPartition m Q = decAlignPartition m Q' :=
        (decAlignPartition_cpNorm hdm Q).symm
      have hiff : ∀ f : Perm (Fin m),
          f • decAlignPartition m P = decAlignPartition m Q ↔ ColPartIso m P' Q' f := by
        intro f
        rw [hZ, hZ', smul_eq_iff_splitOutcomeIso hK, splitOutcomeIso_partition_iff]
      have hiso : alignPairIso (A, rawAlignPartition P, rawAlignPartition Q) =
          alignColPartIso (topAllEven A, (P', Q')) := rfl
      have hG1 : decGroup n (alignPairG1 (A, rawAlignPartition P)) =
          preimageSubgroup ϕ (structAut (decAlignPartition m P)) := by
        change decGroup n (alignG1 (A, P')) = _
        rw [decGroup_alignG1_raw hA hgiant hPl, hZ, structAut_decAlignPartition hK]
      unfold alignPairCoset
      rw [hiso]
      cases hs : alignColPartIso (topAllEven A, (P', Q')) with
      | none =>
        rw [Option.bind_none]
        refine (hempty fun τ hτ => ?_).symm
        obtain ⟨hg, hsg⟩ := alignColPartIso_eq_none hPl hQl hs (ϕ τ) ((hiff _).1 hτ)
        rw [sign_of_flag hA hg τ] at hsg
        exact absurd hsg (by decide)
      | some s =>
        rw [Option.bind_some]
        obtain ⟨hwf, hc, hsign⟩ := alignColPartIso_some hPl hQl hs
        exact hfound hwf hsign ((hiff _).2 hc) hG1
    · -- a partition and a Johnson scheme
      have he : alignTransporter ϕ (decAlignPartition m P) (decAlignJohnson J' hJ') = ∅ :=
        hempty fun τ h => not_splitOutcomeIso_partition_johnson _ P hJ'
          ((smul_eq_iff_splitOutcomeIso hK _ _ _).1 h)
      rw [he]
      rfl
  · rcases decAlignOutcome_cases hz' with ⟨Q, rfl, rfl⟩ | ⟨J', hJ', rfl, rfl⟩
    · have he : alignTransporter ϕ (decAlignJohnson J hJ) (decAlignPartition m Q) = ∅ :=
        hempty fun τ h => not_splitOutcomeIso_johnson_partition _ Q hJ
          ((smul_eq_iff_splitOutcomeIso hK _ _ _).1 h)
      rw [he]
      rfl
    · -- two Johnson schemes
      have hiff : ∀ f : Perm (Fin m),
          f • decAlignJohnson J hJ = decAlignJohnson J' hJ' ↔
            f • decJohnson m J = decJohnson m J' := by
        intro f
        rw [smul_eq_iff_splitOutcomeIso hK, splitOutcomeIso_johnson_iff f hJ hJ']
      have hiso : alignPairIso (A, rawAlignJohnson J, rawAlignJohnson J') =
          alignJIso (topAllEven A, (A.2.1, (J, J'))) := rfl
      have hG1 : decGroup n (alignPairG1 (A, rawAlignJohnson J)) =
          preimageSubgroup ϕ (structAut (decAlignJohnson J hJ)) := by
        change decGroup n (alignJG1 (A, J)) = _
        rw [decGroup_alignJG1_raw hA hgiant hJ, structAut_decAlignJohnson hK hJ]
      unfold alignPairCoset
      rw [hiso]
      cases hs : alignJIso (topAllEven A, (A.2.1, (J, J'))) with
      | none =>
        rw [Option.bind_none]
        refine (hempty fun τ hτ => ?_).symm
        obtain ⟨hg, hsg⟩ := alignJIso_eq_none hdm hJ hJ' hs (ϕ τ) ((hiff _).1 hτ)
        rw [sign_of_flag hA hg τ] at hsg
        exact absurd hsg (by decide)
      | some s =>
        rw [Option.bind_some]
        obtain ⟨hwf, hc, hsign⟩ := alignJIso_some hdm hJ hJ' hs
        exact hfound hwf hsign ((hiff _).2 hc) hG1

end Spec

/-! ## The running time -/

section Cost

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-- `f p` is `none`, or `h` applied to its value and `p`. -/
private theorem pelim {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → Option β}
    {g : α → γ} {h : β × α → γ} (hf : PolyFun f) (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun a => (f a).elim (g a) (fun b => h (b, a))) :=
  (hf.pair polyFun_id).comp (PolyFun.optionElim hg hh)

theorem polyFun_cpNorm : PolyFun cpNorm := by
  have hr : PolyFun (fun p : List ℕ × RawColPart => rawOne p.1) := polyFun_fst.comp polyFun_rawOne
  have h1 : PolyFun (fun p : List ℕ × RawColPart => (rawOne p.1).map (labAt p.2.1)) :=
    ((pfst (psnd polyFun_id)).pair hr).comp (PolyFun.mapParam polyFun_labAtPair)
  have h2 : PolyFun (fun p : List ℕ × RawColPart => (rawOne p.1).map (labAt p.2.2)) :=
    ((psnd (psnd polyFun_id)).pair hr).comp (PolyFun.mapParam polyFun_labAtPair)
  exact h1.pair h2

theorem polyFun_alignPairIso : PolyFun alignPairIso := by
  let T := RawAction × RawAlignOutcome × RawAlignOutcome
  have i1 : PolyFun (fun q : RawJohnson × T => q) := polyFun_id
  have hJ2 : PolyFun (fun q : RawJohnson × T =>
      q.2.2.2.2.elim none fun J' => alignJIso (topAllEven q.2.1, (q.2.1.2.1, (q.1, J')))) := by
    have i : PolyFun (fun r : RawJohnson × (RawJohnson × T) => r) := polyFun_id
    exact pelim (psnd (psnd (psnd (psnd i1)))) (polyFun_const none)
      ((((pfst (psnd (psnd i))).comp polyFun_topAllEven).pair
        ((pfst (psnd (pfst (psnd (psnd i))))).pair ((pfst (psnd i)).pair (pfst i)))).comp
          polyFun_alignJIso)
  have i0 : PolyFun (fun p : T => p) := polyFun_id
  have hJ1 : PolyFun (fun p : T => p.2.1.2.elim none fun J => p.2.2.2.elim none fun J' =>
      alignJIso (topAllEven p.1, (p.1.2.1, (J, J')))) :=
    pelim (psnd (pfst (psnd i0))) (polyFun_const none) hJ2
  have i2 : PolyFun (fun q : RawColPart × T => q) := polyFun_id
  have hP2 : PolyFun (fun q : RawColPart × T => q.2.2.2.1.elim none fun Q =>
      alignColPartIso (topAllEven q.2.1, (cpNorm (q.2.1.2.1, q.1), cpNorm (q.2.1.2.1, Q)))) := by
    have i : PolyFun (fun r : RawColPart × (RawColPart × T) => r) := polyFun_id
    have hd := pfst (psnd (pfst (psnd (psnd i))))
    exact pelim (pfst (psnd (psnd (psnd i2)))) (polyFun_const none)
      ((((pfst (psnd (psnd i))).comp polyFun_topAllEven).pair
        (((hd.pair (pfst (psnd i))).comp polyFun_cpNorm).pair
          ((hd.pair (pfst i)).comp polyFun_cpNorm))).comp polyFun_alignColPartIso)
  exact pelim (pfst (pfst (psnd i0))) hJ1 hP2

theorem polyFun_alignPairG1 : PolyFun alignPairG1 := by
  let T := RawAction × RawAlignOutcome
  have i0 : PolyFun (fun p : T => p) := polyFun_id
  have hJ : PolyFun (fun p : T => p.2.2.elim [] fun J => alignJG1 (p.1, J)) := by
    have i : PolyFun (fun r : RawJohnson × T => r) := polyFun_id
    exact pelim (psnd (psnd i0)) (polyFun_const [])
      (((pfst (psnd i)).pair (pfst i)).comp polyFun_alignJG1)
  have i : PolyFun (fun r : RawColPart × T => r) := polyFun_id
  exact pelim (pfst (psnd i0)) hJ
    (((pfst (psnd i)).pair (((pfst (psnd (pfst (psnd i)))).pair (pfst i)).comp polyFun_cpNorm)).comp
      polyFun_alignG1)

/-- §14.1, lines 1–3 for one pair of versions **run in polynomial time**. -/
theorem polyFun_alignPairCoset : PolyFun alignPairCoset := by
  let T := RawAction × RawAlignOutcome × RawAlignOutcome
  have i : PolyFun (fun r : RawPerm × T => r) := polyFun_id
  have hin : PolyFun (fun r : RawPerm × T =>
      (actPreimage (r.2.1, r.1)).elim none fun σ => some (alignPairG1 (r.2.1, r.2.2.1), σ)) := by
    have j : PolyFun (fun q : RawPerm × (RawPerm × T) => q) := polyFun_id
    exact pelim (((pfst (psnd i)).pair (pfst i)).comp polyFun_actPreimage) (polyFun_const none)
      (((((pfst (psnd (psnd j))).pair (pfst (psnd (psnd (psnd j))))).comp polyFun_alignPairG1).pair
        (pfst j)).comp polyFun_some)
  refine (pelim polyFun_alignPairIso (polyFun_const none) hin).of_eq (fun p => ?_)
  unfold alignPairCoset
  cases alignPairIso p with
  | none => rfl
  | some s =>
    change (actPreimage (p.1, s)).elim none _ = (actPreimage (p.1, s)).map _
    cases actPreimage (p.1, s) <;> rfl

end Cost

end Algo
