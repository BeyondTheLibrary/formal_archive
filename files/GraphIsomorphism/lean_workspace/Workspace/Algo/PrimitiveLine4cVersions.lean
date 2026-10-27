import Workspace.Algo.PrimitiveLine4cSpec
import Workspace.Master.Line4cdBranch

/-! # Section 15, lines 4c–4d on the RAM: the computed versions and the Master's branch

Line 4c's output on the RAM is two lists of raw outcomes (`line4cVersions`). This file reads
them as the canonical family of versions Sec. 14.2 asks for, and hands that family to
Procedure Align on the Master side (`Babai.nonempty_alignData_of_versions`).

* `line4cVers` is the family: for a string `w : Ω → ℕ` it is the set of decoded outcomes the
  machine computes on `H(w)` when that structure is an admitted input of Theorem 9.2.3, and
  empty otherwise. At `x` and at `y` it is exactly the decoded list the node returns
  (`line4c_versions_spec`).
* `isCanonicalVersions_line4cVers`: the family is canonical, `Vers(w^σ) = (σ^ϕ) • Vers(w)`
  for every string and every `σ ∈ G`. This is Theorem 9.2.3's canonicity on the RAM
  (`extendedSplitFamily_transport`), applied to the shift of the structure
  (`IsPaletteStruct.iso`, `Babai.hyperColoring_strAct_eq`).
* `line4c_versions_spec` collects what the Master needs, and `nonempty_line4cdData_ram` is
  the Master's round of lines 4c–4d built on the machine's family. Its count of versions is
  the length of the list the machine returns for `y`, which is quasipolynomial in the size of
  the node's input with one exponent for all inputs (`line4cVersions_length_le`).

The bounds `tt`, `dd` of the Theorem 9.2.2 solver are any at which Theorem 9.2.3 on the RAM
is valid and canonical (`Line4cBounds`); `exists_line4cBounds` gives them for every `c`.
-/

namespace Algo
open Babai RAM Equiv
open scoped Classical Pointwise

/-- The bounds at which the Extended Design Lemma on the RAM (arity guard `1`) is valid and
canonical: the conclusion of `exists_extendedSplitFamily_valid_canonical` at `a = 1`. -/
def Line4cBounds (c tt dd : ℕ) : Prop :=
  BipInputRunCanonical c tt dd ∧
    ∀ n g, ExtendedInputRep 1 n g →
      (∃ o, o ∈ extendedSplitFamily 1 c tt dd g) ∧
      ∀ o ∈ extendedSplitFamily 1 c tt dd g, ∃ Z, decAlignOutcome n o = some Z ∧
        IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z

theorem exists_line4cBounds (c : ℕ) : ∃ tt dd, Line4cBounds c tt dd := by
  obtain ⟨tt, dd, hcan, h⟩ := exists_extendedSplitFamily_valid_canonical c
  exact ⟨tt, dd, hcan, (h 1).2.1⟩

/-! ### Isomorphisms of `k`-ary structures -/

theorem KAryRelStruct.inv_mem_iso {Γ C : Type*} {k : ℕ} {R R' : KAryRelStruct Γ C k}
    {π : Perm Γ} (h : π ∈ KAryRelStruct.Iso R R') : π⁻¹ ∈ KAryRelStruct.Iso R' R := by
  intro i x
  have hx : tupleMap (π : Γ → Γ) (tupleMap ((π⁻¹ : Perm Γ) : Γ → Γ) x) = x := by
    funext j; simp [tupleMap]
  rw [h i (tupleMap ((π⁻¹ : Perm Γ) : Γ → Γ) x), hx]

/-- The automorphism group of an isomorphic copy is the conjugate. -/
theorem KAryRelStruct.aut_eq_map_of_iso {Γ C : Type*} {k : ℕ} {R R' : KAryRelStruct Γ C k}
    {π : Perm Γ} (h : π ∈ KAryRelStruct.Iso R R') :
    R'.Aut = R.Aut.map (Equiv.permCongrHom (π : Γ ≃ Γ)).toMonoidHom := by
  ext τ
  constructor
  · intro hτ
    refine ⟨π⁻¹ * τ * π, ?_, ?_⟩
    · intro i x
      have hx : tupleMap (π : Γ → Γ) (tupleMap ((π⁻¹ * τ * π : Perm Γ) : Γ → Γ) x) =
          tupleMap (τ : Γ → Γ) (tupleMap (π : Γ → Γ) x) := by
        funext j; simp [tupleMap]
      rw [h i x, h i, hx]
      exact hτ i _
    · change (π : Γ ≃ Γ).permCongr (π⁻¹ * τ * π) = τ
      rw [permCongr_eq_conj]
      group
  · rintro ⟨σ, hσ, rfl⟩
    intro i x
    change x ∈ R'.rel i ↔ tupleMap (((π : Γ ≃ Γ).permCongr σ : Perm Γ) : Γ → Γ) x ∈ R'.rel i
    rw [permCongr_eq_conj]
    have hinv := KAryRelStruct.inv_mem_iso h
    rw [hinv i x, hinv i, hσ i]
    have hx : tupleMap (σ : Γ → Γ) (tupleMap ((π⁻¹ : Perm Γ) : Γ → Γ) x) =
        tupleMap ((π⁻¹ : Perm Γ) : Γ → Γ) (tupleMap ((π * σ * π⁻¹ : Perm Γ) : Γ → Γ) x) := by
      funext j; simp [tupleMap]
    rw [hx]

/-! ### The family of versions -/

section Family

variable {n m : ℕ} (c tt dd : ℕ) (p : RawAction) (t : ℕ) (x y : RawStr)

/-- Line 4c's structure of `H(w)` for a string `w : Ω → ℕ`, with the palette of `x` and
`y`. -/
def line4cInput (w : Fin n → ℕ) : AmbientGIn := line4cAmbient (((p, x, y), t), encStrN w)

/-- **Line 4c on the RAM, as a family of versions** (Sec. 14.2): the decoded outcomes the
machine computes on the structure of `H(w)`, when line 4b's test fails at `w` (the relative
symmetry defect of `H(w)` is at least `1/2`, `primitiveSmallDefect`) and the structure is an
admitted input of Theorem 9.2.3, and nothing otherwise. At `x` and `y` the second condition
follows from the first (`extendedInputRep_line4c`), so the machine decides membership with
the polynomial test of line 4b. -/
noncomputable def line4cVers (m : ℕ) (w : Fin n → ℕ) : Set (Pt (SplitOutcomes (Fin m))) :=
  if ExtendedInputRep 1 m (line4cInput p t x y w) ∧
      primitiveSmallDefect (p, encStrN w) = false then
    {Z | ∃ o ∈ extendedSplitFamily 1 c tt dd (line4cInput p t x y w),
      decAlignOutcome m o = some Z}
  else ∅

theorem line4cVers_subset (w : Fin n → ℕ) :
    line4cVers c tt dd p t x y m w ⊆
      {Z | ∃ o ∈ extendedSplitFamily 1 c tt dd (line4cInput p t x y w),
        decAlignOutcome m o = some Z} := by
  unfold line4cVers
  split_ifs
  · exact le_rfl
  · exact Set.empty_subset _

/-- The decoded outcomes of a list are finitely many, at most the length of the list. -/
theorem decoded_finite_ncard_le (l : List RawAlignOutcome) :
    ({Z : Pt (SplitOutcomes (Fin m)) | ∃ o ∈ l, decAlignOutcome m o = some Z}).Finite ∧
    ({Z : Pt (SplitOutcomes (Fin m)) | ∃ o ∈ l, decAlignOutcome m o = some Z}).ncard ≤
      l.length := by
  have he : {Z : Pt (SplitOutcomes (Fin m)) | ∃ o ∈ l, decAlignOutcome m o = some Z} ⊆
      (l.filterMap (decAlignOutcome m)).toFinset := by
    intro Z ⟨o, ho, hZ⟩
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filterMap]
    exact ⟨o, ho, hZ⟩
  refine ⟨(Finset.finite_toSet _).subset he, ?_⟩
  calc _ ≤ ((l.filterMap (decAlignOutcome m)).toFinset : Set _).ncard :=
        Set.ncard_le_ncard he (Finset.finite_toSet _)
    _ = (l.filterMap (decAlignOutcome m)).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (l.filterMap (decAlignOutcome m)).length := List.toFinset_card_le _
    _ ≤ l.length := List.length_filterMap_le _ _

theorem line4cVers_finite (w : Fin n → ℕ) : (line4cVers c tt dd p t x y m w).Finite :=
  (decoded_finite_ncard_le _).1.subset (line4cVers_subset c tt dd p t x y w)

theorem ncard_line4cVers_le (w : Fin n → ℕ) :
    (line4cVers c tt dd p t x y m w).ncard ≤
      (extendedSplitFamily 1 c tt dd (line4cInput p t x y w)).length :=
  (Set.ncard_le_ncard (line4cVers_subset c tt dd p t x y w)
    (decoded_finite_ncard_le _).1).trans (decoded_finite_ncard_le _).2

variable {c tt dd} (hb : Line4cBounds c tt dd)
include hb

theorem line4cVers_good (w : Fin n → ℕ) :
    ∀ Z ∈ line4cVers c tt dd p t x y m w,
      IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) Z := by
  intro Z hZ
  unfold line4cVers at hZ
  split_ifs at hZ with hrep
  · obtain ⟨o, ho, hdec⟩ := hZ
    obtain ⟨Z', hdec', hgood⟩ := (hb.2 m _ hrep.1).2 o ho
    rw [hdec] at hdec'
    cases hdec'
    have hα : sbipAlphaValue (line4cInput p t x y w).2 = 3 / 4 := by
      change ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 / 4
      norm_num
    rwa [hα] at hgood
  · exact absurd hZ (Set.notMem_empty Z)

theorem line4cVers_nonempty (w : Fin n → ℕ)
    (hrep : ExtendedInputRep 1 m (line4cInput p t x y w) ∧
      primitiveSmallDefect (p, encStrN w) = false) :
    (line4cVers c tt dd p t x y m w).Nonempty := by
  obtain ⟨o, ho⟩ := (hb.2 m _ hrep.1).1
  obtain ⟨Z, hdec, -⟩ := (hb.2 m _ hrep.1).2 o ho
  refine ⟨Z, ?_⟩
  unfold line4cVers
  rw [if_pos hrep]
  exact ⟨o, ho, hdec⟩

end Family

/-! ### Canonicity -/

section Canonical

variable {n m t : ℕ} {p : RawAction} {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2))) (id : PrimitiveCaseId ϕ t)

include hp hϕ hk id in
/-- A `G`-shift of the string moves the machine's structure by the corresponding
permutation of `Γ`. -/
theorem iso_line4cInput_strAct (x y : RawStr) (w : Fin n → ℕ) (σ : decGroup n p.1.2) :
    ϕ σ ∈ KAryRelStruct.Iso
      (decRel m (line4cInput p t x y w).1.1.1.length (line4cInput p t x y w).1.2)
      (decRel m (line4cInput p t x y w).1.1.1.length
        (line4cInput p t x y (strAct w (σ : Perm (Fin n)))).1.2) := by
  have hlen : (line4cInput p t x y w).1.1.1.length = t := line4cArity_length hp id x y
  rw [hlen]
  have h := isPaletteStruct_line4c hp hϕ hk id x y (encStrN w)
  have h' := isPaletteStruct_line4c hp hϕ hk id x y (encStrN (strAct w (σ : Perm (Fin n))))
  rw [decStrN_encStrN] at h h'
  rw [hyperColoring_strAct_eq id w σ] at h'
  exact h.iso (ϕ σ) h'

include hp hϕ hk id in
theorem extendedInputRep_line4cInput_strAct (x y : RawStr) (w : Fin n → ℕ)
    (σ : decGroup n p.1.2) :
    ExtendedInputRep 1 m (line4cInput p t x y (strAct w (σ : Perm (Fin n)))) ↔
      ExtendedInputRep 1 m (line4cInput p t x y w) := by
  have hiso := iso_line4cInput_strAct hp hϕ hk id x y w σ
  have haut := KAryRelStruct.aut_eq_map_of_iso hiso
  have hdef : defect (decRel m (line4cInput p t x y w).1.1.1.length
        (line4cInput p t x y (strAct w (σ : Perm (Fin n)))).1.2).Aut =
      defect (decRel m (line4cInput p t x y w).1.1.1.length
        (line4cInput p t x y w).1.2).Aut := by
    rw [haut, defect_map_permCongrHom]
  constructor
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, by have := h.9; rw [← hdef]; exact this⟩
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, by have := h.9; rw [← hdef] at this; exact this⟩

include hp hϕ hk in
/-- Line 4b's polynomial test, read at any string. -/
theorem primitiveSmallDefect_iff (z : RawStr) :
    primitiveSmallDefect (p, z) = true ↔
      defect (colorAut t (hyperColoring id (decStrN n z))) < 1 / 2 := by
  have h := primitiveSmallDefect_spec hp.1 hp.2.1 hp.2.2.2.2 hϕ hk id z
  simpa only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1, Prod.mk.eta]
    using h

include hp hϕ hk id in
/-- Line 4b's test does not see a `G`-shift of the string. -/
theorem primitiveSmallDefect_strAct (w : Fin n → ℕ) (σ : decGroup n p.1.2) :
    primitiveSmallDefect (p, encStrN (strAct w (σ : Perm (Fin n)))) =
      primitiveSmallDefect (p, encStrN w) := by
  have h1 := primitiveSmallDefect_iff hp hϕ hk id (encStrN (strAct w (σ : Perm (Fin n))))
  have h2 := primitiveSmallDefect_iff hp hϕ hk id (encStrN w)
  rw [decStrN_encStrN, hyperColoring_strAct_eq id w σ, colorAut_smul, defect_map_permCongrHom] at h1
  rw [decStrN_encStrN] at h2
  exact Bool.eq_iff_iff.2 (h1.trans h2.symm)

variable {c tt dd : ℕ} (hb : Line4cBounds c tt dd)
    [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))

include hp hϕ hk id hb hK in
/-- One half of canonicity: `σ^ϕ` carries every version of `w` to a version of `w^σ`. -/
theorem smul_line4cVers_subset (x y : RawStr) (w : Fin n → ℕ) (σ : decGroup n p.1.2) :
    ϕ σ • line4cVers c tt dd p t x y m w ⊆
      line4cVers c tt dd p t x y m (strAct w (σ : Perm (Fin n))) := by
  rintro _ ⟨Z, hZ, rfl⟩
  unfold line4cVers at hZ ⊢
  split_ifs at hZ with hrep
  · have hrep' := (extendedInputRep_line4cInput_strAct hp hϕ hk id x y w σ).2 hrep.1
    rw [if_pos ⟨hrep', (primitiveSmallDefect_strAct hp hϕ hk id w σ).trans hrep.2⟩]
    obtain ⟨o, ho, hdec⟩ := hZ
    obtain ⟨o', ho', Z₁, Z₂, h1, h2, hi⟩ := extendedSplitFamily_transport hb.1 hrep.1 hrep'
      rfl rfl (ϕ σ) (iso_line4cInput_strAct hp hϕ hk id x y w σ) ho
    rw [hdec] at h1
    cases h1
    refine ⟨o', ho', ?_⟩
    rw [h2, hi.eq_smul hK]
  · exact absurd hZ (Set.notMem_empty Z)

include hp hϕ hk id hb hK in
/-- **Line 4c on the RAM is canonical** (Sec. 14.2, Theorem 9.2.3): a `G`-shift of the
string shifts the whole family of versions by the corresponding permutation of `Γ`. -/
theorem isCanonicalVersions_line4cVers (x y : RawStr) :
    IsCanonicalVersions ϕ (line4cVers c tt dd p t x y m) := by
  intro w σ
  refine Set.Subset.antisymm ?_ (smul_line4cVers_subset hp hϕ hk id hb hK x y w σ)
  intro Z hZ
  have hback := smul_line4cVers_subset hp hϕ hk id hb hK x y (strAct w (σ : Perm (Fin n)))
    σ⁻¹ ⟨Z, hZ, rfl⟩
  have hw : strAct (strAct w (σ : Perm (Fin n))) ((σ⁻¹ : decGroup n p.1.2) : Perm (Fin n)) =
      w := by
    funext u; simp [strAct]
  rw [hw] at hback
  refine ⟨(ϕ σ)⁻¹ • Z, ?_, smul_inv_smul _ _⟩
  rwa [map_inv] at hback

end Canonical

/-! ### What the Master needs, and the Master's round -/

section Master

variable {n m t : ℕ} {p : RawAction} {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2))) (id : PrimitiveCaseId ϕ t)
    {c tt dd : ℕ} (hb : Line4cBounds c tt dd) {x y : RawStr}
    (hx : x.length = n) (hy : y.length = n)

include hx in
theorem line4cInput_x : line4cInput p t x y (decStrN n x) = line4cAmbient (((p, x, y), t), x) := by
  rw [line4cInput, encStrN_decStrN hx]

include hy in
theorem line4cInput_y : line4cInput p t x y (decStrN n y) = line4cAmbient (((p, x, y), t), y) := by
  rw [line4cInput, encStrN_decStrN hy]

include hp hϕ hk id hb hx hy in
/-- **Section 15, line 4c on the RAM: the specification.** In the primitive case with
`t ≥ 2` and after line 4b's test has failed at `x`, the node's two lists are the canonical
family of versions of Sec. 14.2, read at `x` and at `y`:

* the family is canonical;
* at `x` it is nonempty and is exactly the set of decoded outcomes of the first list;
* at `y` it is the set of decoded outcomes of the second list when line 4b's test fails at
  `y` too, and empty otherwise (then `H(x)` and `H(y)` have different symmetry defects, so
  `x` and `y` are not `G`-isomorphic);
* it is finite, and at `y` it has at most as many members as the second list;
* every member is a colored `3/4`-partition of `Γ` or a Johnson scheme on at least `3m/4`
  points of `Γ` (`Babai.IsSplitOutcome`). -/
theorem line4c_versions_spec (ht2 : 2 ≤ t)
    (hsmall : ¬ defect (colorAut t (hyperColoring id (decStrN n x))) < 1 / 2)
    [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) :
    IsCanonicalVersions ϕ (line4cVers c tt dd p t x y m) ∧
      (line4cVers c tt dd p t x y m (decStrN n x)).Nonempty ∧
      (∀ Z, Z ∈ line4cVers c tt dd p t x y m (decStrN n x) ↔
        ∃ o ∈ (line4cVersions c tt dd ((p, x, y), t)).1, decAlignOutcome m o = some Z) ∧
      (∀ Z, Z ∈ line4cVers c tt dd p t x y m (decStrN n y) ↔
        primitiveSmallDefect (p, y) = false ∧
          ∃ o ∈ (line4cVersions c tt dd ((p, x, y), t)).2, decAlignOutcome m o = some Z) ∧
      (∀ w : Fin n → ℕ, (line4cVers c tt dd p t x y m w).Finite) ∧
      (line4cVers c tt dd p t x y m (decStrN n y)).ncard ≤
        (line4cVersions c tt dd ((p, x, y), t)).2.length ∧
      (∀ w : Fin n → ℕ, ∀ Z ∈ line4cVers c tt dd p t x y m w, IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) Z) := by
  have hrepx : ExtendedInputRep 1 m (line4cInput p t x y (decStrN n x)) ∧
      primitiveSmallDefect (p, encStrN (decStrN n x)) = false := by
    rw [line4cInput_x hx, encStrN_decStrN hx]
    refine ⟨extendedInputRep_line4c hp hϕ hk id x y x (Or.inl rfl) ht2 hsmall, ?_⟩
    rw [← Bool.not_eq_true, primitiveSmallDefect_iff hp hϕ hk id]
    exact hsmall
  refine ⟨isCanonicalVersions_line4cVers hp hϕ hk id hb hK x y,
    line4cVers_nonempty p t x y hb _ hrepx, fun Z => ?_, fun Z => ?_,
    line4cVers_finite c tt dd p t x y, ?_, line4cVers_good p t x y hb⟩
  · unfold line4cVers
    rw [if_pos hrepx, line4cInput_x hx]
    exact Iff.rfl
  · have hiff : (ExtendedInputRep 1 m (line4cInput p t x y (decStrN n y)) ∧
        primitiveSmallDefect (p, encStrN (decStrN n y)) = false) ↔
        primitiveSmallDefect (p, y) = false := by
      rw [line4cInput_y hy, encStrN_decStrN hy]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      refine extendedInputRep_line4c hp hϕ hk id x y y (Or.inr rfl) ht2 ?_
      rw [← primitiveSmallDefect_iff hp hϕ hk id, h]
      exact Bool.false_ne_true
    unfold line4cVers
    split_ifs with hrep
    · rw [line4cInput_y hy]
      exact ⟨fun h => ⟨hiff.1 hrep, h⟩, fun h => h.2⟩
    · exact ⟨fun h => absurd h (Set.notMem_empty Z), fun h => absurd (hiff.2 h.1) hrep⟩
  · have h := ncard_line4cVers_le c tt dd p t x y (m := m) (decStrN n y)
    rwa [line4cInput_y hy] at h

include hp hϕ hk id hb hx hy in
/-- **Sections 15, lines 4c–4d, on the machine's family**: Procedure Align (Sec. 14.1,
`Babai.nonempty_alignData_of_versions`) applied to the canonical versions the RAM node of
line 4c computes, at `α = 3/4`. The number of versions of `y` is the length `V` of the list
the node returns for `y`, and the round makes at most `V(n+1)` Align rounds' worth of calls,
as in Eq. (71). -/
theorem nonempty_line4cdData_ram (hG : IsTransitive (decGroup n p.1.2)) (ht2 : 2 ≤ t)
    (hm : 217 ≤ m) (hmn : m ≤ n)
    (hsmall : ¬ defect (colorAut t (hyperColoring id (decStrN n x))) < 1 / 2) :
    Nonempty (Line4cdData (Fin n) ℕ (decGroup n p.1.2) (decStrN n x) (decStrN n y) m
      ((line4cVersions c tt dd ((p, x, y), t)).2.length * (Fintype.card (Fin n) + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n)))) := by
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  obtain ⟨hcan, ⟨X', hX'⟩, -, -, hfin, hV, hgood⟩ :=
    line4c_versions_spec hp hϕ hk id hb hx hy ht2 hsmall hK
  exact nonempty_alignData_of_versions hG hϕ hk id.tPointOf_eq (by omega)
    (by have := id.four_t; rwa [Fintype.card_fin] at this) hm
    (by rwa [Fintype.card_fin]) hK hcan (hfin _) hV hX' (by norm_num) (by norm_num)
    (by norm_num) (hgood _ X' hX')

end Master

end Algo

#print axioms Algo.isCanonicalVersions_line4cVers
#print axioms Algo.line4c_versions_spec
#print axioms Algo.nonempty_line4cdData_ram
