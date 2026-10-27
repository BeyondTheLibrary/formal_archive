/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, lines 4–8, on the RAM: facts about the machine's dominant color, its window, the
raw colored partition of `ker ψ` in case (A), and the decoded outcomes of Theorem 9.2.3.
-/
import Workspace.Algo.PrimitiveLine4cRoute
import Workspace.Algo.AlignOutcomeDedup
import Workspace.Algo.AlignOutcomeLab
import Workspace.Algo.AggNodeLine57Match
import Workspace.Algo.AlignDomWindows
import Workspace.Algo.AlignDomReps
import Workspace.Master.AlignDominantKer

/-!
# Line 4d: facts about the dominant color on the RAM

These are shared by line 4d with no dominant structure (`Workspace/Algo/PrimitiveLine4d.lean`)
and with one (`Workspace/Algo/PrimitiveLine4dDomData.lean`).

* The dominant points of line 6 are the points of the dominant color, and the dominant class
  has more than half of `Γ` (`Algo.alignRDomPoints_eq`, `Algo.alignRDomColor_dominant_of_wf`);
  its window is `Ω(Δ_j)` (`Algo.winSet_alignRDomWindow_of_wf`).
* Case (A) of line 8, on raw data: the automorphisms of the colored partition
  `Algo.alignKerPartA` (`Algo.colPartIso_alignKerPartA_iff`).
* The decoded outcomes of Theorem 9.2.3, unfolded (`Algo.decAlignPart`,
  `Algo.decAlignJohnsonObj`).
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-! ## The dominant color, read -/

section DomColor

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

/-- The points of `Γ` with a given raw label, counted on the list. -/
theorem length_filter_labAt_eq (lab : RawLab) (k : ℕ) :
    ((List.range m).filter (fun j => decide (labAt lab j = k))).length =
      {γ : Fin m | labAt lab (γ : ℕ) = k}.ncard := by
  classical
  set L := (List.range m).filter (fun j => decide (labAt lab j = k)) with hL
  have hnd : L.Nodup := List.Nodup.filter _ List.nodup_range
  have himg : (fun x : Fin m => (x : ℕ)) '' {γ : Fin m | labAt lab (γ : ℕ) = k} =
      {j : ℕ | j ∈ L} := by
    ext j
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_setOf_eq, hL, List.mem_filter, List.mem_range, decide_eq_true_iff]
      exact ⟨x.isLt, hx⟩
    · intro hj
      rw [Set.mem_setOf_eq, hL, List.mem_filter, List.mem_range, decide_eq_true_iff] at hj
      exact ⟨⟨j, hj.1⟩, hj.2, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg, ← List.coe_toFinset,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- Two different raw labels have at most `m` points between them. -/
theorem ncard_labAt_add_le (lab : RawLab) {k k' : ℕ} (hkk : k ≠ k') :
    {γ : Fin m | labAt lab (γ : ℕ) = k}.ncard + {γ : Fin m | labAt lab (γ : ℕ) = k'}.ncard ≤
      m := by
  classical
  rw [← Set.ncard_union_eq]
  · calc _ ≤ (Set.univ : Set (Fin m)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = m := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  · rw [Set.disjoint_left]
    intro γ h1 h2
    exact hkk (h1.symm.trans h2)

/-- **Line 6: the dominant points are the points of the dominant color.** A point whose color
class has more than half of `Γ` has the color of the first such point, since two different
classes cannot both have more than half of the points. -/
theorem alignRDomPoints_eq (hg : A.2.1.length = m) {lab : RawLab}
    (hd : alignRHasDom (A, lab) = true) :
    alignRDomPoints (A, lab) =
      (List.range m).filter (fun i => decide (labAt lab i = alignRDomColor (A, lab))) := by
  set q : RawAction × RawLab := (A, lab) with hq
  have hlen : 0 < (alignRDomPoints q).length := by
    rw [alignRHasDom, decide_eq_true_iff] at hd; exact hd
  have hi0 : (alignRDomPoints q).getD 0 0 ∈ alignRDomPoints q := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  set i₀ := (alignRDomPoints q).getD 0 0 with hi₀
  have hdc : alignRDomColor q = labAt lab i₀ := rfl
  -- the test of a point, as a count of its label
  have htest : ∀ i, alignRDomTest (q, i) = decide (m < 2 *
      {γ : Fin m | labAt lab (γ : ℕ) = labAt lab i}.ncard) := by
    intro i
    rw [alignRDomTest, ← length_filter_labAt_eq]
    show decide (A.2.1.length < 2 * ((List.range A.2.1.length).filter _).length) = _
    rw [hg]
  have h0 : m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = labAt lab i₀}.ncard := by
    rw [alignRDomPoints, List.mem_filter] at hi0
    have := hi0.2
    rw [htest, decide_eq_true_iff] at this
    exact this
  show (List.range A.2.1.length).filter (fun i => alignRDomTest (q, i)) = _
  rw [hg]
  refine List.filter_congr fun i _ => ?_
  rw [htest, hdc]
  by_cases hi : labAt lab i = labAt lab i₀
  · rw [hi]
    simp only [h0, decide_true]
  · have hsum := ncard_labAt_add_le (m := m) lab hi
    have h1 : ¬ m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = labAt lab i}.ncard := by omega
    simp only [h1, hi, decide_false]

/-- The number of dominant points is the size of the dominant class. -/
theorem length_alignRDomPoints (hg : A.2.1.length = m) {lab : RawLab}
    (hd : alignRHasDom (A, lab) = true) :
    (alignRDomPoints (A, lab)).length =
      {γ : Fin m | labAt lab (γ : ℕ) = alignRDomColor (A, lab)}.ncard := by
  rw [alignRDomPoints_eq hg hd, length_filter_labAt_eq]

/-- The first dominant point is a point of `Γ`. -/
theorem alignRDomFirst_lt (hg : A.2.1.length = m) {lab : RawLab}
    (hd : alignRHasDom (A, lab) = true) : (alignRDomPoints (A, lab)).getD 0 0 < m := by
  have hlen : 0 < (alignRDomPoints (A, lab)).length := by
    rw [alignRHasDom, decide_eq_true_iff] at hd; exact hd
  have hmem : (alignRDomPoints (A, lab)).getD 0 0 ∈ alignRDomPoints (A, lab) := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  set i₀ := (alignRDomPoints (A, lab)).getD 0 0 with hi₀
  rw [alignRDomPoints, List.mem_filter, List.mem_range, hg] at hmem
  exact hmem.1

/-- The window of the color `k`, for a well-formed raw action: `Ω` of the class of `k`. -/
theorem winSet_alignRDomWindow_of_wf (hA : RawAction.WF n m A ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n A.1.2))) (lab : RawLab) (k : ℕ) :
    winSet n (alignRDomWindow ((A, lab), k)) = omegaOf ϕ {γ : Fin m | labAt lab (γ : ℕ) = k} := by
  have h := winSet_alignRDomWindow (gens := A.1.2.map (decPerm n)) (imgs := A.2.2.map (decPerm m))
    (lab := lab) (ϕ := ϕ) hA.1 hA.2.1 hA.2.2.2.2 hϕ hk k
  simp only [map_encPerm_decPerm hA.2.2.1, map_encPerm_decPerm hA.2.2.2.1, Prod.mk.eta] at h
  exact h

/-- Line 6 for a well-formed raw action: the dominant class has more than half of `Γ`. -/
theorem alignRDomColor_dominant_of_wf (hA : RawAction.WF n m A ϕ) {lab : RawLab}
    (hd : alignRHasDom (A, lab) = true) :
    m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = alignRDomColor (A, lab)}.ncard := by
  rw [← length_alignRDomPoints hA.2.1 hd]
  have hlen : 0 < (alignRDomPoints (A, lab)).length := by
    rw [alignRHasDom, decide_eq_true_iff] at hd; exact hd
  have hmem : (alignRDomPoints (A, lab)).getD 0 0 ∈ alignRDomPoints (A, lab) := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  set i₀ := (alignRDomPoints (A, lab)).getD 0 0 with hi₀
  have hdc : alignRDomColor (A, lab) = labAt lab i₀ := rfl
  have h1 := hmem
  rw [alignRDomPoints, List.mem_filter] at h1
  have h2 := h1.2
  rw [alignRDomTest, decide_eq_true_iff] at h2
  rw [length_alignRDomPoints hA.2.1 hd, ← length_filter_labAt_eq, hdc]
  have e : A.2.1.length = m := hA.2.1
  simp only [e] at h2
  exact h2

end DomColor

/-! ## Case (A): the colored partition of `ker ψ` -/

section KerA

variable {m : ℕ} {dom : List ℕ}

/-- The block size depends only on the cell. -/
theorem cpBlockSize_congr (P : RawColPart) {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cpBlockSize ((dom, P), u) = cpBlockSize ((dom, P), v) := by
  simp only [cpBlockSize, h]

/-- A permutation that preserves the cells keeps the size of every block. -/
theorem cpBlockSize_of_cells (hd : dom.length = m) (P : RawColPart) {f : Perm (Fin m)}
    (hf : ∀ u v : Fin m, cellOf P (u : ℕ) = cellOf P (v : ℕ) ↔
      cellOf P ((f u : Fin m) : ℕ) = cellOf P ((f v : Fin m) : ℕ)) (γ : Fin m) :
    cpBlockSize ((dom, P), ((f γ : Fin m) : ℕ)) = cpBlockSize ((dom, P), (γ : ℕ)) := by
  rw [cpBlockSize_eq hd, cpBlockSize_eq hd]
  have hs : {v : Fin m | cellOf P (v : ℕ) = cellOf P ((f γ : Fin m) : ℕ)} =
      f '' {v : Fin m | cellOf P (v : ℕ) = cellOf P (γ : ℕ)} := by
    ext v
    constructor
    · intro hv
      refine ⟨f.symm v, ?_, by simp⟩
      show cellOf P ((f.symm v : Fin m) : ℕ) = cellOf P (γ : ℕ)
      rw [hf]
      simpa using hv
    · rintro ⟨w, hw, rfl⟩
      exact (hf w γ).1 hw
  rw [hs, Set.ncard_image_of_injective _ f.injective]

/-- The raw label of line 4 of a colored partition: the color and the size of the block. -/
theorem labAt_alignOutcomeLab_partition (hd : dom.length = m) (P : RawColPart) (γ : Fin m) :
    labAt (alignOutcomeLab (dom, rawAlignPartition P)) (γ : ℕ) =
      Nat.pair (labAt P.1 (γ : ℕ)) (cpBlockSize ((dom, P), (γ : ℕ))) :=
  labAt_rawOne_map hd _ γ

/-- Equality of the new colors of case (A). -/
theorem alignKerColA_eq_iff (lab : RawLab) (dc : ℕ) (P : RawColPart) (u v : ℕ) :
    alignKerColA (((lab, dc), P), u) = alignKerColA (((lab, dc), P), v) ↔
      (labAt lab u = dc ↔ labAt lab v = dc) ∧ labAt P.1 u = labAt P.1 v ∧
        (labAt lab u = dc → labAt P.2 u = labAt P.2 v) := by
  unfold alignKerColA
  by_cases hu : labAt lab u = dc <;> by_cases hv : labAt lab v = dc <;>
    simp [hu, hv, Nat.pair_eq_pair]

variable (hd : dom.length = m) (P : RawColPart)
include hd

/-- The cells of the colored partition of case (A) are the cells of `X'`: a point of the
dominant class keeps its block, and the new color of a point is determined by its cell. -/
theorem cellOf_alignKerPartA_iff (dc : ℕ) (u v : Fin m) :
    cellOf (alignKerPartA ((alignOutcomeLab (dom, rawAlignPartition P), dc), (dom, P)))
        (u : ℕ) =
      cellOf (alignKerPartA ((alignOutcomeLab (dom, rawAlignPartition P), dc), (dom, P)))
        (v : ℕ) ↔
      cellOf P (u : ℕ) = cellOf P (v : ℕ) := by
  set lab := alignOutcomeLab (dom, rawAlignPartition P)
  have h1 : ∀ w : Fin m, labAt (alignKerPartA ((lab, dc), (dom, P))).1 (w : ℕ) =
      alignKerColA (((lab, dc), P), (w : ℕ)) := fun w => labAt_rawOne_map hd _ w
  have h2 : ∀ w : Fin m, labAt (alignKerPartA ((lab, dc), (dom, P))).2 (w : ℕ) =
      labAt P.2 (w : ℕ) := fun w => labAt_rawOne_map hd _ w
  simp only [cellOf, Prod.mk.injEq, h1, h2, alignKerColA_eq_iff]
  constructor
  · rintro ⟨⟨-, hc, -⟩, hb⟩
    exact ⟨hc, hb⟩
  · rintro ⟨hc, hb⟩
    have hl : labAt lab (u : ℕ) = labAt lab (v : ℕ) := by
      rw [labAt_alignOutcomeLab_partition hd, labAt_alignOutcomeLab_partition hd, hc,
        cpBlockSize_congr P (show cellOf P (u : ℕ) = cellOf P (v : ℕ) from
          Prod.ext hc hb)]
    exact ⟨⟨by rw [hl], hc, fun _ => hb⟩, hb⟩

/-- §14.1, line 8, case (A), **on the raw side**: a permutation of `Γ` is an automorphism of
the colored partition `Algo.alignKerPartA` exactly when it is an automorphism of `X'` that
maps every block inside the class of the label `dc` to itself. -/
theorem colPartIso_alignKerPartA_iff (dc : ℕ) (f : Perm (Fin m)) :
    ColPartIso m (alignKerPartA ((alignOutcomeLab (dom, rawAlignPartition P), dc), (dom, P)))
        (alignKerPartA ((alignOutcomeLab (dom, rawAlignPartition P), dc), (dom, P))) f ↔
      ColPartIso m P P f ∧ ∀ γ : Fin m,
        labAt (alignOutcomeLab (dom, rawAlignPartition P)) (γ : ℕ) = dc →
          cellOf P ((f γ : Fin m) : ℕ) = cellOf P (γ : ℕ) := by
  set lab := alignOutcomeLab (dom, rawAlignPartition P)
  set K := alignKerPartA ((lab, dc), (dom, P))
  have h1 : ∀ w : Fin m, labAt K.1 (w : ℕ) = alignKerColA (((lab, dc), P), (w : ℕ)) :=
    fun w => labAt_rawOne_map hd _ w
  have hcell := cellOf_alignKerPartA_iff hd P dc
  constructor
  · rintro ⟨hc, hp⟩
    have hp' : ∀ u v : Fin m, cellOf P (u : ℕ) = cellOf P (v : ℕ) ↔
        cellOf P ((f u : Fin m) : ℕ) = cellOf P ((f v : Fin m) : ℕ) := by
      intro u v
      rw [← hcell, ← hcell]
      exact hp u v
    have hc' : ∀ u : Fin m, alignKerColA (((lab, dc), P), ((f u : Fin m) : ℕ)) =
        alignKerColA (((lab, dc), P), (u : ℕ)) := by
      intro u; rw [← h1, ← h1]; exact hc u
    refine ⟨⟨fun u => ((alignKerColA_eq_iff lab dc P _ _).1 (hc' u)).2.1, hp'⟩, ?_⟩
    intro γ hγ
    obtain ⟨hiff, hcol, hblk⟩ := (alignKerColA_eq_iff lab dc P _ _).1 (hc' γ)
    exact Prod.ext hcol (hblk (hiff.2 hγ))
  · rintro ⟨⟨hc, hp⟩, hfix⟩
    refine ⟨fun u => ?_, fun u v => ?_⟩
    · rw [h1, h1, alignKerColA_eq_iff]
      have hl : labAt lab ((f u : Fin m) : ℕ) = labAt lab (u : ℕ) := by
        rw [labAt_alignOutcomeLab_partition hd, labAt_alignOutcomeLab_partition hd, hc u,
          cpBlockSize_of_cells hd P hp u]
      refine ⟨by rw [hl], hc u, fun h => ?_⟩
      rw [hl] at h
      exact congrArg Prod.snd (hfix u h)
    · rw [hcell, hcell]
      exact hp u v

end KerA

/-! ## The decoded outcomes, unfolded -/

section Decoded

variable {m : ℕ}

/-- The colored partition of `□X' = Γ` that a raw colored partition decodes to. -/
def decAlignPart (m : ℕ) (P : RawColPart) : ColoredPartition ↥(Set.univ : Set (Fin m)) ℕ where
  color u := (decColPartition m P).color u.val
  part := Setoid.comap Subtype.val (decColPartition m P).part
  part_le_color := fun h => (decColPartition m P).part_le_color h

theorem decAlignPartition_eq (P : RawColPart) :
    decAlignPartition m P = ⟨Set.univ, Sum.inl (decAlignPart m P)⟩ := rfl

theorem decAlignPart_part (P : RawColPart) (x y : ↥(Set.univ : Set (Fin m))) :
    (decAlignPart m P).part x y ↔ cellOf P ((x : Fin m) : ℕ) = cellOf P ((y : Fin m) : ℕ) :=
  Iff.rfl

/-- The Johnson scheme a raw Johnson outcome decodes to. -/
noncomputable def decAlignJohnsonObj {ms ts : ℕ} (J : RawJohnson) (h : J.WF m ms ts) :
    (JohnsonSchemes (Fin m)).Obj (RawJohnson.carrier m J) :=
  ⟨fun u v => rawJDiff (J, (u.val.val, v.val.val)),
    ⟨ms, ts, Equiv.ofBijective _ h.toBinom_bijective, h.two_le, h.params,
      fun u v => rawJDiff_eq_card (h.rowNodup (h.rawJRow_mem u.2))
        (h.rowLt _ (h.rawJRow_mem u.2))⟩⟩

theorem decAlignJohnson_eq {ms ts : ℕ} (J : RawJohnson) (h : J.WF m ms ts) :
    decAlignJohnson J h = ⟨RawJohnson.carrier m J, Sum.inr (decAlignJohnsonObj J h)⟩ := rfl

theorem decAlignJohnsonObj_apply {ms ts : ℕ} (J : RawJohnson) (h : J.WF m ms ts)
    (u v : ↥(RawJohnson.carrier m J)) :
    (decAlignJohnsonObj J h).1 u v =
      (((Equiv.ofBijective _ h.toBinom_bijective u : binom (Fin ms) ts) : Finset (Fin ms)) \
        ((Equiv.ofBijective _ h.toBinom_bijective v : binom (Fin ms) ts) :
          Finset (Fin ms))).card :=
  rawJDiff_eq_card (h.rowNodup (h.rawJRow_mem u.2)) (h.rowLt _ (h.rawJRow_mem u.2))

end Decoded

/-! ## Small facts -/

section Facts

/-- Two filters of `[0, n)` with the same points are the same list. -/
theorem filter_range_eq_of_winSet_eq {n : ℕ} {p p' : ℕ → Bool}
    (h : winSet n ((List.range n).filter p) = winSet n ((List.range n).filter p')) :
    (List.range n).filter p = (List.range n).filter p' := by
  refine List.filter_congr fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hm := congrArg (fun S : Set (Fin n) => (⟨i, hi'⟩ : Fin n) ∈ S) h
  simp only [mem_winSet, List.mem_filter, List.mem_range, hi', true_and, eq_iff_iff] at hm
  cases hp : p i <;> cases hp' : p' i <;> simp_all

/-- In the primitive case, `Ω(Δ)` is not empty once `Δ` has at least `t` points: the point
labelled by a `t`-subset of `Δ` lies in it. -/
theorem omegaOf_nonempty {n m t : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
    (id : PrimitiveCaseId ϕ t) {Δ : Set (Fin m)} (h : t ≤ Δ.ncard) :
    (omegaOf ϕ Δ).Nonempty := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := Δ.toFinset) (n := t)
    (by rw [← Set.ncard_eq_toFinset_card']; exact h)
  refine ⟨id.label.symm ⟨T, hTcard⟩, mem_omegaOf.2 ?_⟩
  have hT : Tpoint ϕ (id.label.symm ⟨T, hTcard⟩) = ((T : Finset (Fin m)) : Set (Fin m)) := by
    have := (id.label_eq (id.label.symm ⟨T, hTcard⟩)).symm
    rw [Equiv.apply_symm_apply] at this
    exact this
  rw [hT]
  intro γ hγ
  have := hTsub hγ
  rwa [Set.mem_toFinset] at this

/-- In case 1 of the repair `m*` is below the guard of `Algo.aggTable`: `m* < 9` or
`2^{m*} < L² ≤ n²`, and both give `m* ≤ (log₂ n + 1)²` once `n ≥ 4`. -/
theorem alignRMs_le_guard {n : ℕ} {A : RawAction} {o : RawAlignOutcome}
    (hd : A.1.1.length = n) (hn : 4 ≤ n) (hs : alignRSmall (A, o) = true) :
    alignRMs (A, o) ≤ guardBound 2 n := by
  have hL : rawMaxOrbit (alignPairG1 (A, o), A.1.1) ≤ n := by
    rw [rawMaxOrbit_eq (alignPairG1_wf hd) hd]
    have := maxOrbitLength_le_card (decGroup n (alignPairG1 (A, o)))
    simpa [Nat.card_eq_fintype_card] using this
  have hv : rawVeryLarge (alignRMs (A, o), rawMaxOrbit (alignPairG1 (A, o), A.1.1)) = false := by
    unfold alignRSmall at hs
    revert hs
    cases rawVeryLarge (alignRMs (A, o), rawMaxOrbit (alignPairG1 (A, o), A.1.1)) <;> simp
  set k := alignRMs (A, o)
  set L := rawMaxOrbit (alignPairG1 (A, o), A.1.1)
  unfold rawVeryLarge at hv
  rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at hv
  unfold guardBound
  set l := Nat.log 2 n with hl
  have hl2 : 2 ≤ l := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hnlt : n < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rcases hv with h9 | hsz
  · nlinarith
  · rw [size_pred_le_iff] at hsz
    push_neg at hsz
    have hpow : 2 ^ k < 2 ^ (2 * l + 2) := by
      calc 2 ^ k < L * L := hsz
        _ ≤ n * n := Nat.mul_le_mul hL hL
        _ < 2 ^ (l + 1) * 2 ^ (l + 1) := Nat.mul_lt_mul'' hnlt hnlt
        _ = 2 ^ (2 * l + 2) := by rw [← pow_add]; ring_nf
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hpow
    nlinarith

end Facts

/-- A raw color class that is not the dominant window has other points. -/
theorem winSet_alignROmegaClass_ne {n : ℕ} {q : RawAction × RawLab} (hlen : q.1.1.1.length = n)
    {u k : ℕ} (hne : alignROmegaClass (q, u) ≠ alignRDomWindow (q, k)) :
    winSet n (alignROmegaClass (q, u)) ≠ winSet n (alignRDomWindow (q, k)) := by
  intro heq
  apply hne
  simp only [alignROmegaClass, alignRDomWindow, hlen] at heq ⊢
  exact filter_range_eq_of_winSet_eq heq


/-! ## A dominant class with a trivial structure -/

section Trivial

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

/-- §14.1, line 7, **the trivial case**: when line 6 finds a dominant class but `m* < 2`, the
outcome is a colored partition and the dominant class is a single block (a Johnson scheme has
`m* ≥ 2t* + 1 ≥ 5`). A block of a `3/4`-partition has at most `3m/4` points, so the dominant
class has at most `3m/4` points. -/
theorem four_mul_ncard_domClass_le (hA : RawAction.WF n m A ϕ) {o : RawAlignOutcome}
    {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    (hZ : IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) X')
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hms : alignRMs (A, o) < 2) :
    4 * {γ : Fin m | labAt (alignOutcomeLab (A.2.1, o)) (γ : ℕ) =
      alignRDomColor (alignRColorOf (A, o))}.ncard ≤ 3 * m := by
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
    -- a block lies inside the class of the label of its points
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
    -- the class is the block of `γ₀`
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
    -- a block has at most `3m/4` points
    set P' := decAlignPart m P
    have hcolor := (alignColor_inl (Set.univ : Set (Fin m)) P' (Set.mem_univ γ₀)).symm.trans
      (alignColor_decAlignPartition hg P γ₀)
    have hbP : (P'.block ⟨γ₀, Set.mem_univ γ₀⟩).ncard = b :=
      congrArg Prod.snd (Sum.inl_injective hcolor)
    letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
    have hZ' : P'.IsAlphaPartition (3 / 4 : ℝ) := hZ.2
    have hρ := hZ'.2
    have hbρ := P'.ncard_block_le_rho ⟨γ₀, Set.mem_univ γ₀⟩
    have hcard : Fintype.card ↥(Set.univ : Set (Fin m)) = m := by
      rw [Fintype.card_eq_nat_card, Nat.card_congr (Equiv.Set.univ (Fin m)), Nat.card_eq_fintype_card,
        Fintype.card_fin]
    rw [hbP] at hbρ
    rw [hcard] at hρ
    have : ((b : ℕ) : ℝ) ≤ 3 / 4 * (m : ℝ) := le_trans (by exact_mod_cast hbρ) hρ
    have : (4 : ℝ) * b ≤ 3 * m := by linarith
    exact_mod_cast this
  · exfalso
    have h1 := hJ.params
    have h2 := hJ.two_le
    have : alignRMs (A, rawAlignJohnson J) = rawJDeg J := rfl
    omega

end Trivial

end Algo
