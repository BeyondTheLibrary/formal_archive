/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the versions of a structure as a set (Def. 6.0.1), on the RAM.
-/
import Workspace.Algo.AlignOutcomeRaw
import Workspace.Algo.AlignJohnsonIso
import Workspace.Algo.AlignStruct
import Workspace.Algo.WFTests

/-!
# Each version once (Def. 6.0.1, Prop. 6.0.4, Eq. (71))

Def. 6.0.1 makes the canonical family `F(Y)` of versions a **set**, and the union of Eq. (40)
(Prop. 6.0.4), which is the union of Eq. (71) in Procedure Align, runs over `Y' ∈ F(Y)` with
pairwise disjoint terms.  The routine of Theorem 9.2.3 on the RAM returns a *list* of raw
outcomes, and two entries may describe the same outcome, or none.  This file removes the
entries that describe no outcome and all but the first of the entries that describe the same
one, so that the list the loop of Eq. (71) runs over lists every version exactly once
(`Algo.rawVersDedup_spec`).  This is what `Babai.Line4cdData.versions_spec` asks of the
Master's list.

Two raw outcomes are compared through what they describe (`Algo.rawOutcomeEq_iff`):
* two colored partitions are equal when they have the same colors and the same cells;
* two Johnson schemes are equal when they have the same carrier and the same edge colors on
  it;
* a colored partition is never a Johnson scheme (`Babai.Cat.sum` has no morphism between
  the two kinds, and `□` is faithful).

## Main results

* `Algo.pt_eq_iff_setCongr` — equality of objects of a category, through `□`;
* `Algo.rawOutcomeOk_iff`, `Algo.rawOutcomeEq_iff` — the two tests, decoded;
* `Algo.rawVersDedup_spec` — the list has each described outcome exactly once;
* `Algo.polyFun_rawVersDedup` — the running time.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

universe u v

/-! ## Equality of objects -/

/-- Two objects of a category are equal exactly when they have the same underlying set and
the identity of that set is a morphism between them (`□` is faithful). -/
theorem pt_eq_iff_setCongr {Ω : Type u} {C : Cat.{u, v} Ω} {X Y : Pt C} :
    X = Y ↔ ∃ h : X.car = Y.car, Equiv.setCongr h ∈ C.IsoP X Y := by
  constructor
  · rintro rfl
    refine ⟨rfl, ?_⟩
    have he : Equiv.setCongr (rfl : X.car = X.car) = Equiv.refl _ := Equiv.ext fun _ => rfl
    rw [he]
    exact C.refl_mem X.obj
  · rintro ⟨h, hi⟩
    exact Cat.faithful_pt h hi

/-! ## The tests -/

/-- Partitions, the test at a point `u`: the same color. -/
def rawPartColorAt (z : (List ℕ × RawColPart × RawColPart) × ℕ) : Bool :=
  decide (labAt z.1.2.1.1 z.2 = labAt z.1.2.2.1 z.2)

/-- Partitions, the test at a pair `(u, v)`: `u` and `v` share a cell in the first exactly
when they do in the second. -/
def rawPartCellAt (z : ((List ℕ × RawColPart × RawColPart) × ℕ) × ℕ) : Bool :=
  decide (cellOf z.1.1.2.1 z.1.2 = cellOf z.1.1.2.1 z.2) ==
    decide (cellOf z.1.1.2.2 z.1.2 = cellOf z.1.1.2.2 z.2)

/-- Partitions, the test at a point `u` against every point. -/
def rawPartRowAt (z : (List ℕ × RawColPart × RawColPart) × ℕ) : Bool :=
  wftAll rawPartCellAt (z, rawOne z.1.1)

/-- **Two raw colored partitions of `Γ` (given by its domain list) describe the same one.** -/
def rawPartSame (z : List ℕ × RawColPart × RawColPart) : Bool :=
  wftAll rawPartColorAt (z, rawOne z.1) && wftAll rawPartRowAt (z, rawOne z.1)

/-- Johnson schemes, the test at a point `u`: in both carriers or in neither. -/
def rawJohnMemAt (z : (List ℕ × RawJohnson × RawJohnson) × ℕ) : Bool :=
  decide (z.2 ∈ z.1.2.1.1) == decide (z.2 ∈ z.1.2.2.1)

/-- Johnson schemes, the test at a pair `(u, v)` of the first carrier: the same edge color. -/
def rawJohnDiffAt (z : ((List ℕ × RawJohnson × RawJohnson) × ℕ) × ℕ) : Bool :=
  !(decide (z.1.2 ∈ z.1.1.2.1.1) && decide (z.2 ∈ z.1.1.2.1.1)) ||
    decide (rawJDiff (z.1.1.2.1, (z.1.2, z.2)) = rawJDiff (z.1.1.2.2, (z.1.2, z.2)))

/-- Johnson schemes, the test at a point `u` against every point. -/
def rawJohnRowAt (z : (List ℕ × RawJohnson × RawJohnson) × ℕ) : Bool :=
  wftAll rawJohnDiffAt (z, rawOne z.1.1)

/-- **Two raw Johnson schemes on `Γ` describe the same one**, if both are well formed. -/
def rawJohnSame (z : List ℕ × RawJohnson × RawJohnson) : Bool :=
  wftAll rawJohnMemAt (z, rawOne z.1) && wftAll rawJohnRowAt (z, rawOne z.1)

/-- **The raw outcome describes an outcome** (`Algo.decAlignOutcome` is not `none`). -/
def rawOutcomeOk (z : List ℕ × RawAlignOutcome) : Bool :=
  z.2.1.elim (z.2.2.elim false fun J => rawJWFb (z.1.length, J))
    (fun _ => z.2.2.elim true fun _ => false)

/-- The comparison of two raw outcomes of the same kind. -/
def rawOutcomeSame (z : List ℕ × RawAlignOutcome × RawAlignOutcome) : Bool :=
  z.2.1.1.elim
    (z.2.1.2.elim false fun J => z.2.2.2.elim false fun J' => rawJohnSame (z.1, J, J'))
    (fun P => z.2.2.1.elim false fun P' => rawPartSame (z.1, P, P'))

/-- **Two raw outcomes describe the same outcome.** -/
def rawOutcomeEq (z : List ℕ × RawAlignOutcome × RawAlignOutcome) : Bool :=
  rawOutcomeOk (z.1, z.2.1) && rawOutcomeOk (z.1, z.2.2) && rawOutcomeSame z

/-! ## The tests, decoded -/

section Spec

variable {m : ℕ} {dom : List ℕ}

theorem mem_rawOne_iff {u : ℕ} : u ∈ rawOne dom ↔ u < dom.length := by
  rw [rawOne, List.mem_range]

private theorem beq_iff {a b : Bool} : (a == b) = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp

/-- **Partitions.** -/
theorem decAlignPartition_eq_iff (hd : dom.length = m) (P P' : RawColPart) :
    decAlignPartition m P = decAlignPartition m P' ↔ rawPartSame (dom, P, P') = true := by
  rw [pt_eq_iff_setCongr]
  simp only [rawPartSame, Bool.and_eq_true, wftAll_eq_true_iff, rawPartColorAt, rawPartRowAt,
    rawPartCellAt, decide_eq_true_eq, beq_iff, mem_rawOne_iff, hd]
  constructor
  · rintro ⟨h, hiso⟩
    obtain ⟨hc, hp⟩ := (hiso : (∀ x, _) ∧ ∀ x y, _)
    refine ⟨fun u hu => ?_, fun u hu v hv => ?_⟩
    · exact (hc ⟨⟨u, hu⟩, trivial⟩).symm
    · exact hp ⟨⟨u, hu⟩, trivial⟩ ⟨⟨v, hv⟩, trivial⟩
  · rintro ⟨hc, hp⟩
    refine ⟨rfl, ?_⟩
    refine (⟨fun x => ?_, fun x y => ?_⟩ : (∀ x, _) ∧ ∀ x y, _)
    · exact (hc x.1.1 x.1.2).symm
    · exact hp x.1.1 x.1.2 y.1.1 y.1.2

/-- **Johnson schemes.** -/
theorem decAlignJohnson_eq_iff (hd : dom.length = m) {J J' : RawJohnson} {ms ts ms' ts' : ℕ}
    (hJ : J.WF m ms ts) (hJ' : J'.WF m ms' ts') :
    decAlignJohnson J hJ = decAlignJohnson J' hJ' ↔ rawJohnSame (dom, J, J') = true := by
  rw [pt_eq_iff_setCongr]
  simp only [rawJohnSame, Bool.and_eq_true, wftAll_eq_true_iff, rawJohnMemAt, rawJohnRowAt,
    rawJohnDiffAt, decide_eq_true_eq, beq_iff, mem_rawOne_iff, hd, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h, hiso⟩
    have hmem : ∀ u : Fin m, (u : ℕ) ∈ J.1 ↔ (u : ℕ) ∈ J'.1 := fun u => Set.ext_iff.1 h u
    refine ⟨fun u hu => hmem ⟨u, hu⟩, fun u hu v hv => ?_⟩
    by_cases hu' : u ∈ J.1
    · by_cases hv' : v ∈ J.1
      · right
        exact (hiso ⟨⟨u, hu⟩, hu'⟩ ⟨⟨v, hv⟩, hv'⟩).symm
      · exact Or.inl (Or.inr hv')
    · exact Or.inl (Or.inl hu')
  · rintro ⟨hmem, hdiff⟩
    have h : RawJohnson.carrier m J = RawJohnson.carrier m J' :=
      Set.ext fun u => hmem u u.2
    refine ⟨h, fun x y => ?_⟩
    rcases hdiff x.1.1 x.1.2 y.1.1 y.1.2 with (hx | hy) | he
    · exact absurd x.2 hx
    · exact absurd y.2 hy
    · exact he.symm

/-- A colored partition is not a Johnson scheme: there is no morphism between the two kinds. -/
theorem decAlignPartition_ne_johnson (P : RawColPart) {J : RawJohnson} {ms ts : ℕ}
    (hJ : J.WF m ms ts) : decAlignPartition m P ≠ decAlignJohnson J hJ := by
  rw [Ne, pt_eq_iff_setCongr]
  rintro ⟨h, hiso⟩
  exact (hiso : _ ∈ (∅ : Set _))

/-- **The first test decoded**: a raw outcome passes exactly when it describes an outcome. -/
theorem rawOutcomeOk_iff (hd : dom.length = m) (o : RawAlignOutcome) :
    rawOutcomeOk (dom, o) = true ↔ (decAlignOutcome m o).isSome := by
  subst hd
  rcases o with ⟨_ | P, _ | J⟩
  · simp [rawOutcomeOk, decAlignOutcome]
  · simp only [rawOutcomeOk, Option.elim, rawJWFb_iff, decAlignOutcome]
    split_ifs with h <;> simp [h]
  · simp [rawOutcomeOk, decAlignOutcome]
  · simp [rawOutcomeOk, decAlignOutcome]

/-- The raw outcomes that describe an outcome: a colored partition, or a well-formed Johnson
scheme. -/
theorem decAlignOutcome_eq_some_iff {o : RawAlignOutcome} {Z : Pt (SplitOutcomes (Fin m))} :
    decAlignOutcome m o = some Z ↔ (∃ P, o = (some P, none) ∧ Z = decAlignPartition m P) ∨
      ∃ J, ∃ h : J.WF m (rawJDeg J) J.2.1, o = (none, some J) ∧ Z = decAlignJohnson J h := by
  rcases o with ⟨_ | P, _ | J⟩
  · simp [decAlignOutcome]
  · simp only [decAlignOutcome]
    split_ifs with h
    · constructor
      · intro hz
        exact Or.inr ⟨J, h, rfl, (Option.some.inj hz).symm⟩
      · rintro (⟨P, hP, -⟩ | ⟨J', h', hJ, hz⟩)
        · simp at hP
        · simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hJ
          subst hJ
          rw [hz]
    · refine ⟨fun h' => absurd h' (by simp), ?_⟩
      rintro (⟨P, hP, -⟩ | ⟨J', h', hJ, -⟩)
      · simp at hP
      · simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hJ
        subst hJ
        exact absurd h' h
  · simp only [decAlignOutcome]
    constructor
    · intro hz
      exact Or.inl ⟨P, rfl, (Option.some.inj hz).symm⟩
    · rintro (⟨P', hP, hz⟩ | ⟨J', h', hJ, -⟩)
      · simp only [Prod.mk.injEq, Option.some.injEq, and_true] at hP
        subst hP
        rw [hz]
      · simp at hJ
  · simp [decAlignOutcome]

/-- **The second test decoded**: two raw outcomes pass exactly when they describe the same
outcome. -/
theorem rawOutcomeEq_iff (hd : dom.length = m) (o o' : RawAlignOutcome) :
    rawOutcomeEq (dom, o, o') = true ↔
      ∃ Z, decAlignOutcome m o = some Z ∧ decAlignOutcome m o' = some Z := by
  have hok := rawOutcomeOk_iff hd o
  have hok' := rawOutcomeOk_iff hd o'
  simp only [rawOutcomeEq, Bool.and_eq_true]
  rw [hok, hok']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨Z', hZ'⟩ := Option.isSome_iff_exists.1 h2
    refine ⟨Z, hZ, ?_⟩
    rw [hZ']
    congr 1
    rcases decAlignOutcome_eq_some_iff.1 hZ with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩ <;>
      rcases decAlignOutcome_eq_some_iff.1 hZ' with ⟨P', rfl, rfl⟩ | ⟨J', hJ', rfl, rfl⟩
    · exact ((decAlignPartition_eq_iff hd P P').2 h3).symm
    · exact absurd h3 (by simp [rawOutcomeSame])
    · exact absurd h3 (by simp [rawOutcomeSame])
    · exact ((decAlignJohnson_eq_iff hd hJ hJ').2 h3).symm
  · rintro ⟨Z, hZ, hZ'⟩
    refine ⟨⟨by rw [hZ]; rfl, by rw [hZ']; rfl⟩, ?_⟩
    rcases decAlignOutcome_eq_some_iff.1 hZ with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩ <;>
      rcases decAlignOutcome_eq_some_iff.1 hZ' with ⟨P', rfl, he⟩ | ⟨J', hJ', rfl, he⟩
    · exact (decAlignPartition_eq_iff hd P P').1 he
    · exact absurd he (decAlignPartition_ne_johnson P hJ')
    · exact absurd he.symm (decAlignPartition_ne_johnson P' hJ)
    · exact (decAlignJohnson_eq_iff hd hJ hJ').1 he

end Spec

/-! ## Each outcome once -/

/-- One step of the deduplication: keep the entry when it describes an outcome that no kept
entry describes. -/
def rawVersStep (z : List ℕ × (List RawAlignOutcome × RawAlignOutcome)) :
    List RawAlignOutcome :=
  if rawOutcomeOk (z.1, z.2.2) && (z.2.1.filter fun o => rawOutcomeEq (z.1, o, z.2.2)).isEmpty
  then z.2.2 :: z.2.1 else z.2.1

/-- Def. 6.0.1 and Eq. (71): **the versions, each once.**  The list of raw outcomes, with the
entries that describe no outcome dropped and each described outcome kept once.  The domain
list `z.1` of `Γ` gives the degree `m`. -/
def rawVersDedup (z : List ℕ × List RawAlignOutcome) : List RawAlignOutcome :=
  List.foldl (fun y a => rawVersStep (z.1, (y, a))) [] z.2

section DedupSpec

variable {m : ℕ} {dom : List ℕ}

/-- A list whose entries all decode is the list of its decodings. -/
theorem map_eq_filterMap_map {l : List RawAlignOutcome}
    (h : ∀ o ∈ l, (decAlignOutcome m o).isSome) :
    l.map (decAlignOutcome m) = (l.filterMap (decAlignOutcome m)).map some := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    rw [List.map_cons, List.filterMap_cons, hZ, ih fun o ho => h o (List.mem_cons_of_mem a ho)]
    rfl

/-- The fold, from any accumulator whose entries decode, with no outcome twice. -/
theorem rawVersFold_spec (hd : dom.length = m) : ∀ (l acc : List RawAlignOutcome),
    (∀ o ∈ acc, (decAlignOutcome m o).isSome) → (acc.filterMap (decAlignOutcome m)).Nodup →
    let r := List.foldl (fun y a => rawVersStep (dom, (y, a))) acc l
    (∀ o ∈ r, (decAlignOutcome m o).isSome) ∧ (r.filterMap (decAlignOutcome m)).Nodup ∧
      ∀ Z, Z ∈ r.filterMap (decAlignOutcome m) ↔
        Z ∈ acc.filterMap (decAlignOutcome m) ∨ ∃ o ∈ l, decAlignOutcome m o = some Z := by
  intro l
  induction l with
  | nil =>
    intro acc h1 h2
    exact ⟨h1, h2, fun Z => by simp⟩
  | cons a t ih =>
    intro acc h1 h2
    simp only [List.foldl_cons]
    by_cases hkeep : (rawOutcomeOk (dom, a) &&
        (acc.filter fun o => rawOutcomeEq (dom, o, a)).isEmpty) = true
    · have hs : rawVersStep (dom, (acc, a)) = a :: acc := by
        rw [rawVersStep]; exact if_pos hkeep
      rw [hs]
      rw [Bool.and_eq_true, rawOutcomeOk_iff hd, List.isEmpty_iff, List.filter_eq_nil_iff] at hkeep
      obtain ⟨hok, hnone⟩ := hkeep
      obtain ⟨Z₀, hZ₀⟩ := Option.isSome_iff_exists.1 hok
      have hnot : Z₀ ∉ acc.filterMap (decAlignOutcome m) := by
        intro hmem
        obtain ⟨o, ho, hoZ⟩ := List.mem_filterMap.1 hmem
        exact hnone o ho ((rawOutcomeEq_iff hd o a).2 ⟨Z₀, hoZ, hZ₀⟩)
      have hfm : (a :: acc).filterMap (decAlignOutcome m) =
          Z₀ :: acc.filterMap (decAlignOutcome m) := by
        rw [List.filterMap_cons, hZ₀]
      obtain ⟨r1, r2, r3⟩ := ih (a :: acc)
        (fun o ho => by
          rcases List.mem_cons.1 ho with rfl | ho
          · exact hok
          · exact h1 o ho)
        (by rw [hfm]; exact List.nodup_cons.2 ⟨hnot, h2⟩)
      refine ⟨r1, r2, fun Z => ?_⟩
      rw [r3, hfm, List.mem_cons]
      constructor
      · rintro ((rfl | hZ) | ⟨o, ho, hoZ⟩)
        · exact Or.inr ⟨a, List.mem_cons_self, hZ₀⟩
        · exact Or.inl hZ
        · exact Or.inr ⟨o, List.mem_cons_of_mem a ho, hoZ⟩
      · rintro (hZ | ⟨o, ho, hoZ⟩)
        · exact Or.inl (Or.inr hZ)
        · rcases List.mem_cons.1 ho with rfl | ho
          · rw [hZ₀] at hoZ
            exact Or.inl (Or.inl (Option.some.inj hoZ).symm)
          · exact Or.inr ⟨o, ho, hoZ⟩
    · have hs : rawVersStep (dom, (acc, a)) = acc := by
        rw [rawVersStep]; exact if_neg hkeep
      rw [hs]
      obtain ⟨r1, r2, r3⟩ := ih acc h1 h2
      refine ⟨r1, r2, fun Z => ?_⟩
      rw [r3]
      constructor
      · rintro (hZ | ⟨o, ho, hoZ⟩)
        · exact Or.inl hZ
        · exact Or.inr ⟨o, List.mem_cons_of_mem a ho, hoZ⟩
      · rintro (hZ | ⟨o, ho, hoZ⟩)
        · exact Or.inl hZ
        · rcases List.mem_cons.1 ho with rfl | ho
          · -- the entry was dropped: it describes nothing, or a kept entry describes it
            rw [Bool.and_eq_true, rawOutcomeOk_iff hd, List.isEmpty_iff, List.filter_eq_nil_iff,
              not_and, hoZ] at hkeep
            have := hkeep rfl
            push_neg at this
            obtain ⟨o', ho', heq⟩ := this
            obtain ⟨Z', h1', h2'⟩ := (rawOutcomeEq_iff hd o' o).1 heq
            rw [hoZ] at h2'
            cases Option.some.inj h2'
            exact Or.inl (List.mem_filterMap.2 ⟨o', ho', h1'⟩)
          · exact Or.inr ⟨o, ho, hoZ⟩

/-- Def. 6.0.1 and Eq. (71): **the deduplicated list lists every described outcome exactly
once.**  Every entry describes an outcome, the described outcomes are pairwise distinct, and
they are the outcomes some entry of the input describes. -/
theorem rawVersDedup_spec (hd : dom.length = m) (l : List RawAlignOutcome) :
    (rawVersDedup (dom, l)).map (decAlignOutcome m) =
        ((rawVersDedup (dom, l)).filterMap (decAlignOutcome m)).map some ∧
      ((rawVersDedup (dom, l)).filterMap (decAlignOutcome m)).Nodup ∧
      ∀ Z, Z ∈ (rawVersDedup (dom, l)).filterMap (decAlignOutcome m) ↔
        ∃ o ∈ l, decAlignOutcome m o = some Z := by
  obtain ⟨h1, h2, h3⟩ := rawVersFold_spec hd l [] (by simp) List.nodup_nil
  refine ⟨map_eq_filterMap_map h1, h2, fun Z => ?_⟩
  rw [rawVersDedup]
  simpa using h3 Z

/-- The shape of the fold: it puts some entries of the list in front of the accumulator. -/
theorem rawVersFold_struct (d : List ℕ) : ∀ (l acc : List RawAlignOutcome),
    ∃ e : List RawAlignOutcome,
      List.foldl (fun y a => rawVersStep (d, (y, a))) acc l = e ++ acc ∧
        e.length ≤ l.length ∧ ∀ k ∈ e, k ∈ l := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨[], by simp, by simp, by simp⟩
  | cons a t ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases hkeep : (rawOutcomeOk (d, a) &&
        (acc.filter fun o => rawOutcomeEq (d, o, a)).isEmpty) = true
    · have hs : rawVersStep (d, (acc, a)) = a :: acc := by
        rw [rawVersStep]; exact if_pos hkeep
      rw [hs]
      obtain ⟨e, he, hl, hm⟩ := ih (a :: acc)
      refine ⟨e ++ [a], by rw [he]; simp, by simp; omega, fun k hk => ?_⟩
      rcases List.mem_append.1 hk with hk | hk
      · exact List.mem_cons_of_mem a (hm k hk)
      · rw [List.mem_singleton.1 hk]; exact List.mem_cons_self
    · have hs : rawVersStep (d, (acc, a)) = acc := by
        rw [rawVersStep]; exact if_neg hkeep
      rw [hs]
      obtain ⟨e, he, hl, hm⟩ := ih acc
      exact ⟨e, he, by simp; omega, fun k hk => List.mem_cons_of_mem a (hm k hk)⟩

theorem length_rawVersDedup_le (l : List RawAlignOutcome) :
    (rawVersDedup (dom, l)).length ≤ l.length := by
  obtain ⟨e, he, hl, -⟩ := rawVersFold_struct dom l []
  rw [rawVersDedup]
  rw [he, List.append_nil]
  exact hl

theorem mem_of_mem_rawVersDedup {l : List RawAlignOutcome} {o : RawAlignOutcome}
    (h : o ∈ rawVersDedup (dom, l)) : o ∈ l := by
  obtain ⟨e, he, -, hm⟩ := rawVersFold_struct dom l []
  rw [rawVersDedup] at h
  rw [he, List.append_nil] at h
  exact hm o h

end DedupSpec

/-! ## The running time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem polyFun_beq {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f)
    (hg : PolyFun g) : PolyFun (fun a => f a == g a) :=
  (PolyFun.ite hf hg (wftPolyFun_not hg)).of_eq (fun a => by
    cases f a <;> cases g a <;> rfl)

private theorem polyFun_or {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f)
    (hg : PolyFun g) : PolyFun (fun a => f a || g a) :=
  (PolyFun.ite hf (polyFun_const true) hg).of_eq (fun a => by cases f a <;> rfl)

private theorem polyFun_cellEq {α : Type*} [Enc α] {P : α → RawColPart} {u v : α → ℕ}
    (hP : PolyFun P) (hu : PolyFun u) (hv : PolyFun v) :
    PolyFun (fun a => decide (cellOf (P a) (u a) = cellOf (P a) (v a))) := by
  have h1 := (hP.pair hu).comp polyFun_cellOfPair
  have h2 := (hP.pair hv).comp polyFun_cellOfPair
  have e1 : PolyFun (fun a => decide ((cellOf (P a) (u a)).1 = (cellOf (P a) (v a)).1)) :=
    ((pfst h1).pair (pfst h2)).comp polyFun_natEq
  have e2 : PolyFun (fun a => decide ((cellOf (P a) (u a)).2 = (cellOf (P a) (v a)).2)) :=
    ((psnd h1).pair (psnd h2)).comp polyFun_natEq
  exact (wftPolyFun_and e1 e2).of_eq (fun a => by
    simp only [Bool.decide_and, Prod.ext_iff])

theorem polyFun_rawPartSame : PolyFun rawPartSame := by
  have hcol : PolyFun rawPartColorAt := by
    have i : PolyFun (fun z : (List ℕ × RawColPart × RawColPart) × ℕ => z) := polyFun_id
    exact (((pfst (pfst (psnd (pfst i)))).pair (psnd i)).comp polyFun_labAtPair |>.pair
      (((pfst (psnd (psnd (pfst i)))).pair (psnd i)).comp polyFun_labAtPair)).comp polyFun_natEq
  have hcell : PolyFun rawPartCellAt := by
    have i : PolyFun (fun z : ((List ℕ × RawColPart × RawColPart) × ℕ) × ℕ => z) := polyFun_id
    exact polyFun_beq (polyFun_cellEq (pfst (psnd (pfst (pfst i)))) (psnd (pfst i)) (psnd i))
      (polyFun_cellEq (psnd (psnd (pfst (pfst i)))) (psnd (pfst i)) (psnd i))
  have hrow : PolyFun rawPartRowAt := by
    have i : PolyFun (fun z : (List ℕ × RawColPart × RawColPart) × ℕ => z) := polyFun_id
    exact (i.pair ((pfst (pfst i)).comp polyFun_rawOne)).comp (wftPolyFun_all hcell)
  have i : PolyFun (fun z : List ℕ × RawColPart × RawColPart => z) := polyFun_id
  exact wftPolyFun_and ((i.pair ((pfst i).comp polyFun_rawOne)).comp (wftPolyFun_all hcol))
    ((i.pair ((pfst i).comp polyFun_rawOne)).comp (wftPolyFun_all hrow))

theorem polyFun_rawJDiff : PolyFun rawJDiff := by
  have i : PolyFun (fun p : RawJohnson × (ℕ × ℕ) => p) := polyFun_id
  have r1 := ((pfst i).pair (pfst (psnd i))).comp polyFun_rawJRow
  have r2 := ((pfst i).pair (psnd (psnd i))).comp polyFun_rawJRow
  have hq : PolyFun (fun w : List ℕ × ℕ => !decide (w.2 ∈ w.1)) :=
    wftPolyFun_not ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
  exact ((r2.pair r1).comp (PolyFun.filterParam hq)).comp polyFun_length |>.of_eq
    (fun _ => rfl)

theorem polyFun_rawJohnSame : PolyFun rawJohnSame := by
  have hmem : PolyFun rawJohnMemAt := by
    have i : PolyFun (fun z : (List ℕ × RawJohnson × RawJohnson) × ℕ => z) := polyFun_id
    exact polyFun_beq (((psnd i).pair (pfst (pfst (psnd (pfst i))))).comp polyFun_natListMem)
      (((psnd i).pair (pfst (psnd (psnd (pfst i))))).comp polyFun_natListMem)
  have hdiff : PolyFun rawJohnDiffAt := by
    have i : PolyFun (fun z : ((List ℕ × RawJohnson × RawJohnson) × ℕ) × ℕ => z) := polyFun_id
    have hJ := pfst (psnd (pfst (pfst i)))
    have hJ' := psnd (psnd (pfst (pfst i)))
    have hu := psnd (pfst i)
    have hv := psnd i
    exact polyFun_or (wftPolyFun_not (wftPolyFun_and
        ((hu.pair (pfst hJ)).comp polyFun_natListMem)
        ((hv.pair (pfst hJ)).comp polyFun_natListMem)))
      (((hJ.pair (hu.pair hv)).comp polyFun_rawJDiff).pair
        ((hJ'.pair (hu.pair hv)).comp polyFun_rawJDiff) |>.comp polyFun_natEq)
  have hrow : PolyFun rawJohnRowAt := by
    have i : PolyFun (fun z : (List ℕ × RawJohnson × RawJohnson) × ℕ => z) := polyFun_id
    exact (i.pair ((pfst (pfst i)).comp polyFun_rawOne)).comp (wftPolyFun_all hdiff)
  have i : PolyFun (fun z : List ℕ × RawJohnson × RawJohnson => z) := polyFun_id
  exact wftPolyFun_and ((i.pair ((pfst i).comp polyFun_rawOne)).comp (wftPolyFun_all hmem))
    ((i.pair ((pfst i).comp polyFun_rawOne)).comp (wftPolyFun_all hrow))

theorem polyFun_rawOutcomeOk : PolyFun rawOutcomeOk := by
  have i : PolyFun (fun z : List ℕ × RawAlignOutcome => z) := polyFun_id
  have hJ : PolyFun (fun w : RawJohnson × (List ℕ × RawAlignOutcome) =>
      rawJWFb (w.2.1.length, w.1)) :=
    (((pfst polyFun_snd).comp polyFun_length).pair polyFun_fst).comp polyFun_rawJWFb
  have hnoneJ : PolyFun (fun z : List ℕ × RawAlignOutcome =>
      z.2.2.elim false fun J => rawJWFb (z.1.length, J)) :=
    ((psnd (psnd i)).pair i).comp (PolyFun.optionElim (polyFun_const false) hJ)
  have hP : PolyFun (fun w : RawColPart × (List ℕ × RawAlignOutcome) =>
      w.2.2.2.elim true fun _ => false) :=
    ((psnd (psnd polyFun_snd)).pair polyFun_snd).comp
      (PolyFun.optionElim (polyFun_const true) (polyFun_const false))
  exact ((pfst (psnd i)).pair i).comp (PolyFun.optionElim hnoneJ hP) |>.of_eq (fun _ => rfl)

theorem polyFun_rawOutcomeSame : PolyFun rawOutcomeSame := by
  have i : PolyFun (fun z : List ℕ × RawAlignOutcome × RawAlignOutcome => z) := polyFun_id
  -- the Johnson branch
  have hJJ : PolyFun (fun w : RawJohnson × (RawJohnson × (List ℕ × RawAlignOutcome ×
      RawAlignOutcome)) => rawJohnSame (w.2.2.1, w.2.1, w.1)) :=
    ((pfst (psnd polyFun_snd)).pair ((pfst polyFun_snd).pair polyFun_fst)).comp
      polyFun_rawJohnSame
  have hJ : PolyFun (fun w : RawJohnson × (List ℕ × RawAlignOutcome × RawAlignOutcome) =>
      w.2.2.2.2.elim false fun J' => rawJohnSame (w.2.1, w.1, J')) :=
    ((psnd (psnd (psnd polyFun_snd))).pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_const false) hJJ)
  have hnone : PolyFun (fun z : List ℕ × RawAlignOutcome × RawAlignOutcome =>
      z.2.1.2.elim false fun J => z.2.2.2.elim false fun J' => rawJohnSame (z.1, J, J')) :=
    ((psnd (pfst (psnd i))).pair i).comp (PolyFun.optionElim (polyFun_const false) hJ)
  -- the partition branch
  have hPP : PolyFun (fun w : RawColPart × (RawColPart × (List ℕ × RawAlignOutcome ×
      RawAlignOutcome)) => rawPartSame (w.2.2.1, w.2.1, w.1)) :=
    ((pfst (psnd polyFun_snd)).pair ((pfst polyFun_snd).pair polyFun_fst)).comp
      polyFun_rawPartSame
  have hP : PolyFun (fun w : RawColPart × (List ℕ × RawAlignOutcome × RawAlignOutcome) =>
      w.2.2.2.1.elim false fun P' => rawPartSame (w.2.1, w.1, P')) :=
    ((pfst (psnd (psnd polyFun_snd))).pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_const false) hPP)
  exact ((pfst (pfst (psnd i))).pair i).comp (PolyFun.optionElim hnone hP) |>.of_eq
    (fun _ => rfl)

theorem polyFun_rawOutcomeEq : PolyFun rawOutcomeEq := by
  have i : PolyFun (fun z : List ℕ × RawAlignOutcome × RawAlignOutcome => z) := polyFun_id
  exact wftPolyFun_and (wftPolyFun_and (((pfst i).pair (pfst (psnd i))).comp polyFun_rawOutcomeOk)
    (((pfst i).pair (psnd (psnd i))).comp polyFun_rawOutcomeOk)) polyFun_rawOutcomeSame

theorem polyFun_rawVersStep : PolyFun rawVersStep := by
  have i : PolyFun (fun z : List ℕ × (List RawAlignOutcome × RawAlignOutcome) => z) :=
    polyFun_id
  have hq : PolyFun (fun w : (List ℕ × RawAlignOutcome) × RawAlignOutcome =>
      rawOutcomeEq (w.1.1, w.2, w.1.2)) :=
    ((pfst polyFun_fst).pair (polyFun_snd.pair (psnd polyFun_fst))).comp polyFun_rawOutcomeEq
  have hempty : PolyFun (fun z : List ℕ × (List RawAlignOutcome × RawAlignOutcome) =>
      (z.2.1.filter fun o => rawOutcomeEq (z.1, o, z.2.2)).isEmpty) :=
    (((pfst i).pair (psnd (psnd i))).pair (pfst (psnd i))).comp (PolyFun.filterParam hq) |>.comp
      polyFun_isEmpty
  have htest := wftPolyFun_and (((pfst i).pair (psnd (psnd i))).comp polyFun_rawOutcomeOk) hempty
  exact PolyFun.ite htest (((psnd (psnd i)).pair (pfst (psnd i))).comp polyFun_cons)
    (pfst (psnd i))

theorem polyFun_rawVersDedup : PolyFun rawVersDedup := by
  have hacc : ∀ (cc : List ℕ) (x : List RawAlignOutcome) (r : List RawAlignOutcome) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawVersStep (cc, (y, a))) x (r.take j))
        ≤ (fun N => N + (1 + N * (2 * N + 1)))
          (Enc.size ((cc, (x, r)) : List ℕ × (List RawAlignOutcome × List RawAlignOutcome))) := by
    intro cc x r j
    obtain ⟨e, he, hlen, hmem⟩ := rawVersFold_struct cc (r.take j) x
    rw [he]
    set N := Enc.size ((cc, (x, r)) : List ℕ × (List RawAlignOutcome × List RawAlignOutcome))
      with hN
    have hxr : Enc.size ((x, r) : List RawAlignOutcome × List RawAlignOutcome) ≤ N :=
      Combine.size_snd_le _ _
    have hx : Enc.size x ≤ N := (Combine.size_fst_le x r).trans hxr
    have hr : Enc.size r ≤ N := (Combine.size_snd_le x r).trans hxr
    have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have hlen2 : (r.take j).length ≤ N := by
      have h1 : (r.take j).length ≤ Enc.size (r.take j) := length_le_size _
      omega
    have hentry : ∀ k ∈ e, Enc.size k ≤ N := by
      intro k hk
      have h1 : Enc.size k ≤ Enc.size (r.take j) := size_mem_le (hmem k hk)
      omega
    have hsize := size_list_le_of_entries e N hentry
    have hmul : e.length * (2 * N + 1) ≤ N * (2 * N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have happ := size_append_le e x
    dsimp only
    omega
  have hfold := PolyFun.foldlParam polyFun_rawVersStep
    (p := fun N => N + (1 + N * (2 * N + 1)))
    (polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))))
    hacc
  have hin : PolyFun (fun z : List ℕ × List RawAlignOutcome =>
      ((z.1, (([] : List RawAlignOutcome), z.2)) :
        List ℕ × (List RawAlignOutcome × List RawAlignOutcome))) :=
    polyFun_fst.pair (polyFun_nil.pair polyFun_snd)
  exact (hin.comp hfold).of_eq (fun _ => rfl)

end Algo
#print axioms Algo.rawVersDedup_spec
#print axioms Algo.polyFun_rawVersDedup
