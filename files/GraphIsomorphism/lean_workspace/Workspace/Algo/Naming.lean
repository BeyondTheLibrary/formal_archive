/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: naming the vertices of an abstract input by `0, …, n − 1`.
-/
import Workspace.Algo.DesignBridge

/-!
# Naming the vertices: the abstract carrier against `Fin n`

Every routine of `Workspace/Algo/` works over `Fin n`, with the vertices named `0, …, n − 1`
(item 3 of `Workspace/Algo/DESIGN.md`).  The mathematical layer of §6–§9 works over an abstract
carrier: a point `X` of a category `Cat Ω` has a vertex set `X.car : Set Ω`, and the objects
attached to it live over the subtype `↥X.car`.  A *naming* of `X` is a bijection
`e : ↥X.car ≃ Fin n`; this file is the dictionary along a naming.

Two halves.

* **Transport of the test of §8.2 across vertex sets.**  `Workspace/DesignLemma/Canonical.lean`
  proves that each ingredient of lines 04–08 is canonical; `Workspace/DesignLemma/Main.lean`
  does the same for `k`-WL across *different* vertex sets, where the `k`-WL color type depends
  on `|Ω|` and the colors have to be moved along an equality of types.  Assembled, they give
  `Algo.returns_canonical` and `Algo.kWL_returns_canonical`: the whole test of lines 04–08 is
  carried by an isomorphism.  These are the statements that let a routine run on the *named*
  copy of an input and report an outcome of the original.
* **The raw form of an abstract structure.**  `Algo.rawStructOf` lists the relations of a
  `k`-ary structure over `Fin n` as lists of tuples, and `Algo.decRel_rawStructOf` says that
  `Algo.decRel` decodes it back.  For a point `X` of `Babai.DesignInputs Ω k α` and a naming
  `e`, `Algo.relsOf X e` is the raw form of `Babai.karyOf X` named by `e`
  (`Algo.decRel_relsOf`).

The two halves meet in `Algo.designOutcome_relsOf_mem_designOut`: run the routine of §8.2 on
the raw form of `X`, and the outcome it returns is attached to a string of `X` at which
Procedure "Design Lemma" returns, so it is a member of `Babai.designOut X` — the family
`Babai.designLemma_finds` finds.  This is the debt **R-A9-6** of the note "A9, session 3" in
`Workspace/Algo/DESIGN.md`.  By `Algo.designOutcome_relabel` the answer does not depend on the
naming `e`.

No axiom and no `sorry`.
-/

universe u

open scoped Classical

namespace Algo

open Babai

/-! ## 1. The test of §8.2 is carried by an isomorphism

Lines 04–08 test four things at the restriction `X_x⃗`: that `x⃗` has distinct entries, that no
vertex-color class is dominant (line 04), that there is a dominant class (line 06), and that the
`2`-skeleton does not induce a clique configuration on it (line 07).  Each is canonical; what is
assembled here is the conjunction, `Babai.KAryPartStruct.Returns`. -/

section Clique

variable {V W : Type*} [Fintype V] [Fintype W]

set_option maxHeartbeats 1000000 in
/-- **A clique configuration is carried by a bijection.**  If `e` carries the color classes of
`S` to those of `T` (`Babai.PartitionStructure.IsColorIso`, the comparison of Def. 3.1.1 that
ignores the names of the colors), then `S` induces a clique configuration on `Δ` exactly when
`T` induces one on `e '' Δ`.  Line 07 of Procedure "Design Lemma" reads this at
`Δ = C(x⃗)`. -/
theorem isCliqueOn_congr_equiv {S : PartitionStructure V} {T : PartitionStructure W}
    {e : V ≃ W} (h : S.IsColorIso T e) {Δ : Set V} {Δ' : Set W} (hΔ : e '' Δ = Δ') :
    S.IsCliqueOn Δ ↔ T.IsCliqueOn Δ' := by
  classical
  subst hΔ
  -- the bijection of the two subsets induced by `e`
  let eΔ : ↥Δ ≃ ↥(e '' Δ) := Equiv.Set.image (e : V → W) Δ e.injective
  have hval : ∀ u : ↥Δ, ((eΔ u : ↥(e '' Δ)) : W) = e (u : V) := fun _ => rfl
  have hsymm : ∀ a : ↥(e '' Δ), e ((eΔ.symm a : ↥Δ) : V) = (a : W) := by
    intro a
    have hv := hval (eΔ.symm a)
    rw [Equiv.apply_symm_apply] at hv
    exact hv.symm
  -- the two induced structures have the same color classes, after transporting along `eΔ`
  have hker : ∀ a b c d : ↥(e '' Δ),
      ((S.induced Δ).congrEquiv eΔ).color a b = ((S.induced Δ).congrEquiv eΔ).color c d
        ↔ (T.induced (e '' Δ)).color a b = (T.induced (e '' Δ)).color c d := by
    intro a b c d
    have h1 := PartitionStructure.induced_color_eq_iff S Δ
      (eΔ.symm a) (eΔ.symm b) (eΔ.symm c) (eΔ.symm d)
    have h2 := PartitionStructure.induced_color_eq_iff T (e '' Δ) a b c d
    have h3 := h ((eΔ.symm a : ↥Δ) : V) ((eΔ.symm b : ↥Δ) : V) ((eΔ.symm c : ↥Δ) : V)
      ((eΔ.symm d : ↥Δ) : V)
    rw [hsymm a, hsymm b, hsymm c, hsymm d] at h3
    exact h1.trans (h3.trans h2.symm)
  have hrank : (S.induced Δ).rank = (T.induced (e '' Δ)).rank := by
    rw [← PartitionStructure.congrEquiv_rank (S.induced Δ) eΔ]
    exact PartitionStructure.rank_congr hker
  unfold PartitionStructure.IsCliqueOn
  -- the `Fintype ↥(e '' Δ)` of the goal and the one of `hrank` are different terms
  have hfix := PartitionStructure.induced_rank_congr T (e '' Δ)
  exact iff_of_eq (congrArg (fun r : ℕ => r = 2) (hrank.trans (hfix _ _)))

end Clique

section Returns

variable {Ω Ω' C : Type*} {k l : ℕ} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

omit [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] in
/-- **A string has distinct entries exactly when its image does.** -/
theorem distinct_tupleMap {f : Ω ≃ Ω'} (x : Str Ω l) :
    Str.Distinct (tupleMap (f : Ω → Ω') x) ↔ Str.Distinct x := by
  constructor
  · intro h i j hij
    exact h (show (tupleMap (f : Ω → Ω') x) i = (tupleMap (f : Ω → Ω') x) j from
      congrArg f hij)
  · intro h i j hij
    exact h (f.injective hij)

/-- **Lines 04–08 are carried by an isomorphism.**  Theorem 8.1.5 ends with *"Canonicity in the
above statements is relative to `x⃗`"*: an isomorphism `f : X → Y` of `k`-ary partition
structures turns the test performed at `x⃗` into the test performed at `x⃗^f`.  The four
ingredients are `Babai.Str.Distinct` (line 03), `Babai.KAryPartStruct.NoDominantColor`
(line 04), `Babai.KAryPartStruct.HasDominantClass` (line 06) and
`Babai.PartitionStructure.IsCliqueOn` of the `2`-skeleton on the dominant class (line 07). -/
theorem returns_canonical {α : ℝ} (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k)
    {f : Ω ≃ Ω'} (hf : f ∈ KAryPartStruct.Iso X Y) (hl : l ≤ k) (x : Str Ω l) :
    KAryPartStruct.Returns α X hl x
      ↔ KAryPartStruct.Returns α Y hl (tupleMap (f : Ω → Ω') x) := by
  classical
  have hres : f ∈ KAryPartStruct.Iso (X.restrTo hl x)
      (Y.restrTo hl (tupleMap (f : Ω → Ω') x)) :=
    KAryPartStruct.restrTo_canonical X Y hl x hf
  set Xr := X.restrTo hl x with hXr
  set Yr := Y.restrTo hl (tupleMap (f : Ω → Ω') x) with hYr
  have hnd : KAryPartStruct.NoDominantColor α Xr ↔ KAryPartStruct.NoDominantColor α Yr :=
    KAryPartStruct.noDominantColor_canonical Xr Yr hres
  have hhd : KAryPartStruct.HasDominantClass α Xr ↔ KAryPartStruct.HasDominantClass α Yr := by
    rw [← KAryPartStruct.not_noDominantColor_iff, ← KAryPartStruct.not_noDominantColor_iff]
    exact not_congr hnd
  have hdom : f '' KAryPartStruct.dominantClass α Xr = KAryPartStruct.dominantClass α Yr :=
    KAryPartStruct.dominantClass_canonical Xr Yr hres
  have hclq : ∀ h2 : l + 2 ≤ k,
      (Xr.skel2 (by omega)).IsCliqueOn (KAryPartStruct.dominantClass α Xr)
        ↔ (Yr.skel2 (by omega)).IsCliqueOn (KAryPartStruct.dominantClass α Yr) := by
    intro h2
    exact isCliqueOn_congr_equiv
      (KAryPartStruct.skel2_canonical Xr Yr (by omega : 2 ≤ k - l) hres) hdom
  rw [KAryPartStruct.Returns, KAryPartStruct.Returns]
  refine and_congr (distinct_tupleMap (f := f) x).symm (or_congr hnd ?_)
  exact exists_congr fun h2 => and_congr hhd (not_congr (hclq h2))

end Returns

section KWL

variable {Ω Ω' : Type*} {C : Type} {k l : ℕ} [Fintype Ω] [DecidableEq Ω]
  [Fintype Ω'] [DecidableEq Ω']

/-- **Lines 04–08 do not see the color type.**  Two `k`-ary partition structures on the same
vertex set whose colors agree up to an equality of color types perform the same test.  This is
the companion of `Babai.KAryPartStruct.returnsAtStruct_cast` for the `Returns` spelling; it is
needed because the `k`-WL color type depends on `|Ω|`. -/
theorem returns_cast {C₁ C₂ : Type u} {α : ℝ} (hC : C₁ = C₂) {X₁ : KAryPartStruct Ω C₁ k}
    {X₂ : KAryPartStruct Ω C₂ k} (hcol : ∀ z, X₂.color z = cast hC (X₁.color z))
    (hl : l ≤ k) (x : Str Ω l) :
    KAryPartStruct.Returns α X₂ hl x ↔ KAryPartStruct.Returns α X₁ hl x := by
  subst hC
  obtain rfl : X₂ = X₁ := KAryPartStruct.eq_of_color_cast hcol
  exact Iff.rfl

/-- **The test of §8.2 is canonical across vertex sets.**  An isomorphism `f : X → Y` of `k`-ary
relational structures on *different* vertex sets turns the test of lines 04–08, performed on
`kWL(X)` at `x⃗`, into the test performed on `kWL(Y)` at `x⃗^f`.  The color types of `kWL(X)` and
`kWL(Y)` differ (the number of rounds is read off `|Ω|`), so the proof goes through the run of
`k`-WL on `Y` with the rounds of `Ω` (`Babai.KAryRelStruct.kWL_iso_aux`) and moves the colors
with `Algo.returns_cast`. -/
theorem kWL_returns_canonical {α : ℝ} (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k)
    {f : Ω ≃ Ω'} (hf : f ∈ KAryRelStruct.Iso X Y) (hl : l ≤ k) (x : Str Ω l) :
    KAryPartStruct.Returns α X.kWL hl x
      ↔ KAryPartStruct.Returns α Y.kWL hl (tupleMap (f : Ω → Ω') x) := by
  classical
  have hN : Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k) :=
    Fintype.card_congr ((Equiv.arrowCongr (Equiv.refl (Fin k)) f).prodCongr
      (Equiv.arrowCongr (Equiv.refl (Fin k)) f))
  have h1 : KAryPartStruct.Returns α X.kWL hl x
      ↔ KAryPartStruct.Returns α (Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))) hl
        (tupleMap (f : Ω → Ω') x) :=
    returns_canonical _ _ (KAryRelStruct.kWL_iso_aux X Y hf) hl x
  have h2 : KAryPartStruct.Returns α Y.kWL hl (tupleMap (f : Ω → Ω') x)
      ↔ KAryPartStruct.Returns α (Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))) hl
        (tupleMap (f : Ω → Ω') x) :=
    returns_cast (congrArg (KAryPartStruct.wlColorType _ k) hN)
      (fun z => KAryRelStruct.kWL_color_cast (Ω := Ω) Y hN z) hl _
  exact h1.trans h2.symm

end KWL

/-! ## 2. The raw form of a `k`-ary structure over `Fin n`

A raw structure is one list of tuples per color (`Algo.RawRelStruct`).  The list of a color is
the list of *all* tuples over `[0, n)` that the relation contains; it is not computable from an
abstract `Set`, and it is not meant to be: it is the specification of what the routine's input
means, and `Algo.decRel` reads it back. -/

section Raw

variable {n k : ℕ}

/-- The raw form of one `k`-ary relation on `Fin n`: the list of the tuples it contains, in the
order of `Algo.tuplesOf`. -/
noncomputable def rawRelOf (n k : ℕ) (R : Set (Str (Fin n) k)) : RawRel :=
  (tuplesOf (List.range n) k).filter
    (fun t => decide (∃ x : Str (Fin n) k, tupleOf x = t ∧ x ∈ R))

/-- **The raw form of a relation lists exactly its tuples.** -/
theorem tupleOf_mem_rawRelOf (R : Set (Str (Fin n) k)) (x : Str (Fin n) k) :
    tupleOf x ∈ rawRelOf n k R ↔ x ∈ R := by
  classical
  rw [rawRelOf, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨y, hy, hyR⟩ := of_decide_eq_true h
    rwa [tupleOf_injective hy] at hyR
  · intro hx
    refine ⟨(mem_tuplesOf _ k _).2 ⟨length_tupleOf x, fun a ha => ?_⟩, ?_⟩
    · exact List.mem_range.2 (tupleOf_lt x ha)
    · exact decide_eq_true ⟨x, rfl, hx⟩

/-- The raw form of a `k`-ary structure over `Fin n` with `r` colors: one list of tuples per
color. -/
noncomputable def rawStructOf (n k r : ℕ) (Y : KAryRelStruct (Fin n) ℕ k) : RawRelStruct :=
  (List.range r).map (fun i => rawRelOf n k (Y.rel i))

@[simp] theorem length_rawStructOf (n k r : ℕ) (Y : KAryRelStruct (Fin n) ℕ k) :
    (rawStructOf n k r Y).length = r := by simp [rawStructOf]

theorem getD_rawStructOf {r : ℕ} (Y : KAryRelStruct (Fin n) ℕ k) {i : ℕ} (hi : i < r) :
    (rawStructOf n k r Y).getD i [] = rawRelOf n k (Y.rel i) := by
  have hlen : i < (rawStructOf n k r Y).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  show ((List.range r).map (fun j => rawRelOf n k (Y.rel j)))[i] = _
  rw [List.getElem_map, List.getElem_range]

/-- **`Algo.decRel` decodes the raw form.**  A `k`-ary structure over `Fin n` all of whose
colors `≥ r` index the empty relation is the decoding of its own raw form with `r` colors. -/
theorem decRel_rawStructOf (n k r : ℕ) (Y : KAryRelStruct (Fin n) ℕ k)
    (hr : ∀ i, r ≤ i → Y.rel i = ∅) :
    decRel n k (rawStructOf n k r Y) = Y := by
  have hcol : ∀ i : ℕ,
      {x : Str (Fin n) k | tupleOf x ∈ (rawStructOf n k r Y).getD i []} = Y.rel i := by
    intro i
    rcases Nat.lt_or_ge i r with hi | hi
    · rw [getD_rawStructOf Y hi]
      ext x
      exact tupleOf_mem_rawRelOf (Y.rel i) x
    · rw [getD_of_length_le (by simpa using hi), hr i hi]
      ext x
      simp
  obtain ⟨rel⟩ := Y
  exact congrArg KAryRelStruct.mk (funext hcol)

end Raw

/-! ## 3. Naming the vertices of an abstract structure

`Algo.nameStruct e X` is the `k`-ary structure `X` with its vertices renamed by `e`.  The naming
is an isomorphism `X → nameStruct e X` on the nose (`Algo.mem_iso_nameStruct`), so §1 carries the
test of §8.2 along it. -/

section Name

variable {V W C : Type*} {k : ℕ}

/-- A `k`-ary relational structure with its vertices renamed by a bijection `e`. -/
def nameStruct (e : V ≃ W) (X : KAryRelStruct V C k) : KAryRelStruct W C k :=
  ⟨fun i => {y | tupleMap (e.symm : W → V) y ∈ X.rel i}⟩

@[simp] theorem mem_nameStruct_rel (e : V ≃ W) (X : KAryRelStruct V C k) (i : C)
    (y : Str W k) : y ∈ (nameStruct e X).rel i ↔ tupleMap (e.symm : W → V) y ∈ X.rel i :=
  Iff.rfl

/-- **The naming is an isomorphism.** -/
theorem mem_iso_nameStruct (e : V ≃ W) (X : KAryRelStruct V C k) :
    e ∈ KAryRelStruct.Iso X (nameStruct e X) := by
  intro i x
  rw [mem_nameStruct_rel]
  have : tupleMap (e.symm : W → V) (tupleMap (e : V → W) x) = x := by
    funext j; simp [tupleMap]
  rw [this]

/-- **The renamed structure has the same empty colors.** -/
theorem nameStruct_rel_eq_empty (e : V ≃ W) (X : KAryRelStruct V C k) {i : C}
    (h : X.rel i = ∅) : (nameStruct e X).rel i = ∅ := by
  ext y
  rw [mem_nameStruct_rel, h]
  simp

end Name

/-! ## 4. R-A9-6: the raw form of an input of the Design Lemma

For a point `X` of `Babai.DesignInputs Ω k α` and a naming `e : ↥X.car ≃ Fin n`, the raw input
of the routine of §8.2 is the list of the relations of `Babai.karyOf X`, named by `e`. -/

section Input

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {k : ℕ} {α : ℝ}

/-- **The raw form of an input of Theorem 8.1.2, named by `e`.**  One list of tuples per
relation of the relational structure `X = (Ω, R)` of Def. 2.3.1, in the order of the colors,
with the vertices named `0, …, n − 1` by `e`. -/
noncomputable def relsOf (X : Pt (DesignInputs Ω k α)) {n : ℕ} (e : ↥X.car ≃ Fin n) :
    RawRelStruct :=
  rawStructOf n k X.obj.1.1.numRel (nameStruct e (karyOf X))

/-- **R-A9-6.**  `Algo.decRel` decodes the raw form of `X` back to `Babai.karyOf X` named by
`e`.  This is the one equality the encoding layer owed to A9 (see the note "A9, session 3" in
`Workspace/Algo/DESIGN.md`): with it, the specification of the routine
(`Algo.designOutcome_spec`), which speaks of `decRel n k rels`, speaks of the input structure
itself. -/
theorem decRel_relsOf (X : Pt (DesignInputs Ω k α)) {n : ℕ} (e : ↥X.car ≃ Fin n) :
    decRel n k (relsOf X e) = nameStruct e (karyOf X) := by
  refine decRel_rawStructOf n k _ _ (fun i hi => ?_)
  refine nameStruct_rel_eq_empty e (karyOf X) ?_
  exact RelStructure.toKAry_rel_of_ge X.obj.1.1 X.obj.1.2 (by omega)

/-- **The routine of §8.2, run on the raw form of `X`, returns an outcome of
`Babai.designOut X`.**  This is the conclusion R-A9-6 asked for: `Algo.designOutcome_spec`
produces a string of `Fin n` at which the test of lines 04–08 fires on `kWL` of the *decoded*
input; `Algo.decRel_relsOf` says the decoded input is `Babai.karyOf X` named by `e`;
`Algo.kWL_returns_canonical` carries the test back to a string `x⃗` of `↥X.car`; and
`Algo.designOutcomeOf_mem_designOut` says the outcome at `x⃗` is a member of the family
`Babai.designLemma_finds` finds.

By `Algo.designOutcome_relabel` the value the routine returns does not depend on the naming
`e`, so nothing here is a choice. -/
theorem designOutcome_relsOf_mem_designOut (X : Pt (DesignInputs Ω k α)) {n : ℕ}
    (e : ↥X.car ≃ Fin n) {c₀ a b : ℕ} {ks : List ℕ}
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c₀ n) {w : List ℕ × (List ℕ × ℕ)}
    (hs : designOutcome c₀ (((ks, List.range n), relsOf X e), (a, b)) = some w) :
    ∃ (l : ℕ) (hl : l < k) (x : Str ↥X.car l),
      w = designOutRaw (designAt c₀ (((ks, List.range n), relsOf X e), (a, b))
          (tupleOf (tupleMap (e : ↥X.car → Fin n) x))) ∧
        Babai.designOutcome X hl.le x ∈ designOut X := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨xs, l, hl, x', hxs, hw, hret, -, -, -, -⟩ :=
    designOutcome_spec (n := n) (k := k) (c₀ := c₀) (ks := ks) (dom := List.range n)
      (α := α) (rels := relsOf X e) (List.nodup_range) (fun c => List.mem_range) hk hb hab
      (by simpa using hg) hs
  -- the test fires on `kWL` of the named input structure
  have hdec : (decRel n k (relsOf X e)).F1.F2.F3 = (nameStruct e (karyOf X)).kWL := by
    rw [← decRel_kWL n k (relsOf X e), decRel_relsOf X e]
  rw [hdec] at hret
  -- carry it back along the naming
  refine ⟨l, hl, tupleMap (e.symm : Fin n → ↥X.car) x', ?_, ?_⟩
  · have hx : tupleMap (e : ↥X.car → Fin n) (tupleMap (e.symm : Fin n → ↥X.car) x') = x' := by
      funext j; simp [tupleMap]
    rw [hx, hxs]
    exact hw
  · refine designOutcomeOf_mem_designOut X hl _ ?_
    refine (kWL_returns_canonical (α := α) (karyOf X) (nameStruct e (karyOf X))
      (mem_iso_nameStruct e (karyOf X)) hl.le _).2 ?_
    have hx : tupleMap (e : ↥X.car → Fin n) (tupleMap (e.symm : Fin n → ↥X.car) x') = x' := by
      funext j; simp [tupleMap]
    rw [hx]
    exact hret

end Input

end Algo
