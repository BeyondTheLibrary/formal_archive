/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure "Design Lemma" (§8.2) on raw data.
-/
import Workspace.Algo.WLVertex
import Workspace.DesignLemma.Defs

/-!
# §8.2 Procedure "Design Lemma" — the test at one string, on raw data

```
Input: a k-ary structure X = (Ω, R) with symmetry defect ≥ 1 − α where 1/2 ≤ α < 1.
Output: (i) or (ii) of Theorem 8.1.5.
01 apply k-WL to X       (: henceforth we assume X is k-ary coherent :)
02 for ℓ = 0 to k − 1
03   for x⃗ ∈ Ω^⟨ℓ⟩
04     if each vertex-color class in the restriction X_x⃗ has size ≤ αn
05     then return the vertex-coloring, exit           (: goal (i) achieved :)
06     else (: we have a unique vertex-color class C(x⃗) of size > αn :)
07       if ℓ ≤ k − 2 and the 2-skeleton (X_x⃗)^{(2)} does not induce
          a clique configuration on C(x⃗) then
08         return X* := (X_x⃗)^{(2)}, exit              (: goal (ii) achieved :)
```

Line 01 is `Algo.wlPipeline` (A8).  This file is the body of lines 03–08, the test performed
at one string `x⃗`; the loop of lines 02–03 is a later session.

The mathematics is `Babai.KAryPartStruct.Returns` (`Workspace/DesignLemma/Defs.lean`).  Read
line by line, the test at `x⃗` uses the `(k−ℓ)`-ary restriction `X_x⃗` only through

* its vertex colors `c_x⃗(u) = c(x⃗ u u … u)` (`Babai.KAryPartStruct.restrTo_color`), and
* its `2`-skeleton colors `c_x⃗^{(2)}(u,v) = c(x⃗ u v v … v)`
  (`Babai.KAryPartStruct.restrTo_skeletonColor2`),

and both are single lookups in the `k`-ary table that line 01 produced.  So the routine never
builds the restricted table and never refines again: individualizing `x⃗` is a change of the
tuple that is read, not a recoloring.  See the note "A9, session 1" in
`Workspace/Algo/DESIGN.md`.

## The raw encoding

`Algo.DIn = ((ks, x⃗), p), (a, b)` with `k = ks.length` the arity carrier, `x⃗` the raw string
of line 03, `p` the table of line 01 (`Algo.RawWL.WF n k p`, so `n = p.1.length`), and
`α = a / b` the threshold of Def. 8.1.1.

No axiom and no `sorry`.  The running times are `Workspace/Algo/DesignPoly.lean`.
-/

open scoped Classical

namespace Algo

open Babai RAM

/-! ## Two counting lemmas

Both are general facts about lists and finite sets, used to turn "the number of distinct
values of a routine" into a `Finset.card`, which is how `PartitionStructure.rank` is
defined. -/

/-- **`RAM.dedupG` counts the distinct entries.**  The deduplicated list has as many entries
as the list has distinct entries. -/
theorem length_dedupG_eq_card (l : List ℕ) :
    (dedupG (([] : List ℕ), l)).length = l.toFinset.card := by
  have hnd := nodup_dedupG l
  have hset : (dedupG (([] : List ℕ), l)).toFinset = l.toFinset := by
    ext c
    simp only [List.mem_toFinset]
    exact mem_dedupG_nil l c
  rw [← hset, List.toFinset_card_of_nodup hnd]

/-- **`RAM.dedupG` decides `Nodup`.**  A list has no repetition exactly when deduplicating it
does not shorten it.  This is the machine form of line 03's `x⃗ ∈ Ω^⟨ℓ⟩`. -/
theorem length_dedupG_eq_iff_nodup (l : List ℕ) :
    (dedupG (([] : List ℕ), l)).length = l.length ↔ l.Nodup := by
  obtain ⟨e, he, hnd, -, hmem⟩ := dedupG_struct l ([] : List ℕ)
  have hde : dedupG (([] : List ℕ), l) = e := by rw [dedupG, he]; simp
  have hsub : e ⊆ l := fun c hc => hmem c hc
  have hsubperm : List.Subperm e l := List.subperm_of_subset hnd hsub
  rw [hde]
  constructor
  · intro hlen
    exact (hsubperm.perm_of_length_le (le_of_eq hlen.symm)).nodup_iff.1 hnd
  · intro hl
    have hsub' : l ⊆ e := fun c hc => by
      have : c ∈ dedupG (([] : List ℕ), l) := (mem_dedupG_nil l c).2 hc
      rwa [hde] at this
    exact le_antisymm hsubperm.length_le (List.subperm_of_subset hl hsub').length_le

/-- **Two colorings with the same color classes realize the same number of colors.**  This is
the bridge between the raw `2`-skeleton colors (naturals read from the table) and the colors
of `Babai.PartitionStructure.ofColoring`, which renames them by `[r]`; `rank` is the number of
realized colors, so only the classes matter. -/
theorem card_image_congr_of_iff {β γ : Type*} [DecidableEq β] [DecidableEq γ] [Inhabited γ]
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ p ∈ s, ∀ q ∈ s, (f p = f q ↔ g p = g q)) :
    (s.image f).card = (s.image g).card := by
  classical
  set F : β → γ := fun c => if hc : ∃ u ∈ s, f u = c then g hc.choose else default with hF
  have hFf : ∀ u ∈ s, F (f u) = g u := by
    intro u hu
    have hex : ∃ w ∈ s, f w = f u := ⟨u, hu, rfl⟩
    have := hex.choose_spec
    rw [hF]
    simp only [dif_pos hex]
    exact (h _ this.1 u hu).1 this.2
  have himg : s.image g = (s.image f).image F := by
    rw [Finset.image_image]
    exact (Finset.image_congr (fun u hu => hFf u hu)).symm
  have hinj : Set.InjOn F (s.image f) := by
    intro c1 hc1 c2 hc2 hc
    obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.1 hc1
    obtain ⟨u2, hu2, rfl⟩ := Finset.mem_image.1 hc2
    rw [hFf u1 hu1, hFf u2 hu2] at hc
    exact (h u1 hu1 u2 hu2).2 hc
  rw [himg, Finset.card_image_of_injOn hinj]

/-! ## The individualized tuple -/

/-- The `k`-tuple `x⃗ u v v … v`, of the arity carried by `ks`: the letter of `x⃗` at each
position below `ℓ = |x⃗|`, then `u` at position `ℓ`, then `v` everywhere above.

One routine serves both reads of the procedure: the vertex color of `u` in `X_x⃗` is read at
`(u, u)` and the `2`-skeleton color of `(u, v)` at `(u, v)`.  It is a `map` over
`ks.zipIdx`, never `List.take`/`List.drop`, which have no `RAM.PolyFun`. -/
def indivTuple (z : (List ℕ × List ℕ) × (ℕ × ℕ)) : List ℕ :=
  z.1.1.zipIdx.map fun r => z.1.2.getD r.2 (if r.2 = z.1.2.length then z.2.1 else z.2.2)

@[simp] theorem length_indivTuple (ks x : List ℕ) (u v : ℕ) :
    (indivTuple ((ks, x), (u, v))).length = ks.length := by
  simp [indivTuple]

theorem getElem_indivTuple (ks x : List ℕ) (u v : ℕ) {i : ℕ}
    (hi : i < (indivTuple ((ks, x), (u, v))).length) :
    (indivTuple ((ks, x), (u, v)))[i] = x.getD i (if i = x.length then u else v) := by
  simp only [indivTuple, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]

/-- **The individualized tuple is the paper's string `x⃗ y⃗`.**  `Babai.KAryPartStruct.fill`
is the concatenation `x⃗ y⃗` written with the arity `k` rather than `ℓ + (k − ℓ)`; this lemma
covers every `y⃗` whose first letter is `u` and whose remaining letters are `v`. -/
theorem indivTuple_eq_fill {n k l : ℕ} {ks : List ℕ} (hk : ks.length = k) (hl : l ≤ k)
    (x : Str (Fin n) l) (u v : Fin n) (y : Str (Fin n) (k - l))
    (hy : ∀ j : Fin (k - l), (y j : ℕ) = if (j : ℕ) = 0 then (u : ℕ) else (v : ℕ)) :
    indivTuple ((ks, tupleOf x), ((u : ℕ), (v : ℕ)))
      = tupleOf (Babai.KAryPartStruct.fill hl x y) := by
  refine List.ext_getElem (by simp [hk]) (fun i h1 h2 => ?_)
  have hlen : (tupleOf x).length = l := by simp
  have hik : i < k := by simpa [hk] using h1
  rw [getElem_indivTuple, getElem_tupleOf, hlen]
  show (tupleOf x).getD i (if i = l then (u : ℕ) else (v : ℕ))
    = ((Babai.KAryPartStruct.fill hl x y ⟨i, hik⟩ : Fin n) : ℕ)
  rw [Babai.KAryPartStruct.fill]
  by_cases hil : i < l
  · rw [dif_pos hil, List.getD_eq_getElem _ _ (by omega : i < (tupleOf x).length),
      getElem_tupleOf]
  · rw [dif_neg hil, List.getD_eq_default _ _ (by omega : (tupleOf x).length ≤ i), hy]
    by_cases hie : i = l
    · rw [if_pos hie, if_pos (by simp [hie] : ((⟨i - l, by omega⟩ : Fin (k - l)) : ℕ) = 0)]
    · rw [if_neg hie, if_neg (by simp; omega : ¬ (((⟨i - l, by omega⟩ : Fin (k - l)) : ℕ) = 0))]

/-! ## Reading the restriction `X_x⃗` -/

/-- The input of the tests: `((ks, x⃗), p), (a, b)` — the arity carrier, the raw string, the
table of line 01, and the threshold `α = a / b` of Def. 8.1.1. -/
abbrev DIn : Type := ((List ℕ × List ℕ) × RawWL) × (ℕ × ℕ)

/-- The `2`-skeleton color `c_x⃗^{(2)}(u, v) = c(x⃗ u v v … v)` of the restriction `X_x⃗`. -/
def restrPairColorAt (w : DIn × (ℕ × ℕ)) : ℕ :=
  tblGet (w.1.1.2.2, indivTuple (w.1.1.1, w.2))

/-- The vertex color `c_x⃗(u) = c(x⃗ u u … u)` of the restriction `X_x⃗`. -/
def restrVColorAt (w : DIn × ℕ) : ℕ := restrPairColorAt (w.1, (w.2, w.2))

/-- The vertex colors of `X_x⃗`, in the order the table lists the vertices. -/
def restrVColors (z : DIn) : List ℕ := z.1.2.1.map fun u => restrVColorAt (z, u)

section Spec

variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}

/-- **The vertex read is the vertex color of the restriction.**  Lines 04–06 of the
procedure: `c_x⃗(u) = c(x⃗ u … u)`. -/
theorem restrVColorAt_spec (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l) (u : Fin n) :
    restrVColorAt ((((ks, tupleOf x), p), (a, b)), (u : ℕ))
      = ((decWL n k p).restrTo hl x).vcolor u := by
  rw [restrVColorAt, restrPairColorAt]
  show tblGet (p.2, indivTuple ((ks, tupleOf x), ((u : ℕ), (u : ℕ))))
    = ((decWL n k p).restrTo hl x).color (fun _ => u)
  rw [indivTuple_eq_fill hk hl x u u (fun _ => u) (fun j => by by_cases h : (j : ℕ) = 0 <;>
    simp [h]), Babai.KAryPartStruct.restrTo_color, decWL_color]

/-- **The pair read is the `2`-skeleton color of the restriction.**  Line 07:
`c_x⃗^{(2)}(u, v) = c(x⃗ u v v … v)`. -/
theorem restrPairColorAt_spec (hk : ks.length = k) (hl : l ≤ k) (h2 : l + 2 ≤ k)
    (x : Str (Fin n) l) (u v : Fin n) :
    restrPairColorAt ((((ks, tupleOf x), p), (a, b)), ((u : ℕ), (v : ℕ)))
      = ((decWL n k p).restrTo hl x).skeletonColor (by norm_num) (by omega) ![u, v] := by
  rw [restrPairColorAt]
  show tblGet (p.2, indivTuple ((ks, tupleOf x), ((u : ℕ), (v : ℕ))))
    = ((decWL n k p).restrTo hl x).color (Str.pad (by norm_num) (k - l) ![u, v])
  rw [indivTuple_eq_fill hk hl x u v (Str.pad (by norm_num) (k - l) ![u, v])
      (fun j => by rw [Str.pad2_val]; by_cases h : (j : ℕ) = 0 <;> simp [h]),
    Babai.KAryPartStruct.restrTo_color, decWL_color]

end Spec

/-! ## Lines 04–06: the size of a vertex-color class, and the dominant class -/

/-- The size of the `c_x⃗`-color class of the color `i`: how many vertices carry it. -/
def classSize (w : DIn × ℕ) : ℕ :=
  (w.1.1.2.1.filter fun y => decide (restrVColorAt (w.1, y) = w.2)).length

/-- Lines 04–05: *"each vertex-color class in the restriction `X_x⃗` has size `≤ αn`"*, with
`α = a / b`: the integer test `b·|C| ≤ a·n`, applied to every realized color.  (An unrealized
color has an empty class, and `0 ≤ αn` because `α ≥ 0`.) -/
def noDominantB (z : DIn) : Bool :=
  ((restrVColors z).filter fun i =>
    !decide (z.2.2 * classSize (z, i) ≤ z.2.1 * z.1.2.1.length)).isEmpty

/-- Line 06: the dominant vertex-color class `C(x⃗)` — the vertices whose own class has size
`> αn`, that is `a·n < b·|C|`.  It is empty when no class is dominant, exactly as
`Babai.KAryPartStruct.dominantClass` is. -/
def dominantList (z : DIn) : List ℕ :=
  z.1.2.1.filter fun u =>
    decide (z.2.1 * z.1.2.1.length + 1 ≤ z.2.2 * classSize (z, restrVColorAt (z, u)))

section Classes

variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}

/-- **The raw class size is the paper's class size.** -/
theorem classSize_spec (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (x : Str (Fin n) l) (i : ℕ) :
    classSize ((((ks, tupleOf x), p), (a, b)), i)
      = (((decWL n k p).restrTo hl x).vclass i).ncard := by
  have hset : ((decWL n k p).restrTo hl x).vclass i
      = {z : Fin n | (z : ℕ) ∈ p.1 ∧
          (fun y => decide (restrVColorAt ((((ks, tupleOf x), p), (a, b)), y) = i)) (z : ℕ)
            = true} := by
    ext z
    simp only [Babai.KAryPartStruct.vclass, Set.mem_setOf_eq, decide_eq_true_eq]
    rw [restrVColorAt_spec hk hl x z]
    exact ⟨fun hz => ⟨mem_dom h z, hz⟩, fun hz => hz.2⟩
  show (p.1.filter fun y =>
      decide (restrVColorAt ((((ks, tupleOf x), p), (a, b)), y) = i)).length = _
  rw [hset]
  exact (ncard_eq_length_filter (n := n) p.1 h.domNodup (fun c hc => (h.domMem c).1 hc)
    (fun y => decide (restrVColorAt ((((ks, tupleOf x), p), (a, b)), y) = i))).symm

theorem card_eq_length_dom (h : RawWL.WF n k p) : p.1.length = n := by
  have : p.1.toFinset = Finset.range n := by
    ext c; simp [List.mem_toFinset, h.domMem c]
  have := congrArg Finset.card this
  rwa [List.toFinset_card_of_nodup h.domNodup, Finset.card_range] at this

/-- **Lines 04–05.**  The Boolean test is the paper's *"each vertex-color class in `X_x⃗` has
size `≤ αn`"*, for the rational threshold `α = a / b`.  (An unrealized color needs no
hypothesis on `α`: its class is empty and `α = a/b ≥ 0`.) -/
theorem noDominantB_spec {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (x : Str (Fin n) l) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) :
    noDominantB (((ks, tupleOf x), p), (a, b)) = true
      ↔ Babai.KAryPartStruct.NoDominantColor α ((decWL n k p).restrTo hl x) := by
  classical
  set z : DIn := (((ks, tupleOf x), p), (a, b)) with hz
  set Y := (decWL n k p).restrTo hl x with hY
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcard : (Fintype.card (Fin n) : ℝ) = (p.1.length : ℝ) := by
    rw [Fintype.card_fin, card_eq_length_dom h]
  -- the integer test and the real inequality agree
  have hkey : ∀ i : ℕ, (b * classSize (z, i) ≤ a * p.1.length)
      ↔ ((Y.vclass i).ncard : ℝ) ≤ α * (Fintype.card (Fin n) : ℝ) := by
    intro i
    rw [hab, hcard, classSize_spec h hk hl x i]
    constructor
    · intro hc
      have : ((b * (Y.vclass i).ncard : ℕ) : ℝ) ≤ ((a * p.1.length : ℕ) : ℝ) := by
        exact_mod_cast hc
      push_cast at this
      rw [div_mul_eq_mul_div, le_div_iff₀ hbR]
      linarith
    · intro hc
      rw [div_mul_eq_mul_div, le_div_iff₀ hbR] at hc
      have : ((b * (Y.vclass i).ncard : ℕ) : ℝ) ≤ ((a * p.1.length : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
  have hEmpty : noDominantB z = true ↔ ∀ i ∈ restrVColors z,
      b * classSize (z, i) ≤ a * p.1.length := by
    rw [noDominantB]
    show (((restrVColors z).filter fun i =>
      !decide (b * classSize (z, i) ≤ a * p.1.length)).isEmpty = true) ↔ _
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    constructor
    · intro hall i hi
      have := hall i hi
      simpa using this
    · intro hall i hi
      simpa using hall i hi
  rw [hEmpty]
  constructor
  · intro hall i
    rw [← hkey i]
    by_cases hi : i ∈ restrVColors z
    · exact hall i hi
    · -- an unrealized color has an empty class, and `0 ≤ αn` because `0 ≤ α`
      have hzero : classSize (z, i) = 0 := by
        rw [classSize, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro y hy hc
        exact hi (List.mem_map.2 ⟨y, hy, of_decide_eq_true hc⟩)
      simp [hzero]
  · intro hno i _
    exact (hkey i).2 (hno i)

/-- **Line 06.**  The raw dominant class is `Babai.KAryPartStruct.dominantClass`. -/
theorem mem_dominantList {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (x : Str (Fin n) l) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) (u : Fin n) :
    (u : ℕ) ∈ dominantList (((ks, tupleOf x), p), (a, b))
      ↔ u ∈ Babai.KAryPartStruct.dominantClass α ((decWL n k p).restrTo hl x) := by
  classical
  set z : DIn := (((ks, tupleOf x), p), (a, b)) with hz
  set Y := (decWL n k p).restrTo hl x with hY
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcard : (Fintype.card (Fin n) : ℝ) = (p.1.length : ℝ) := by
    rw [Fintype.card_fin, card_eq_length_dom h]
  rw [dominantList, List.mem_filter]
  simp only [decide_eq_true_eq]
  have hmem : (u : ℕ) ∈ p.1 := mem_dom h u
  have hcol : restrVColorAt (z, (u : ℕ)) = Y.vcolor u := restrVColorAt_spec hk hl x u
  rw [hcol]
  show ((u : ℕ) ∈ p.1 ∧ a * p.1.length + 1 ≤ b * classSize (z, Y.vcolor u))
    ↔ IsDominant α (Y.vclass (Y.vcolor u))
  rw [classSize_spec h hk hl x (Y.vcolor u)]
  unfold IsDominant
  rw [hab, hcard]
  constructor
  · rintro ⟨-, hc⟩
    have : ((a * p.1.length + 1 : ℕ) : ℝ) ≤ ((b * (Y.vclass (Y.vcolor u)).ncard : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast at this
    rw [div_mul_eq_mul_div, div_lt_iff₀ hbR]
    linarith
  · intro hc
    refine ⟨hmem, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ hbR] at hc
    have : ((a * p.1.length + 1 : ℕ) : ℝ) ≤ ((b * (Y.vclass (Y.vcolor u)).ncard : ℕ) : ℝ) := by
      push_cast
      have h1 : (a : ℝ) * (p.1.length : ℝ) < (b : ℝ) * ((Y.vclass (Y.vcolor u)).ncard : ℝ) := by
        linarith
      have h2 : a * p.1.length < b * (Y.vclass (Y.vcolor u)).ncard := by exact_mod_cast h1
      exact_mod_cast h2
    exact_mod_cast this

/-- Every entry of the dominant class is a vertex. -/
theorem lt_of_mem_dominantList (h : RawWL.WF n k p) {xs : List ℕ} {c : ℕ}
    (hc : c ∈ dominantList (((ks, xs), p), (a, b))) : c < n :=
  (h.domMem c).1 (List.mem_filter.1 hc).1

end Classes

/-! ## Line 07: the clique test on the dominant class

*"the `2`-skeleton `(X_x⃗)^{(2)}` does not induce a clique configuration on `C(x⃗)`"*.  By
Def. 3.1.8 a configuration is the clique configuration exactly when its rank is `2`
(`Babai.PartitionStructure.IsCliqueOn`), and the rank of an induced substructure is the number
of colors realized on it.  So the raw test lists the `2`-skeleton colors on
`C(x⃗) × C(x⃗)`, deduplicates, and compares the length with `2`. -/

/-- The `2`-skeleton colors on `C(x⃗) × C(x⃗)`. -/
def pairColors (z : DIn) : List ℕ :=
  ((dominantList z).map fun u =>
    (dominantList z).map fun v => restrPairColorAt (z, (u, v))).flatten

/-- Line 07: the number of colors the `2`-skeleton realizes on `C(x⃗)`, that is the rank of
`(X_x⃗)^{(2)}[C(x⃗)]`. -/
def cliqueRank (z : DIn) : ℕ := (dedupG (([] : List ℕ), pairColors z)).length

section Clique

variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}

/-- **Line 07.**  The raw count is the rank of the induced `2`-skeleton. -/
theorem cliqueRank_spec {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (h2 : l + 2 ≤ k) (x : Str (Fin n) l) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) :
    cliqueRank (((ks, tupleOf x), p), (a, b))
      = ((((decWL n k p).restrTo hl x).skel2 (by omega)).induced
          (Babai.KAryPartStruct.dominantClass α ((decWL n k p).restrTo hl x))).rank := by
  classical
  set z : DIn := (((ks, tupleOf x), p), (a, b)) with hz
  set Y := (decWL n k p).restrTo hl x with hY
  set Δ := Babai.KAryPartStruct.dominantClass α Y with hΔ
  set S := (Y.skel2 (by omega : 2 ≤ k - l)) with hS
  -- the raw color of a pair of `Δ`
  set g : ↥Δ × ↥Δ → ℕ := fun q => restrPairColorAt (z, (((q.1 : Fin n) : ℕ),
    ((q.2 : Fin n) : ℕ))) with hg
  set f : ↥Δ × ↥Δ → Fin S.rank := fun q => S.color q.1 q.2 with hf
  have hgspec : ∀ q : ↥Δ × ↥Δ, g q
      = Y.skeletonColor (by norm_num) (by omega) ![(q.1 : Fin n), (q.2 : Fin n)] :=
    fun q => restrPairColorAt_spec hk hl h2 x _ _
  -- the raw list of colors is the image of `g`
  have hlist : (pairColors z).toFinset = Finset.univ.image g := by
    ext c
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hc
      rw [pairColors, List.mem_flatten] at hc
      obtain ⟨L, hL, hcL⟩ := hc
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
      obtain ⟨v, hv, hcv⟩ := List.mem_map.1 hcL
      have hun : u < n := lt_of_mem_dominantList (ks := ks) h hu
      have hvn : v < n := lt_of_mem_dominantList (ks := ks) h hv
      refine ⟨(⟨⟨u, hun⟩, ?_⟩, ⟨⟨v, hvn⟩, ?_⟩), hcv⟩
      · exact (mem_dominantList h hk hl x hb hab ⟨u, hun⟩).1 hu
      · exact (mem_dominantList h hk hl x hb hab ⟨v, hvn⟩).1 hv
    · rintro ⟨q, rfl⟩
      rw [pairColors, List.mem_flatten]
      refine ⟨(dominantList z).map fun v => restrPairColorAt (z, (((q.1 : Fin n) : ℕ), v)),
        List.mem_map.2 ⟨((q.1 : Fin n) : ℕ), ?_, rfl⟩,
        List.mem_map.2 ⟨((q.2 : Fin n) : ℕ), ?_, rfl⟩⟩
      · exact (mem_dominantList h hk hl x hb hab _).2 q.1.2
      · exact (mem_dominantList h hk hl x hb hab _).2 q.2.2
  -- the two colorings have the same classes
  have hiff : ∀ q₁ ∈ (Finset.univ : Finset (↥Δ × ↥Δ)), ∀ q₂ ∈ (Finset.univ : Finset (↥Δ × ↥Δ)),
      (f q₁ = f q₂ ↔ g q₁ = g q₂) := by
    intro q₁ _ q₂ _
    rw [hf]
    simp only
    rw [Babai.KAryPartStruct.skel2_color_eq_iff, hgspec q₁, hgspec q₂]
  rw [cliqueRank, length_dedupG_eq_card, hlist,
    ← card_image_congr_of_iff (Finset.univ : Finset (↥Δ × ↥Δ)) f g hiff]
  rfl

/-- **Line 07, as the paper words it.**  The `2`-skeleton induces a clique configuration on
`C(x⃗)` exactly when the raw count is `2`. -/
theorem cliqueRank_eq_two_iff {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (h2 : l + 2 ≤ k) (x : Str (Fin n) l) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) :
    cliqueRank (((ks, tupleOf x), p), (a, b)) = 2
      ↔ (((decWL n k p).restrTo hl x).skel2 (by omega)).IsCliqueOn
          (Babai.KAryPartStruct.dominantClass α ((decWL n k p).restrTo hl x)) := by
  rw [Babai.PartitionStructure.IsCliqueOn, cliqueRank_spec h hk hl h2 x hb hab]

end Clique

/-! ## Line 03 and the whole test -/

/-- Line 03: `x⃗ ∈ Ω^⟨ℓ⟩`, a string of **distinct** vertices.  On raw data that is
`List.Nodup`, decided by `RAM.dedupG`. -/
def nodupB (l : List ℕ) : Bool := decide ((dedupG (([] : List ℕ), l)).length = l.length)

theorem nodupB_eq_true {l : List ℕ} : nodupB l = true ↔ l.Nodup := by
  rw [nodupB, decide_eq_true_eq]
  exact length_dedupG_eq_iff_nodup l

theorem nodup_tupleOf_iff {n k : ℕ} (x : Str (Fin n) k) :
    (tupleOf x).Nodup ↔ Str.Distinct x := by
  rw [tupleOf, List.nodup_ofFn]
  constructor
  · intro hinj i j hij
    exact hinj (by simp [hij])
  · intro hinj i j hij
    exact hinj (Fin.ext hij)

/-- **Lines 03–08 at one string.**  The test the procedure performs at `x⃗`: the string is a
string of distinct vertices, and either no vertex-color class of `X_x⃗` is dominant (line 05),
or `ℓ + 2 ≤ k` and the `2`-skeleton does not induce a clique configuration on the dominant
class (line 08).

The clause *"we have a unique vertex-color class `C(x⃗)`"* of line 06 is not tested: it is the
negation of line 04's test (`Babai.KAryPartStruct.not_noDominantColor_iff`), so
`A ∨ (h ∧ ¬A ∧ B)` and `A ∨ (h ∧ B)` are the same condition. -/
def returnsB (z : DIn) : Bool :=
  if nodupB z.1.1.2 then
    (if noDominantB z then true
      else if decide (z.1.1.2.length + 2 ≤ z.1.1.1.length) then
        !decide (cliqueRank z = 2) else false)
  else false

section Returns

variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}

/-- **The raw test is the paper's test at `x⃗`** (`Babai.KAryPartStruct.Returns`, lines
03–08 of Procedure "Design Lemma"). -/
theorem returnsB_spec {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (x : Str (Fin n) l) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) :
    returnsB (((ks, tupleOf x), p), (a, b)) = true
      ↔ Babai.KAryPartStruct.Returns α (decWL n k p) hl x := by
  classical
  set z : DIn := (((ks, tupleOf x), p), (a, b)) with hz
  set Y := (decWL n k p).restrTo hl x with hY
  have hnd : (nodupB (tupleOf x) = true) ↔ Str.Distinct x := by
    rw [nodupB_eq_true]; exact nodup_tupleOf_iff x
  have hlenx : (tupleOf x).length = l := by simp
  rw [Babai.KAryPartStruct.Returns, returnsB]
  show (if nodupB (tupleOf x) then
      (if noDominantB z then true
        else if decide ((tupleOf x).length + 2 ≤ ks.length) then
          !decide (cliqueRank z = 2) else false) else false) = true ↔ _
  by_cases hd : nodupB (tupleOf x) = true
  · rw [if_pos hd]
    have hdist : Str.Distinct x := hnd.1 hd
    simp only [hdist, true_and]
    by_cases hnodom : noDominantB z = true
    · rw [if_pos hnodom]
      simp only [true_iff]
      exact Or.inl ((noDominantB_spec h hk hl x hb hab).1 hnodom)
    · rw [if_neg hnodom]
      have hnoD : ¬ Babai.KAryPartStruct.NoDominantColor α Y := fun hc =>
        hnodom ((noDominantB_spec h hk hl x hb hab).2 hc)
      by_cases hroom : l + 2 ≤ k
      · rw [if_pos (by simp [hlenx, hk, hroom])]
        rw [Bool.not_eq_true', decide_eq_false_iff_not,
          cliqueRank_eq_two_iff h hk hl hroom x hb hab]
        constructor
        · intro hc
          exact Or.inr ⟨by omega, ⟨(Babai.KAryPartStruct.not_noDominantColor_iff Y).1 hnoD, hc⟩⟩
        · rintro (hc | ⟨h2', hdom', hcl⟩)
          · exact absurd hc hnoD
          · exact hcl
      · rw [if_neg (by simp [hlenx, hk]; omega)]
        simp only [Bool.false_eq_true, false_iff]
        rintro (hc | ⟨h2', -⟩)
        · exact hnoD hc
        · omega
  · rw [if_neg hd]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨hc, -⟩
    exact hd (hnd.2 hc)

end Returns

/-! ## Line 03: the loop over the strings of one length

Line 03 of the procedure is *"for `x⃗ ∈ Ω^⟨ℓ⟩`"*.  The paper prescribes no order on `Ω^⟨ℓ⟩`
(see `Babai.KAryPartStruct.procedure`, which therefore chooses by `Exists.choose`), so the
routine takes the first returning string in the enumeration order of `Algo.tuplesOf`, which is
the order in which the table of `k`-tuples itself is built.  Strings with a repetition are not
filtered out beforehand: `Algo.returnsB` already tests `List.Nodup`, so they never fire.

The outer loop of line 02, `ℓ = 0` to `k − 1`, needs `ℓ` to arrive in the input, hence the
guarded construction of `Workspace/Algo/WLGuarded.lean`; it is the next session. -/

/-- Put a new string into the input of the test, keeping the arity carrier, the table and the
threshold. -/
def withStr (w : DIn × List ℕ) : DIn := (((w.1.1.1.1, w.2), w.1.1.2), w.1.2)

/-- **Lines 03–08 at one length `ℓ`**: the first string of length `ℓ` at which the test of
lines 04–08 fires, and `none` if there is none. -/
def scanLen (l : ℕ) (z : DIn) : Option (List ℕ) :=
  ((tuplesOf z.1.2.1 l).filter fun xs => returnsB (withStr (z, xs))).head?

section Scan

variable {n k l a b : ℕ} {ks x₀ : List ℕ} {p : RawWL}

theorem withStr_eq (xs : List ℕ) :
    withStr ((((ks, x₀), p), (a, b)), xs) = (((ks, xs), p), (a, b)) := rfl

/-- The raw form of a string of length `ℓ` is one of the strings the loop enumerates. -/
theorem tupleOf_mem_tuplesOf (h : RawWL.WF n k p) (x : Str (Fin n) l) :
    tupleOf x ∈ tuplesOf p.1 l :=
  (mem_tuplesOf p.1 l (tupleOf x)).2
    ⟨by simp, fun c hc => (h.domMem c).2 (tupleOf_lt x hc)⟩

/-- **Line 03, the answer.**  A string the loop returns is a string of length `ℓ` at which the
paper's test fires. -/
theorem scanLen_some {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) {xs : List ℕ}
    (hs : scanLen l (((ks, x₀), p), (a, b)) = some xs) :
    ∃ x : Str (Fin n) l, tupleOf x = xs ∧
      Babai.KAryPartStruct.Returns α (decWL n k p) hl x := by
  have hmem : xs ∈ (tuplesOf p.1 l).filter
      fun t => returnsB (withStr ((((ks, x₀), p), (a, b)), t)) :=
    List.mem_of_mem_head? hs
  rw [List.mem_filter] at hmem
  obtain ⟨hxs, hret⟩ := hmem
  obtain ⟨hlen, -⟩ := (mem_tuplesOf p.1 l xs).1 hxs
  obtain ⟨x, rfl⟩ := exists_tupleOf (n := n) hlen
    (fun c hc => (h.domMem c).1 (((mem_tuplesOf p.1 l _).1 hxs).2 c hc))
  exact ⟨x, rfl, (returnsB_spec h hk hl x hb hab).1 (by rwa [withStr_eq] at hret)⟩

/-- **Line 03, exhaustiveness.**  The loop returns nothing exactly when the paper's test fires
at no string of length `ℓ`. -/
theorem scanLen_none_iff {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) :
    scanLen l (((ks, x₀), p), (a, b)) = none
      ↔ ∀ x : Str (Fin n) l, ¬ Babai.KAryPartStruct.Returns α (decWL n k p) hl x := by
  rw [scanLen, List.head?_eq_none_iff, List.filter_eq_nil_iff]
  constructor
  · intro hall x hx
    have hne := hall _ (tupleOf_mem_tuplesOf h x)
    rw [withStr_eq] at hne
    exact hne ((returnsB_spec h hk hl x hb hab).2 hx)
  · intro hno t ht
    obtain ⟨hlen, hlt⟩ := (mem_tuplesOf p.1 l t).1 ht
    obtain ⟨x, rfl⟩ := exists_tupleOf (n := n) hlen
      (fun c hc => (h.domMem c).1 (hlt c hc))
    rw [withStr_eq]
    intro hc
    exact hno x ((returnsB_spec h hk hl x hb hab).1 hc)

end Scan

end Algo
