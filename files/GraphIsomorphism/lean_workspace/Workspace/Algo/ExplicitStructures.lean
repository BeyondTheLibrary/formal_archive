import Workspace.Algo.WFTests
import Workspace.Prelim.Structures
import Workspace.Prelim.Hypergraphs

/-!
# §2.3 and §2.5 on the RAM: explicit structures, twins, symmetry defect

Version 2.5 makes three polynomial-time claims about *explicit* structures, that is, structures
whose relations (or hyperedges) are given as lists:

* Prop. 2.3.6: "Given two explicit relational structures `X = (Ω, R)` and `X' = (Ω', R')` and a
  bijection `σ : Ω → Ω'`, one can decide … whether `σ ∈ Iso(X, X')`.  In particular, given an
  explicit relational structure `X = (Ω, R)` and a permutation `σ ∈ S(Ω)`, one can decide …
  whether `σ ∈ Aut(X)`."  The paper says "in linear time", and adds in the proof: "Performing
  this test in polynomial time would be straightforward and we shall never need more than
  that."  This file proves the polynomial-time test; the linear-time bound is the statement
  `Algo.Proposition_2_3_6_linear_statement`, proved as
  `Algo.ExplLinear.proposition_2_3_6_linear` in `Workspace/Algo/ExplLinear.lean`.
* Obs. 2.3.17: "one can find the twin equivalence classes in polynomial time (test each
  transposition).  Therefore, the symmetricity and the symmetry defect of explicit relational
  structures can also be computed in polynomial time."
* Obs. 2.5.8: "Candidate isomorphisms (and therefore automorphisms) of explicit hypergraphs can
  be tested in polynomial time (cf. Prop. 2.3.6).  In particular, one can find the twin
  equivalence classes of an explicit hypergraph in polynomial time.  Consequently, the symmetry
  defect of a hypergraph can also be computed in polynomial time."

## Encodings

The domain is `[0, n)`, given by a list of length `n` (its entries are not read).  The domain has
to be given as a list and not as the number `n`: the output of the twin-class routine has about
`n` entries, which is not polynomial in the bit length of `n`.

* An explicit relational structure is `List (ℕ × List (List ℕ))`: for each relation its arity and
  the list of its tuples (`Algo.decExpl`).  Listed tuples of the wrong length or with an entry
  `≥ n` are not tuples of `[0, n)` and are ignored.
* An explicit hypergraph is `List (List ℕ)`: the list of its hyperedges, each as a list of
  points, repetitions allowed (`Algo.decHyp`).
* A bijection `σ : [0,n) → [0,n)` is a raw permutation (`Algo.encPerm`).

## The routines and what they compute

* `Algo.rawExplIsoTest`, `Algo.rawExplIsoTest_spec`, `Algo.polyFun_rawExplIsoTest` (Prop. 2.3.6,
  both parts: `Aut(X) = Iso(X, X)`);
* `Algo.rawHypIsoTest`, `Algo.rawHypIsoTest_spec`, `Algo.polyFun_rawHypIsoTest` (Obs. 2.5.8, first
  sentence);
* for any automorphism test, generically: `Algo.rawTwinClasses` (the twin equivalence classes,
  `Algo.mem_rawTwinClasses`), `Algo.rawSymmetricity` (`Algo.rawSymmetricity_eq`), and
  `Algo.rawSymDefect` (`Algo.rawSymDefect_eq`, and `Algo.defect_eq_rawSymDefect` for the relative
  defect);
* instantiated for explicit relational structures (Obs. 2.3.17): `Algo.explTwinClasses`,
  `Algo.explSymmetricity`, `Algo.explSymDefect` with their `_spec`s and `polyFun_`s;
* and for explicit hypergraphs (Obs. 2.5.8): `Algo.hypTwinClasses`, `Algo.hypSymmetricity`,
  `Algo.hypSymDefect`.

No axiom, no `sorry`.
-/

namespace Algo

open Babai RAM
open Equiv (Perm)

/-! ## Maxima of lists -/

theorem foldl_max_spec (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧
      (l.foldl max a = a ∨ l.foldl max a ∈ l) := by
  induction l generalizing a with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (max a x)
    refine ⟨le_trans (le_max_left _ _) h1, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_trans (le_max_right _ _) h1
      · exact h2 y hy
    · rcases h3 with h | h
      · rcases le_total a x with hle | hle
        · right; rw [h, max_eq_right hle]; exact List.mem_cons_self
        · left; rw [h, max_eq_left hle]
      · right; exact List.mem_cons_of_mem _ h

theorem polyFun_foldlMax : PolyFun (fun l : List ℕ => l.foldl max 0) := by
  have hf : PolyFun (fun z : ℕ × ℕ => max z.1 z.2) := polyFun_max
  have hacc : ∀ (a : ℕ) (l : List ℕ) (j : ℕ),
      Enc.size ((l.take j).foldl max a) ≤ Enc.size (a, l) := by
    intro a l j
    rcases (foldl_max_spec (l.take j) a).2.2 with he | hm
    · rw [he]; exact Combine.size_fst_le _ _
    · exact le_trans (size_mem_le (List.mem_of_mem_take hm)) (Combine.size_snd_le _ _)
  exact (((polyFun_const (0 : ℕ)).pair polyFun_id).comp
    (PolyFun.foldl hf polyBound_id hacc)).of_eq (fun _ => rfl)

/-- The maximum of `f` over `[0, n)`, computed as a fold, is the supremum over `Fin n`. -/
theorem foldl_max_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).foldl max 0 = Finset.univ.sup (fun u : Fin n => f u) := by
  obtain ⟨-, h2, h3⟩ := foldl_max_spec ((List.range n).map f) 0
  apply le_antisymm
  · rcases h3 with h | h
    · rw [h]; exact Nat.zero_le _
    · obtain ⟨u, hu, he⟩ := List.mem_map.1 h
      rw [← he]
      exact Finset.le_sup (f := fun u : Fin n => f u) (Finset.mem_univ ⟨u, List.mem_range.1 hu⟩)
  · refine Finset.sup_le fun u _ => h2 _ ?_
    exact List.mem_map.2 ⟨u, List.mem_range.2 u.isLt, rfl⟩

/-- Filtering `[0, n)` counts the points of `Fin n` that pass the test. -/
theorem length_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = (Finset.univ.filter (fun u : Fin n => p u = true)).card := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.length_map,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext u
  simp

/-! ## Transpositions -/

/-- The image of a point under the transposition of two points. -/
def transpImage (p : (ℕ × ℕ) × ℕ) : ℕ :=
  if p.2 = p.1.1 then p.1.2 else if p.2 = p.1.2 then p.1.1 else p.2

theorem polyFun_transpImage : PolyFun transpImage :=
  (PolyFun.ite (polyFun_snd.natEq (polyFun_fst.comp polyFun_fst)) (polyFun_fst.comp polyFun_snd)
    (PolyFun.ite (polyFun_snd.natEq (polyFun_fst.comp polyFun_snd))
      (polyFun_fst.comp polyFun_fst) polyFun_snd)).of_eq (fun p => by simp [transpImage])

/-- The raw transposition `(u v)` of the domain `[0, n)`, `n` the length of the list. -/
def rawTransp (p : List ℕ × (ℕ × ℕ)) : RawPerm :=
  (List.range p.1.length).map (fun z => transpImage (p.2, z))

theorem polyFun_rawTransp : PolyFun rawTransp :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_transpImage)).of_eq (fun _ => rfl)

theorem rawTransp_eq {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (u v : Fin n) :
    rawTransp (dom, ((u : ℕ), (v : ℕ))) = encPerm n (Equiv.swap u v) := by
  apply List.ext_getElem
  · simp [rawTransp, hd]
  · intro j h1 _
    have hj : j < n := by simpa [rawTransp, hd] using h1
    rw [getElem_encPerm n _ j hj]
    simp only [rawTransp, List.getElem_map, List.getElem_range, transpImage,
      Equiv.swap_apply_def]
    by_cases hju : (⟨j, hj⟩ : Fin n) = u
    · subst hju; simp
    · by_cases hjv : (⟨j, hj⟩ : Fin n) = v
      · subst hjv
        have : j ≠ (u : ℕ) := fun h => hju (Fin.ext h)
        simp [this, hju]
      · have h1 : j ≠ (u : ℕ) := fun h => hju (Fin.ext h)
        have h2 : j ≠ (v : ℕ) := fun h => hjv (Fin.ext h)
        simp [hju, hjv, h1, h2]

/-! ## Twin classes, symmetricity and symmetry defect from an automorphism test

Obs. 2.3.17: "one can find the twin equivalence classes in polynomial time (test each
transposition)."  Everything in this section is stated for an arbitrary automorphism test
`test : α × RawPerm → Bool`; the structure `a : α` carries the list `dom` of the points. -/

section Twins

variable {α : Type*}

/-- Definition 2.3.10's "twin or equal" relation, by testing one transposition. -/
def rawTwinOrEq (test : α × RawPerm → Bool) (z : (α × List ℕ) × (ℕ × ℕ)) : Bool :=
  decide (z.2.1 = z.2.2) || test (z.1.1, rawTransp (z.1.2, z.2))

/-- The twin equivalence class of a point (Def. 2.3.11), as the list of its members. -/
def rawTwinClass (test : α × RawPerm → Bool) (z : (α × List ℕ) × ℕ) : List ℕ :=
  (List.range z.1.2.length).filter (fun v => rawTwinOrEq test (z.1, (z.2, v)))

/-- Obs. 2.3.17: the twin equivalence classes, the class of each point `0, …, n-1` in turn. -/
def rawTwinClasses (test : α × RawPerm → Bool) (z : α × List ℕ) : List (List ℕ) :=
  (List.range z.2.length).map (fun u => rawTwinClass test (z, u))

/-- Obs. 2.3.17: the symmetricity, the size of a largest twin class (Def. 2.3.13). -/
def rawSymmetricity (test : α × RawPerm → Bool) (z : α × List ℕ) : ℕ :=
  ((rawTwinClasses test z).map List.length).foldl max 0

/-- Obs. 2.3.17: the symmetry defect `|Ω| - s(G)` (Def. 2.3.13). -/
def rawSymDefect (test : α × RawPerm → Bool) (z : α × List ℕ) : ℕ :=
  z.2.length - rawSymmetricity test z

variable [Enc α] {test : α × RawPerm → Bool}

theorem polyFun_rawTwinOrEq (ht : PolyFun test) : PolyFun (rawTwinOrEq test) := by
  have h1 : PolyFun (fun z : (α × List ℕ) × (ℕ × ℕ) => decide (z.2.1 = z.2.2)) :=
    (polyFun_snd.comp polyFun_fst).natEq (polyFun_snd.comp polyFun_snd)
  have h2 : PolyFun (fun z : (α × List ℕ) × (ℕ × ℕ) => test (z.1.1, rawTransp (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawTransp)).comp ht
  exact (PolyFun.ite h1 (polyFun_const true) h2).of_eq (fun z => by
    simp only [rawTwinOrEq]; cases decide (z.2.1 = z.2.2) <;> rfl)

theorem polyFun_rawTwinClass (ht : PolyFun test) : PolyFun (rawTwinClass test) := by
  have hf : PolyFun (fun z : ((α × List ℕ) × ℕ) × ℕ => rawTwinOrEq test (z.1.1, (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp
      (polyFun_rawTwinOrEq ht)
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

theorem polyFun_rawTwinClasses (ht : PolyFun test) : PolyFun (rawTwinClasses test) :=
  ((polyFun_id.pair (polyFun_snd.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam (polyFun_rawTwinClass ht))).of_eq (fun _ => rfl)

theorem polyFun_rawSymmetricity (ht : PolyFun test) : PolyFun (rawSymmetricity test) :=
  (((polyFun_rawTwinClasses ht).comp (PolyFun.map polyFun_length)).comp
    polyFun_foldlMax).of_eq (fun _ => rfl)

theorem polyFun_rawSymDefect (ht : PolyFun test) : PolyFun (rawSymDefect test) :=
  ((polyFun_snd.comp polyFun_length).sub (polyFun_rawSymmetricity ht)).of_eq (fun _ => rfl)

/-! The specifications, for a test that decides membership in a group `G ≤ S([0,n))`. -/

variable {n : ℕ} {G : Subgroup (Perm (Fin n))} {a : α} {dom : List ℕ}

theorem rawTwinOrEq_spec (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) (u v : Fin n) :
    rawTwinOrEq test ((a, dom), ((u : ℕ), (v : ℕ))) = true ↔ TwinOrEq G u v := by
  rw [rawTwinOrEq, rawTransp_eq hd, TwinOrEq, IsTwin]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.val_inj, htest]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases huv : u = v
      · exact Or.inl huv
      · exact Or.inr ⟨huv, h⟩
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h

/-- The twin class of `u` lists exactly the points twin-or-equal to `u`. -/
theorem mem_rawTwinClass (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) (u : Fin n) (v : ℕ) :
    v ∈ rawTwinClass test ((a, dom), (u : ℕ)) ↔ ∃ h : v < n, TwinOrEq G u ⟨v, h⟩ := by
  simp only [rawTwinClass, List.mem_filter, List.mem_range, hd]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, (rawTwinOrEq_spec htest hd u ⟨v, hv⟩).1 h⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, (rawTwinOrEq_spec htest hd u ⟨v, hv⟩).2 h⟩

/-- **Obs. 2.3.17: the twin equivalence classes.**  Entry `u` of the output is the twin class
of `u` (Def. 2.3.11), listed as a set of points. -/
theorem mem_rawTwinClasses (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) (u : Fin n) (v : ℕ) :
    (rawTwinClasses test (a, dom)).length = n ∧
      (v ∈ (rawTwinClasses test (a, dom)).getD u [] ↔
        ∃ h : v < n, (⟨v, h⟩ : Fin n) ∈ twinClass G u) := by
  have hu : (u : ℕ) < (rawTwinClasses test (a, dom)).length := by
    simp [rawTwinClasses, hd]
  refine ⟨by simp [rawTwinClasses, hd], ?_⟩
  rw [List.getD_eq_getElem _ _ hu]
  simp only [rawTwinClasses, List.getElem_map, List.getElem_range]
  exact mem_rawTwinClass htest hd u v

open scoped Classical in
theorem length_rawTwinClass (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) (u : Fin n) :
    (rawTwinClass test ((a, dom), (u : ℕ))).length
      = (Finset.univ.filter (fun v => TwinOrEq G u v)).card := by
  rw [rawTwinClass, hd, length_filter_range]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact rawTwinOrEq_spec htest hd u v

/-- **Obs. 2.3.17: the symmetricity** `s(G)` (Def. 2.3.13). -/
theorem rawSymmetricity_eq (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) :
    rawSymmetricity test (a, dom) = symmetricity G := by
  classical
  rw [symmetricity_eq_sup_twinClass, rawSymmetricity, rawTwinClasses, List.map_map, hd]
  rw [show (List.length ∘ fun u => rawTwinClass test ((a, dom), u))
      = fun u => (rawTwinClass test ((a, dom), u)).length from rfl, foldl_max_map_range]
  congr 1
  funext u
  exact length_rawTwinClass htest hd u

/-- **Obs. 2.3.17: the symmetry defect** `|Ω| - s(G)` (Def. 2.3.13). -/
theorem rawSymDefect_eq (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) :
    rawSymDefect test (a, dom) = symDefect G := by
  rw [rawSymDefect, rawSymmetricity_eq htest hd, symDefect, hd, Fintype.card_fin]

/-- **Obs. 2.3.17: the relative symmetry defect** `defect(G) = 1 - s(G)/|Ω|`, read off the two
naturals the routines return. -/
theorem defect_eq_rawSymDefect (htest : ∀ σ : Perm (Fin n), test (a, encPerm n σ) = true ↔ σ ∈ G)
    (hd : dom.length = n) :
    defect G = 1 - (rawSymmetricity test (a, dom) : ℚ) / (dom.length : ℚ) := by
  rw [rawSymmetricity_eq htest hd, hd, defect, relSymmetricity, Fintype.card_fin]

end Twins

/-! ## Prop. 2.3.6: explicit relational structures -/

section Relational

/-- A tuple `x ∈ [0,n)^k` as the list of its entries. -/
def tupList {n k : ℕ} (x : Fin k → Fin n) : List ℕ := List.ofFn (fun j => (x j : ℕ))

theorem tupList_cast {n a a' : ℕ} (e : a' = a) (x : Fin a → Fin n) :
    tupList (x ∘ Fin.cast e) = tupList x := by
  subst e; rfl

theorem tupList_injective {n k : ℕ} : Function.Injective (tupList (n := n) (k := k)) := by
  intro x y h
  funext j
  have := congrArg (fun l : List ℕ => l.getD j 0) h
  simp only [tupList, List.getD_eq_getElem?_getD, List.getElem?_ofFn] at this
  simp only [Fin.is_lt, Option.some.injEq] at this
  apply Fin.ext
  simpa [List.ofFnNthVal, j.isLt] using this

/-- An explicit relational structure on `[0, n)` (§2.3.1): for each relation, its arity and the
list of its tuples ("each relation is given as the list of its elements", Prop. 2.3.6). -/
abbrev RawExplRels := List (ℕ × List (List ℕ))

/-- The entry of relation `i`; beyond the list, the empty relation of arity `0`. -/
def explEntry (R : RawExplRels) (i : ℕ) : ℕ × List (List ℕ) := R.getD i (0, [])

/-- **The decoding** of an explicit relational structure on `[0, n)`.  A listed tuple of the
wrong length, or with an entry `≥ n`, is not a tuple of `[0, n)` and plays no role. -/
def decExpl (n : ℕ) (R : RawExplRels) : RelStructure (Fin n) where
  numRel := R.length
  arity i := (explEntry R i).1
  rel i := {x | tupList x ∈ (explEntry R i).2}

/-- A listed tuple is a tuple of `[0, n)^a`: `z = ((n, a), t)`. -/
def goodTuple (z : (ℕ × ℕ) × List ℕ) : Bool :=
  decide (z.2.length = z.1.2) && wftAllLt (z.1.1, z.2)

theorem goodTuple_iff (n a : ℕ) (t : List ℕ) :
    goodTuple ((n, a), t) = true ↔ ∃ y : Fin a → Fin n, tupList y = t := by
  simp only [goodTuple, Bool.and_eq_true, decide_eq_true_eq, wftAllLt_eq_true_iff]
  constructor
  · rintro ⟨hl, hlt⟩
    refine ⟨fun j => ⟨t[(j : ℕ)]'(by rw [hl]; exact j.isLt),
      hlt _ (List.getElem_mem _)⟩, ?_⟩
    apply List.ext_getElem
    · simp [tupList, hl]
    · intro j h1 h2; simp [tupList]
  · rintro ⟨y, rfl⟩
    refine ⟨by simp [tupList], fun e he => ?_⟩
    simp only [tupList, List.mem_ofFn] at he
    obtain ⟨j, rfl⟩ := he
    exact (y j).isLt

theorem polyFun_goodTuple : PolyFun goodTuple := by
  have h1 : PolyFun (fun z : (ℕ × ℕ) × List ℕ => decide (z.2.length = z.1.2)) :=
    (polyFun_snd.comp polyFun_length).natEq (polyFun_fst.comp polyFun_snd)
  have h2 : PolyFun (fun z : (ℕ × ℕ) × List ℕ => wftAllLt (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp wftPolyFun_allLt
  exact (wftPolyFun_and h1 h2).of_eq (fun _ => rfl)

/-- Notation 2.3.2 on raw data: `x^σ`, entry by entry. -/
def rawMapTuple (z : RawPerm × List ℕ) : List ℕ := z.2.map (fun e => rawApply (z.1, e))

theorem polyFun_rawMapTuple : PolyFun rawMapTuple :=
  (PolyFun.mapParam polyFun_rawApply).of_eq (fun _ => rfl)

theorem rawMapTuple_tupList {n k : ℕ} (σ : Perm (Fin n)) (y : Fin k → Fin n) :
    rawMapTuple (encPerm n σ, tupList y) = tupList (tupleMap σ y) := by
  simp only [rawMapTuple, tupList, List.map_ofFn]
  congr 1
  funext j
  simp [rawApply_encPerm n σ (y j).isLt]

/-- One listed tuple `t` passes: if it is a tuple of `[0,n)^a`, then `t^σ` is in the target
list.  `w = (((σ, a), target), t)`. -/
def tupOk (w : ((RawPerm × ℕ) × List (List ℕ)) × List ℕ) : Bool :=
  !goodTuple ((w.1.1.1.length, w.1.1.2), w.2) || decide (rawMapTuple (w.1.1.1, w.2) ∈ w.1.2)

theorem polyFun_tupOk : PolyFun tupOk := by
  have hg : PolyFun (fun w : ((RawPerm × ℕ) × List (List ℕ)) × List ℕ =>
      goodTuple ((w.1.1.1.length, w.1.1.2), w.2)) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length).pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).pair polyFun_snd).comp polyFun_goodTuple
  have hm : PolyFun (fun w : ((RawPerm × ℕ) × List (List ℕ)) × List ℕ =>
      decide (rawMapTuple (w.1.1.1, w.2) ∈ w.1.2)) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
      polyFun_rawMapTuple).pair (polyFun_fst.comp polyFun_snd)).comp
      (polyFun_listMem polyFun_listNatEq) |>.of_eq (fun _ => decide_eq_decide.2 Iff.rfl)
  exact (PolyFun.ite hg hm (polyFun_const true)).of_eq (fun w => by
    simp only [tupOk]; cases goodTuple ((w.1.1.1.length, w.1.1.2), w.2) <;> rfl)

/-- Every tuple of `[0,n)^a` listed in `R` is mapped by `σ` into `R'`.
`z = ((σ, a), (R, R'))`. -/
def relDirOk (z : (RawPerm × ℕ) × (List (List ℕ) × List (List ℕ))) : Bool :=
  wftAll tupOk ((z.1, z.2.2), z.2.1)

theorem polyFun_relDirOk : PolyFun relDirOk :=
  (((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).pair (polyFun_snd.comp polyFun_fst)).comp
    (wftPolyFun_all polyFun_tupOk)).of_eq (fun _ => rfl)

theorem relDirOk_iff {n : ℕ} (σ : Perm (Fin n)) (a : ℕ) (R R' : List (List ℕ)) :
    relDirOk ((encPerm n σ, a), (R, R')) = true ↔
      ∀ y : Fin a → Fin n, tupList y ∈ R → tupList (tupleMap σ y) ∈ R' := by
  simp only [relDirOk, wftAll_eq_true_iff, tupOk, length_encPerm, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · intro h y hy
    rcases h _ hy with hg | hm
    · have : goodTuple ((n, a), tupList y) = true := (goodTuple_iff n a _).2 ⟨y, rfl⟩
      rw [this] at hg; exact absurd hg (by simp)
    · rwa [rawMapTuple_tupList] at hm
  · intro h t ht
    cases hg : goodTuple ((n, a), t) with
    | false => exact Or.inl rfl
    | true =>
      obtain ⟨y, rfl⟩ := (goodTuple_iff n a t).1 hg
      exact Or.inr (by rw [rawMapTuple_tupList]; exact h y ht)

/-- One relation of `X` against the relation of `X'` with the same index: the arities agree and
`Rᵢ^σ = Rᵢ'`.  `z = ((σ, σ⁻¹), ((a, R), (a', R')))`. -/
def pairOk (z : (RawPerm × RawPerm) × ((ℕ × List (List ℕ)) × (ℕ × List (List ℕ)))) : Bool :=
  decide (z.2.1.1 = z.2.2.1) && relDirOk ((z.1.1, z.2.1.1), (z.2.1.2, z.2.2.2)) &&
    relDirOk ((z.1.2, z.2.1.1), (z.2.2.2, z.2.1.2))

theorem polyFun_pairOk : PolyFun pairOk := by
  let Z := (RawPerm × RawPerm) × ((ℕ × List (List ℕ)) × (ℕ × List (List ℕ)))
  have ha : PolyFun (fun z : Z => z.2.1.1) := (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have ha' : PolyFun (fun z : Z => z.2.2.1) := (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hR : PolyFun (fun z : Z => z.2.1.2) := (polyFun_snd.comp polyFun_fst).comp polyFun_snd
  have hR' : PolyFun (fun z : Z => z.2.2.2) := (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hs : PolyFun (fun z : Z => z.1.1) := polyFun_fst.comp polyFun_fst
  have hs' : PolyFun (fun z : Z => z.1.2) := polyFun_fst.comp polyFun_snd
  have h1 : PolyFun (fun z : Z => decide (z.2.1.1 = z.2.2.1)) := ha.natEq ha'
  have h2 : PolyFun (fun z : Z => relDirOk ((z.1.1, z.2.1.1), (z.2.1.2, z.2.2.2))) :=
    ((hs.pair ha).pair (hR.pair hR')).comp polyFun_relDirOk
  have h3 : PolyFun (fun z : Z => relDirOk ((z.1.2, z.2.1.1), (z.2.2.2, z.2.1.2))) :=
    ((hs'.pair ha).pair (hR'.pair hR)).comp polyFun_relDirOk
  exact (wftPolyFun_and (wftPolyFun_and h1 h2) h3).of_eq (fun _ => rfl)

theorem pairOk_iff {n : ℕ} (σ : Perm (Fin n)) (a a' : ℕ) (R R' : List (List ℕ)) :
    pairOk ((encPerm n σ, encPerm n σ⁻¹), ((a, R), (a', R'))) = true ↔
      ∃ e : a = a', ∀ y : Fin a → Fin n,
        (tupList (tupleMap σ y) ∈ R' ↔ tupList y ∈ R) := by
  simp only [pairOk, Bool.and_eq_true, decide_eq_true_eq, relDirOk_iff]
  constructor
  · rintro ⟨⟨rfl, h1⟩, h2⟩
    refine ⟨rfl, fun y => ⟨fun hy => ?_, h1 y⟩⟩
    have := h2 _ hy
    have hyy : tupleMap (σ⁻¹ : Perm (Fin n)) (tupleMap σ y) = y := by
      funext j; simp [tupleMap]
    rwa [hyy] at this
  · rintro ⟨rfl, h⟩
    refine ⟨⟨rfl, fun y hy => (h y).2 hy⟩, fun y hy => ?_⟩
    have hyy : tupleMap σ (tupleMap (σ⁻¹ : Perm (Fin n)) y) = y := by
      funext j; simp [tupleMap]
    exact (h _).1 (by rwa [hyy])

/-- **Prop. 2.3.6: the test.**  `p = ((R, R'), σ)`: the two explicit structures and the
candidate bijection. -/
def rawExplIsoTest (p : (RawExplRels × RawExplRels) × RawPerm) : Bool :=
  decide (p.1.1.length = p.1.2.length) && wftAll pairOk ((p.2, rawInv p.2), p.1.1.zip p.1.2)

theorem polyFun_rawExplIsoTest : PolyFun rawExplIsoTest := by
  have h1 : PolyFun (fun p : (RawExplRels × RawExplRels) × RawPerm =>
      decide (p.1.1.length = p.1.2.length)) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_length).natEq
      ((polyFun_fst.comp polyFun_snd).comp polyFun_length)
  have h2 : PolyFun (fun p : (RawExplRels × RawExplRels) × RawPerm =>
      wftAll pairOk ((p.2, rawInv p.2), p.1.1.zip p.1.2)) :=
    (((polyFun_snd.pair (polyFun_snd.comp polyFun_rawInv)).pair
      (polyFun_fst.comp polyFun_zip)).comp (wftPolyFun_all polyFun_pairOk))
  exact (wftPolyFun_and h1 h2).of_eq (fun _ => rfl)

/-- Equality of relational structures, relation by relation. -/
theorem relStructure_eq_iff {Ω : Type*} (A B : RelStructure Ω) :
    A = B ↔ ∃ h : A.numRel = B.numRel, ∃ ha : ∀ i, A.arity i = B.arity (Fin.cast h i),
      ∀ i (x : Fin (A.arity i) → Ω), x ∈ A.rel i ↔ (x ∘ Fin.cast (ha i).symm) ∈ B.rel (Fin.cast h i) := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun i => rfl, fun i x => Iff.rfl⟩
  · obtain ⟨nA, aA, RA⟩ := A
    obtain ⟨nB, aB, RB⟩ := B
    rintro ⟨h, ha, hr⟩
    simp only at h
    subst h
    have haa : aA = aB := funext fun i => by simpa using ha i
    subst haa
    simp only [RelStructure.mk.injEq, heq_eq_eq, true_and]
    funext i
    ext x
    simpa using hr i x

theorem forall_mem_zip_iff {β γ : Type*} {l : List β} {l' : List γ} (hl : l.length = l'.length)
    (P : β × γ → Prop) :
    (∀ q ∈ l.zip l', P q) ↔ ∀ i (h : i < l.length), P (l[i], l'[i]'(hl ▸ h)) := by
  constructor
  · intro H i h
    apply H
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩
  · intro H q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    have hi' : i < l.length := by simpa [hl] using hi
    simpa using H i hi'

/-- **Prop. 2.3.6 (Testing candidate isomorphism).**  "Given two explicit relational structures
`X = (Ω, R)` and `X' = (Ω', R')` and a bijection `σ : Ω → Ω'`, one can decide … whether
`σ ∈ Iso(X, X')`."  The routine `rawExplIsoTest` answers exactly this question
(`polyFun_rawExplIsoTest`: in polynomial time).  Both structures live on `[0, n)`; the second
part of the proposition, `σ ∈ Aut(X)`, is the case `R' = R` (`rawExplAutTest_spec`). -/
theorem rawExplIsoTest_spec {n : ℕ} (R R' : RawExplRels) (σ : Perm (Fin n)) :
    rawExplIsoTest ((R, R'), encPerm n σ) = true ↔
      (σ : Fin n ≃ Fin n) ∈ RelStructure.Iso (decExpl n R) (decExpl n R') := by
  simp only [rawExplIsoTest, Bool.and_eq_true, decide_eq_true_eq, wftAll_eq_true_iff,
    rawInv_encPerm]
  rw [RelStructure.Iso, Set.mem_setOf_eq, relStructure_eq_iff]
  constructor
  · rintro ⟨hl, h⟩
    rw [forall_mem_zip_iff hl] at h
    have hp : ∀ i (hi : i < R.length), ∃ e : (explEntry R i).1 = (explEntry R' i).1,
        ∀ y : Fin (explEntry R i).1 → Fin n,
          (tupList (tupleMap σ y) ∈ (explEntry R' i).2 ↔ tupList y ∈ (explEntry R i).2) := by
      intro i hi
      have := h i hi
      rw [show R[i] = ((R[i]).1, (R[i]).2) from rfl,
        show R'[i]'(hl ▸ hi) = ((R'[i]'(hl ▸ hi)).1, (R'[i]'(hl ▸ hi)).2) from rfl,
        pairOk_iff] at this
      have e1 : explEntry R i = R[i] := by rw [explEntry, List.getD_eq_getElem _ _ hi]
      have e2 : explEntry R' i = R'[i]'(hl ▸ hi) := by
        rw [explEntry, List.getD_eq_getElem _ _ (hl ▸ hi)]
      rw [e1, e2]; exact this
    refine ⟨hl, fun i => by obtain ⟨e, -⟩ := hp i i.isLt; exact e, fun i x => ?_⟩
    obtain ⟨e, he⟩ := hp i i.isLt
    change x ∈ tupleMap σ '' {x | tupList x ∈ (explEntry R i).2} ↔
      tupList (x ∘ Fin.cast _) ∈ (explEntry R' i).2
    rw [tupList_cast]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (he y).2 hy
    · intro hx
      refine ⟨tupleMap (σ⁻¹ : Perm (Fin n)) x, (he _).1 ?_, ?_⟩
      · convert hx using 2
        funext j; simp [tupleMap]
      · funext j; simp [tupleMap]
  · rintro ⟨hl0, ha, hr⟩
    have hl : R.length = R'.length := hl0
    refine ⟨hl, ?_⟩
    rw [forall_mem_zip_iff hl]
    intro i hi
    have e1 : explEntry R i = R[i] := by rw [explEntry, List.getD_eq_getElem _ _ hi]
    have e2 : explEntry R' i = R'[i]'(hl ▸ hi) := by
      rw [explEntry, List.getD_eq_getElem _ _ (hl ▸ hi)]
    rw [show R[i] = ((R[i]).1, (R[i]).2) from rfl,
      show R'[i]'(hl ▸ hi) = ((R'[i]'(hl ▸ hi)).1, (R'[i]'(hl ▸ hi)).2) from rfl,
      pairOk_iff, ← e1, ← e2]
    have hai := ha ⟨i, hi⟩
    refine ⟨hai, fun y => ?_⟩
    have := hr ⟨i, hi⟩ (tupleMap σ y)
    change tupleMap σ y ∈ tupleMap σ '' {x | tupList x ∈ (explEntry R i).2} ↔
      tupList (tupleMap σ y ∘ Fin.cast _) ∈ (explEntry R' i).2 at this
    rw [tupList_cast] at this
    rw [← this]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := by
        funext j; exact σ.injective (congrFun hzy j)
      exact this ▸ hz
    · intro hy; exact ⟨y, hy, rfl⟩

/-- **Prop. 2.3.6, second part.**  "Given an explicit relational structure `X = (Ω, R)` and a
permutation `σ ∈ S(Ω)`, one can decide … whether `σ ∈ Aut(X)`."  `p = (R, σ)`. -/
def rawExplAutTest (p : RawExplRels × RawPerm) : Bool := rawExplIsoTest ((p.1, p.1), p.2)

theorem polyFun_rawExplAutTest : PolyFun rawExplAutTest :=
  (((polyFun_fst.pair polyFun_fst).pair polyFun_snd).comp polyFun_rawExplIsoTest).of_eq
    (fun _ => rfl)

theorem rawExplAutTest_spec {n : ℕ} (R : RawExplRels) (σ : Perm (Fin n)) :
    rawExplAutTest (R, encPerm n σ) = true ↔ σ ∈ RelStructure.Aut (decExpl n R) :=
  rawExplIsoTest_spec R R σ

/-- **Prop. 2.3.6, the linear-time claim** (§2.3.1): "Given two explicit relational structures
`X = (Ω, R)` and `X' = (Ω', R')` and a bijection `σ : Ω → Ω'`, one can decide in linear time
whether `σ ∈ Iso(X, X')`."  On the RAM: one program decides, within `C·(size + 1)` steps, the
test `rawExplIsoTest` (which is `σ ∈ Iso(X, X')` by `rawExplIsoTest_spec`) on every input
whose last component is a bijection.

**Proved** as `Algo.ExplLinear.proposition_2_3_6_linear` (`Workspace/Algo/ExplLinear.lean`,
with `C = 500`), by a step-exact RAM routine: tries in fresh memory in place of the paper's
per-relation radix sort (see the corrected paper entry for Prop. 2.3.6).  The
polynomial-time test is `polyFun_rawExplIsoTest`. -/
def Proposition_2_3_6_linear_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ (n : ℕ) (R R' : RawExplRels) (σ : Perm (Fin n)),
    ∃ k ≤ C * (Enc.size ((R, R'), encPerm n σ) + 1),
      Halted P (run P (Config.init (encode ((R, R'), encPerm n σ))) k) ∧
        OutputAt (run P (Config.init (encode ((R, R'), encPerm n σ))) k).mem
          (encode (rawExplIsoTest ((R, R'), encPerm n σ)))

end Relational

/-! ## Obs. 2.3.17 for explicit relational structures -/

section RelTwins

/-- Obs. 2.3.17: the twin equivalence classes of an explicit relational structure.
`z = (R, dom)`, the domain being `[0, dom.length)`. -/
def explTwinClasses (z : RawExplRels × List ℕ) : List (List ℕ) := rawTwinClasses rawExplAutTest z

/-- Obs. 2.3.17: the symmetricity of an explicit relational structure. -/
def explSymmetricity (z : RawExplRels × List ℕ) : ℕ := rawSymmetricity rawExplAutTest z

/-- Obs. 2.3.17: the symmetry defect of an explicit relational structure. -/
def explSymDefect (z : RawExplRels × List ℕ) : ℕ := rawSymDefect rawExplAutTest z

theorem polyFun_explTwinClasses : PolyFun explTwinClasses :=
  polyFun_rawTwinClasses polyFun_rawExplAutTest

theorem polyFun_explSymmetricity : PolyFun explSymmetricity :=
  polyFun_rawSymmetricity polyFun_rawExplAutTest

theorem polyFun_explSymDefect : PolyFun explSymDefect :=
  polyFun_rawSymDefect polyFun_rawExplAutTest

variable {n : ℕ} {R : RawExplRels} {dom : List ℕ}

/-- **Obs. 2.3.17**, "one can find the twin equivalence classes in polynomial time": entry `u`
of `explTwinClasses` is the twin class of `u` in `Aut(X)` (Defs. 2.3.9, 2.3.11). -/
theorem explTwinClasses_spec (hd : dom.length = n) (u : Fin n) (v : ℕ) :
    (explTwinClasses (R, dom)).length = n ∧
      (v ∈ (explTwinClasses (R, dom)).getD u [] ↔
        ∃ h : v < n, (⟨v, h⟩ : Fin n) ∈ twinClass (RelStructure.Aut (decExpl n R)) u) :=
  mem_rawTwinClasses (fun σ => rawExplAutTest_spec R σ) hd u v

/-- **Obs. 2.3.17**, "the symmetricity … of explicit relational structures can also be computed
in polynomial time" (Def. 2.3.16: the parameters of `X` are those of `Aut(X)`). -/
theorem explSymmetricity_spec (hd : dom.length = n) :
    explSymmetricity (R, dom) = structSymmetricity (decExpl n R) :=
  rawSymmetricity_eq (fun σ => rawExplAutTest_spec R σ) hd

/-- **Obs. 2.3.17**, "… and the symmetry defect of explicit relational structures can also be
computed in polynomial time". -/
theorem explSymDefect_spec (hd : dom.length = n) :
    explSymDefect (R, dom) = structSymDefect (decExpl n R) :=
  rawSymDefect_eq (fun σ => rawExplAutTest_spec R σ) hd

/-- **Obs. 2.3.17**, the relative symmetry defect, from the two naturals computed. -/
theorem explDefect_spec (hd : dom.length = n) :
    structDefect (decExpl n R) = 1 - (explSymmetricity (R, dom) : ℚ) / (dom.length : ℚ) :=
  defect_eq_rawSymDefect (fun σ => rawExplAutTest_spec R σ) hd

end RelTwins

/-! ## Obs. 2.5.8: explicit hypergraphs -/

section Hyper

/-- An explicit hypergraph on `[0, n)`: the list of its hyperedges, each a list of points.
Repeated hyperedges are allowed (multiplicities, §2.5.1). -/
abbrev RawHyp := List (List ℕ)

/-- The set of points of `[0, n)` that a listed hyperedge contains. -/
def decEdge (n : ℕ) (e : List ℕ) : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => (v : ℕ) ∈ e)

/-- **The decoding** of an explicit hypergraph on `[0, n)`. -/
def decHyp (n : ℕ) (E : RawHyp) : Hypergraph (Fin n) where
  numEdges := E.length
  edge i := decEdge n (E.get i)

/-- Two listed hyperedges are the same subset of the domain `rng = [0, n)`.
`z = ((e, e'), rng)`. -/
def rawSameSet (z : (List ℕ × List ℕ) × List ℕ) : Bool :=
  z.2.all (fun v => decide (v ∈ z.1.1) == decide (v ∈ z.1.2))

theorem polyFun_rawSameSet : PolyFun rawSameSet := by
  have hq : PolyFun (fun w : (List ℕ × List ℕ) × ℕ =>
      decide (w.2 ∈ w.1.1) == decide (w.2 ∈ w.1.2)) := by
    have h1 : PolyFun (fun w : (List ℕ × List ℕ) × ℕ => decide (w.2 ∈ w.1.1)) :=
      (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_natListMem
    have h2 : PolyFun (fun w : (List ℕ × List ℕ) × ℕ => decide (w.2 ∈ w.1.2)) :=
      (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natListMem
    exact (PolyFun.ite h1 h2 (wftPolyFun_not h2)).of_eq (fun w => by
      cases decide (w.2 ∈ w.1.1) <;> cases decide (w.2 ∈ w.1.2) <;> rfl)
  exact (wftPolyFun_all hq).of_eq (fun z => by simp [wftAll, rawSameSet])

theorem rawSameSet_iff (n : ℕ) (e e' : List ℕ) :
    rawSameSet ((e, e'), List.range n) = true ↔ decEdge n e = decEdge n e' := by
  simp only [rawSameSet, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_decide]
  constructor
  · intro h
    ext v
    simp only [decEdge, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h v v.isLt
  · intro h v hv
    have := congrArg (fun A => (⟨v, hv⟩ : Fin n) ∈ A) h
    simpa [decEdge] using this

/-- The multiplicity of a listed hyperedge `e` in the list `E`.  `z = ((E, e), rng)`. -/
def rawMult (z : (RawHyp × List ℕ) × List ℕ) : ℕ :=
  (z.1.1.filter (fun e' => rawSameSet ((z.1.2, e'), z.2))).length

theorem polyFun_rawMult : PolyFun rawMult := by
  have hq : PolyFun (fun w : (List ℕ × List ℕ) × List ℕ => rawSameSet ((w.1.2, w.2), w.1.1)) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_rawSameSet
  exact ((((polyFun_snd.pair (polyFun_fst.comp polyFun_snd))).pair
    (polyFun_fst.comp polyFun_fst)).comp (PolyFun.filterParam hq) |>.comp polyFun_length).of_eq
    (fun _ => rfl)

theorem length_filter_eq_card {β : Type*} (E : List β) (p : β → Bool) :
    (E.filter p).length = (Finset.univ.filter (fun i : Fin E.length => p (E.get i) = true)).card := by
  conv_lhs => rw [← List.ofFn_get E, List.ofFn_eq_map, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  congr 1
  ext i
  simp

theorem rawMult_eq (n : ℕ) (E : RawHyp) (e : List ℕ) :
    rawMult ((E, e), List.range n) = (decHyp n E).mult (decEdge n e) := by
  rw [rawMult, length_filter_eq_card, Hypergraph.mult]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rawSameSet_iff, decHyp]
  exact eq_comm

theorem decEdge_rawMapTuple {n : ℕ} (σ : Perm (Fin n)) (e : List ℕ) :
    decEdge n (rawMapTuple (encPerm n σ, e)) = (decEdge n e).image σ := by
  ext v
  simp only [decEdge, rawMapTuple, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map,
    Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxv⟩
    by_cases hxn : x < n
    · refine ⟨⟨x, hxn⟩, hx, Fin.ext ?_⟩
      rw [← hxv, rawApply_encPerm n σ hxn]
    · rw [rawApply_of_length_le (by simp; omega)] at hxv
      exact absurd (hxv ▸ v.isLt) hxn
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rawApply_encPerm n σ w.isLt⟩

/-- Every listed hyperedge `e` of `E` has the same multiplicity in `E` as `e^σ` in `E'`.
`z = ((σ, rng), (E, E'))`. -/
def hypDirOk (z : (RawPerm × List ℕ) × (RawHyp × RawHyp)) : Bool :=
  z.2.1.all (fun e => decide (rawMult ((z.2.1, e), z.1.2) =
    rawMult ((z.2.2, rawMapTuple (z.1.1, e)), z.1.2)))

theorem polyFun_hypDirOk : PolyFun hypDirOk := by
  let Z := (RawPerm × List ℕ) × (RawHyp × RawHyp)
  have hq : PolyFun (fun w : Z × List ℕ => decide (rawMult ((w.1.2.1, w.2), w.1.1.2) =
      rawMult ((w.1.2.2, rawMapTuple (w.1.1.1, w.2)), w.1.1.2))) := by
    have h1 : PolyFun (fun w : Z × List ℕ => rawMult ((w.1.2.1, w.2), w.1.1.2)) :=
      ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd).pair
        ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp polyFun_rawMult
    have h2 : PolyFun (fun w : Z × List ℕ =>
        rawMult ((w.1.2.2, rawMapTuple (w.1.1.1, w.2)), w.1.1.2)) :=
      ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
        ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
          polyFun_rawMapTuple)).pair
        ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp polyFun_rawMult
    exact h1.natEq h2
  exact ((polyFun_id.pair ((polyFun_snd.comp polyFun_fst))).comp (wftPolyFun_all hq)).of_eq
    (fun _ => rfl)

theorem hypDirOk_iff {n : ℕ} (σ : Perm (Fin n)) (E E' : RawHyp) :
    hypDirOk ((encPerm n σ, List.range n), (E, E')) = true ↔
      ∀ e ∈ E, (decHyp n E).mult (decEdge n e) = (decHyp n E').mult ((decEdge n e).image σ) := by
  simp only [hypDirOk, List.all_eq_true, decide_eq_true_eq, rawMult_eq, decEdge_rawMapTuple]

/-- **Obs. 2.5.8: the test.**  `p = ((E, E'), σ)`: the two explicit hypergraphs and the
candidate bijection. -/
def rawHypIsoTest (p : (RawHyp × RawHyp) × RawPerm) : Bool :=
  hypDirOk ((p.2, List.range p.2.length), (p.1.1, p.1.2)) &&
    hypDirOk ((rawInv p.2, List.range p.2.length), (p.1.2, p.1.1))

theorem polyFun_rawHypIsoTest : PolyFun rawHypIsoTest := by
  have hr : PolyFun (fun p : (RawHyp × RawHyp) × RawPerm => List.range p.2.length) :=
    polyFun_snd.comp polyFun_rangeLength
  have h1 := ((polyFun_snd.pair hr).pair ((polyFun_fst.comp polyFun_fst).pair
    (polyFun_fst.comp polyFun_snd))).comp polyFun_hypDirOk
  have h2 := (((polyFun_snd.comp polyFun_rawInv).pair hr).pair
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst))).comp polyFun_hypDirOk
  exact (wftPolyFun_and h1 h2).of_eq (fun _ => rfl)

theorem mult_eq_zero_of_forall_ne {n : ℕ} (E : RawHyp) (A : Finset (Fin n))
    (h : ∀ e ∈ E, decEdge n e ≠ A) : (decHyp n E).mult A = 0 := by
  rw [Hypergraph.mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact h _ (List.get_mem E i)

/-- **Obs. 2.5.8** (Def. 2.5.3).  "Candidate isomorphisms … of explicit hypergraphs can be
tested in polynomial time (cf. Prop. 2.3.6)."  The routine `rawHypIsoTest` answers exactly
whether `σ` is an isomorphism (`polyFun_rawHypIsoTest`: in polynomial time). -/
theorem rawHypIsoTest_spec {n : ℕ} (E E' : RawHyp) (σ : Perm (Fin n)) :
    rawHypIsoTest ((E, E'), encPerm n σ) = true ↔
      Hypergraph.IsIsoOf (σ : Fin n ≃ Fin n) (decHyp n E) (decHyp n E') := by
  simp only [rawHypIsoTest, length_encPerm, rawInv_encPerm, Bool.and_eq_true, hypDirOk_iff]
  have hinv : ∀ A : Finset (Fin n), (A.image σ).image (σ⁻¹ : Perm (Fin n)) = A := by
    intro A; rw [Finset.image_image]; simp
  have hinv' : ∀ A : Finset (Fin n), (A.image (σ⁻¹ : Perm (Fin n))).image σ = A := by
    intro A; rw [Finset.image_image]; simp
  constructor
  · rintro ⟨h1, h2⟩ A
    by_cases hA : ∃ e ∈ E, decEdge n e = A
    · obtain ⟨e, he, rfl⟩ := hA
      exact h1 e he
    by_cases hB : ∃ e' ∈ E', decEdge n e' = A.image σ
    · obtain ⟨e', he', hAe⟩ := hB
      have := h2 e' he'
      rw [hAe, hinv] at this
      exact this.symm
    push Not at hA hB
    rw [mult_eq_zero_of_forall_ne E A hA, mult_eq_zero_of_forall_ne E' _ hB]
  · intro h
    refine ⟨fun e _ => h _, fun e' _ => ?_⟩
    have := h ((decEdge n e').image (σ⁻¹ : Perm (Fin n)))
    rw [hinv'] at this
    exact this.symm

/-- Obs. 2.5.8: the automorphism test.  `p = (E, σ)`. -/
def rawHypAutTest (p : RawHyp × RawPerm) : Bool := rawHypIsoTest ((p.1, p.1), p.2)

theorem polyFun_rawHypAutTest : PolyFun rawHypAutTest :=
  (((polyFun_fst.pair polyFun_fst).pair polyFun_snd).comp polyFun_rawHypIsoTest).of_eq
    (fun _ => rfl)

/-- **Obs. 2.5.8**, "(and therefore automorphisms)". -/
theorem rawHypAutTest_spec {n : ℕ} (E : RawHyp) (σ : Perm (Fin n)) :
    rawHypAutTest (E, encPerm n σ) = true ↔ σ ∈ (decHyp n E).Aut := by
  rw [rawHypAutTest, rawHypIsoTest_spec, Hypergraph.IsIsoOf]
  change _ ↔ ∀ A : Finset (Fin n), (decHyp n E).mult (A.image σ) = (decHyp n E).mult A
  exact ⟨fun h A => (h A).symm, fun h A => (h A).symm⟩

/-- Obs. 2.5.8: the twin equivalence classes of an explicit hypergraph.  `z = (E, dom)`. -/
def hypTwinClasses (z : RawHyp × List ℕ) : List (List ℕ) := rawTwinClasses rawHypAutTest z

/-- Obs. 2.5.8: the symmetricity of an explicit hypergraph. -/
def hypSymmetricity (z : RawHyp × List ℕ) : ℕ := rawSymmetricity rawHypAutTest z

/-- Obs. 2.5.8: the symmetry defect of an explicit hypergraph. -/
def hypSymDefect (z : RawHyp × List ℕ) : ℕ := rawSymDefect rawHypAutTest z

theorem polyFun_hypTwinClasses : PolyFun hypTwinClasses :=
  polyFun_rawTwinClasses polyFun_rawHypAutTest

theorem polyFun_hypSymmetricity : PolyFun hypSymmetricity :=
  polyFun_rawSymmetricity polyFun_rawHypAutTest

theorem polyFun_hypSymDefect : PolyFun hypSymDefect :=
  polyFun_rawSymDefect polyFun_rawHypAutTest

variable {n : ℕ} {E : RawHyp} {dom : List ℕ}

/-- **Obs. 2.5.8**, "one can find the twin equivalence classes of an explicit hypergraph in
polynomial time" (Def. 2.5.6). -/
theorem hypTwinClasses_spec (hd : dom.length = n) (u : Fin n) (v : ℕ) :
    (hypTwinClasses (E, dom)).length = n ∧
      (v ∈ (hypTwinClasses (E, dom)).getD u [] ↔
        ∃ h : v < n, (⟨v, h⟩ : Fin n) ∈ twinClass (decHyp n E).Aut u) :=
  mem_rawTwinClasses (fun σ => rawHypAutTest_spec E σ) hd u v

/-- **Obs. 2.5.8**, the symmetricity of an explicit hypergraph (Def. 2.5.6). -/
theorem hypSymmetricity_spec (hd : dom.length = n) :
    hypSymmetricity (E, dom) = (decHyp n E).symmetricity :=
  rawSymmetricity_eq (fun σ => rawHypAutTest_spec E σ) hd

/-- **Obs. 2.5.8**, "Consequently, the symmetry defect of a hypergraph can also be computed in
polynomial time" (Def. 2.5.6): the absolute defect `|V| - s(H)` … -/
theorem hypSymDefect_spec (hd : dom.length = n) :
    hypSymDefect (E, dom) = symDefect (decHyp n E).Aut :=
  rawSymDefect_eq (fun σ => rawHypAutTest_spec E σ) hd

/-- … and the relative defect `defect(H) = 1 - s(H)/|V|`. -/
theorem hypDefect_spec (hd : dom.length = n) :
    (decHyp n E).defect = 1 - (hypSymmetricity (E, dom) : ℚ) / (dom.length : ℚ) :=
  defect_eq_rawSymDefect (fun σ => rawHypAutTest_spec E σ) hd

end Hyper

end Algo
