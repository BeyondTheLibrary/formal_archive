/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the indexed right coset representative of a subgroup.
-/
import Workspace.Algo.Labelled

/-!
# Right coset representatives, one at a time

Proposition 11.1.6 and Theorem 11.1.9 of §11.1 both let "`σ` range over right coset
representatives" of a subgroup `H ≤ G` that is not a group of the point stabilizer chain (it is
the block kernel `N`), so `Algo.rawRow` does not give them.  The number of representatives is
`|G : H|`, which is the multiplicative cost of the round and is quasipolynomial, so the whole
transversal is too big to be the answer of a routine.  `Algo.Round` never asks for the list: it
asks for the `j`-th child.  So what is computed here is the **`j`-th representative**.

The search is a breadth-first search on the right cosets: the current list of representatives
starts at the identity, one round multiplies every representative by every generator of `G` on
the right, and a candidate `r` is kept when no representative `r'` found so far satisfies
`r (r')⁻¹ ∈ H`, which is the test "`H r = H r'`" and is decided by `Algo.rawMem`.

Two points of the shape.

**The index arrives in unary.**  `Enc ℕ` measures a natural by its bit length, so a routine
that loops `j` times on a machine natural is not polynomial in its input (the rule already
recorded for `List.range`).  The index is therefore a *list* `js`, and `j` is `js.length`; then
`j` counts towards the input size and the running time is polynomial in the input, which is
what `RAM.PolyFun` says and what the evaluator of `Algo/Evaluator.lean` needs, since it charges
the cost of a node of the recursion tree against the size of the instance stored at it.

**The list of representatives is truncated.**  A round only adds while the list has at most
`js.length` entries, so the list never exceeds `js.length + 1` entries.  This is what keeps the
state polynomial; it costs nothing, because a round that does not find every coset still finds
at least one new one, so `js.length` rounds already produce `min(|G : H|, js.length + 1)`
representatives.

## Main definitions and results

* `Algo.cosetAdd`, `Algo.cosetRound`, `Algo.rawCosetReps`, `Algo.rawCosetRep`;
* `Algo.RepsOK` and `Algo.rawCosetReps_sound` — every representative lies in `G` and no two of
  them lie in the same right coset of `H`;
* `Algo.length_rawCosetReps_le` — at most `j + 1` representatives;
* `Algo.polyFun_rawCosetReps`, `Algo.polyFun_rawCosetRep`.

The covering half is `Algo.length_rawCosetReps_eq` and `Algo.rawCosetReps_cover`: with
`j + 1` at most the index the list has exactly `j + 1` entries, and once `j + 1` reaches the
index every element of `G` lies in one of the listed right cosets.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## The routine -/

/-- The parameter of the search: the domain witness with the generators of `G`, then the
generators of `H` and the index in unary. -/
abbrev CosetParam := (List ℕ × RawGens) × (RawGens × List ℕ)

/-- **The candidates of one round**: every representative times every generator of `G`, on the
right, because the right cosets `Hr` are permuted by right multiplication. -/
def cosetCands (p : RawGens × RawGens) : RawGens :=
  (p.1.map (fun r => rawGensMul (r, p.2))).flatten

theorem mem_cosetCands {reps gens : RawGens} {x : RawPerm} (h : x ∈ cosetCands (reps, gens)) :
    ∃ r ∈ reps, ∃ g ∈ gens, x = rawMul (r, g) := by
  rw [cosetCands, List.mem_flatten] at h
  obtain ⟨row, hrow, hx⟩ := h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrow
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
  exact ⟨r, hr, g, hg, rfl⟩

/-- **A candidate is new** when the list is still short and no representative found so far
lies in the same right coset. -/
def cosetNew (p : CosetParam × (RawGens × RawPerm)) : Bool :=
  decide (p.2.1.length ≤ p.1.2.2.length) &&
    (p.2.1.filter
      (fun r => rawMem ((p.1.1.1, p.1.2.1), rawMul (p.2.2, rawInv r)))).isEmpty

/-- **One candidate offered to the list of representatives.** -/
def cosetAdd (p : CosetParam × (RawGens × RawPerm)) : RawGens :=
  if cosetNew p then p.2.1 ++ [p.2.2] else p.2.1

/-- **One round of the search.** -/
def cosetRound (p : CosetParam × RawGens) : RawGens :=
  List.foldl (fun acc cand => cosetAdd (p.1, (acc, cand))) p.2
    (cosetCands (p.2, p.1.1.2))

/-- **The representatives found after `js.length` rounds.** -/
def rawCosetReps (c : CosetParam) : RawGens :=
  List.foldl (fun reps _ => cosetRound (c, reps)) [rawOne c.1.1] c.2.2

/-- `Algo.rawCosetReps` read as an outer fold over the unary index. -/
theorem rawCosetReps_eq (dom : List ℕ) (gensG gensH : RawGens) (js : List ℕ) :
    rawCosetReps ((dom, gensG), (gensH, js))
      = List.foldl (fun reps (_ : ℕ) =>
          cosetRound (((dom, gensG), (gensH, js)), reps)) [rawOne dom] js := rfl

/-- **The `j`-th right coset representative**, for `j = js.length`. -/
def rawCosetRep (c : CosetParam) : RawPerm :=
  (rawCosetReps c).getD c.2.2.length (rawOne c.1.1)

/-! ## Soundness

`Algo.RepsOK` is the invariant of the search: every entry is a well-formed permutation lying
in `G`, and no two entries lie in the same right coset of `H`. -/

/-- **The invariant of the search.** -/
def RepsOK (n : ℕ) (G H : Subgroup (Perm (Fin n))) (l : RawGens) : Prop :=
  (∀ r ∈ l, RawPerm.WF n r ∧ decPerm n r ∈ G) ∧
    l.Pairwise (fun a b => decPerm n b * (decPerm n a)⁻¹ ∉ H)

section Sound

variable {dom : List ℕ} {gensG gensH : List (Perm (Fin n))} {js : List ℕ}

/-- The coset test is what `Algo.rawMem` decides. -/
theorem cosetNew_sound (hdom : dom.length = n) {reps : RawGens} {cand : RawPerm}
    (hreps : ∀ r ∈ reps, RawPerm.WF n r) (hcand : RawPerm.WF n cand)
    (h : cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
      (reps, cand)) = true) :
    ∀ r ∈ reps, decPerm n cand * (decPerm n r)⁻¹ ∉ genGroup gensH := by
  intro r hr hmem
  rw [cosetNew, Bool.and_eq_true, List.isEmpty_iff, List.filter_eq_nil_iff] at h
  have hwfr := hreps r hr
  have htest : rawMem ((dom, gensH.map (encPerm n)),
      rawMul (cand, rawInv r)) = true := by
    have hrw : rawMul (cand, rawInv r) = encPerm n (decPerm n cand * (decPerm n r)⁻¹) := by
      rw [← encPerm_decPerm hcand, ← encPerm_decPerm hwfr, rawInv_encPerm, rawMul_encPerm,
        encPerm_decPerm hcand, encPerm_decPerm hwfr]
    rw [hrw]
    exact (rawMem_spec dom hdom gensH _).2 hmem
  exact absurd htest (by simpa using h.2 r hr)

/-- **One candidate keeps the invariant.** -/
theorem cosetAdd_sound (hdom : dom.length = n) {reps : RawGens} {cand : RawPerm}
    (hok : RepsOK n (genGroup gensG) (genGroup gensH) reps)
    (hcand : RawPerm.WF n cand) (hcandG : decPerm n cand ∈ genGroup gensG) :
    RepsOK n (genGroup gensG) (genGroup gensH)
      (cosetAdd (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), (reps, cand))) := by
  rw [cosetAdd]
  by_cases h : cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
      (reps, cand))
  · rw [if_pos h]
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases List.mem_append.1 hr with h1 | h1
      · exact hok.1 r h1
      · rw [List.mem_singleton.1 h1]; exact ⟨hcand, hcandG⟩
    · refine List.pairwise_append.2 ⟨hok.2, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.1 hb]
      exact cosetNew_sound hdom (fun r hr => (hok.1 r hr).1) hcand h a ha
  · rw [if_neg h]; exact hok

/-- **One round keeps the invariant.** -/
theorem cosetFold_sound (hdom : dom.length = n) :
    ∀ (l : RawGens) (reps : RawGens),
      (∀ x ∈ l, RawPerm.WF n x ∧ decPerm n x ∈ genGroup gensG) →
      RepsOK n (genGroup gensG) (genGroup gensH) reps →
      RepsOK n (genGroup gensG) (genGroup gensH)
        (List.foldl (fun acc cand =>
          cosetAdd (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), (acc, cand)))
          reps l) := by
  intro l
  induction l with
  | nil => intro reps _ hok; exact hok
  | cons a s ih =>
      intro reps hl hok
      rw [List.foldl_cons]
      exact ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (cosetAdd_sound hdom hok (hl a List.mem_cons_self).1 (hl a List.mem_cons_self).2)

/-- The candidates of a round lie in `G` and are well formed. -/
theorem cosetCands_sound {reps : RawGens}
    (hreps : ∀ r ∈ reps, RawPerm.WF n r ∧ decPerm n r ∈ genGroup gensG) :
    ∀ x ∈ cosetCands (reps, gensG.map (encPerm n)),
      RawPerm.WF n x ∧ decPerm n x ∈ genGroup gensG := by
  intro x hx
  obtain ⟨r, hr, g, hg, rfl⟩ := mem_cosetCands hx
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hwfr, hrG⟩ := hreps r hr
  have hrw : rawMul (r, encPerm n σ) = encPerm n (decPerm n r * σ) := by
    rw [← encPerm_decPerm hwfr, rawMul_encPerm, encPerm_decPerm hwfr]
  rw [hrw, decPerm_encPerm]
  exact ⟨wf_encPerm _ _, Subgroup.mul_mem _ hrG (Subgroup.subset_closure hσ)⟩

theorem cosetRound_sound (hdom : dom.length = n) {reps : RawGens}
    (hok : RepsOK n (genGroup gensG) (genGroup gensH) reps) :
    RepsOK n (genGroup gensG) (genGroup gensH)
      (cosetRound (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps)) :=
  cosetFold_sound hdom _ reps (cosetCands_sound hok.1) hok

/-- **The search is sound.**  Every representative lies in `G`, and no two of them lie in the
same right coset of `H`.  Paper: the right coset representatives of Prop. 11.1.6 and
Thm. 11.1.9 (§11.1). -/
theorem rawCosetReps_sound (hdom : dom.length = n) :
    RepsOK n (genGroup gensG) (genGroup gensH)
      (rawCosetReps ((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js))) := by
  have hstart : RepsOK n (genGroup gensG) (genGroup gensH) [rawOne dom] := by
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro r hr
    rw [List.mem_singleton.1 hr, rawOne_eq dom, hdom]
    exact ⟨wf_encPerm n 1, by rw [decPerm_encPerm]; exact Subgroup.one_mem _⟩
  have key : ∀ (l : List ℕ) (start : RawGens),
      RepsOK n (genGroup gensG) (genGroup gensH) start →
      RepsOK n (genGroup gensG) (genGroup gensH)
        (List.foldl (fun reps _ =>
          cosetRound (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps))
          start l) := by
    intro l
    induction l with
    | nil => intro start h; exact h
    | cons a s ih => intro start h; exact ih _ (cosetRound_sound hdom h)
  exact key js [rawOne dom] hstart

end Sound

/-! ## The number of representatives

The guard in `Algo.cosetNew` is what keeps the list short: a round only adds while the list
has at most `js.length` entries. -/

theorem length_cosetAdd_le (p : CosetParam × (RawGens × RawPerm)) :
    (cosetAdd p).length ≤ max p.2.1.length (p.1.2.2.length + 1) := by
  rw [cosetAdd]
  by_cases h : cosetNew p
  · rw [if_pos h]
    rw [cosetNew, Bool.and_eq_true] at h
    have := of_decide_eq_true h.1
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [if_neg h]; exact le_max_left _ _

theorem length_cosetFold_le (c : CosetParam) :
    ∀ (l : RawGens) (reps : RawGens),
      (List.foldl (fun acc cand => cosetAdd (c, (acc, cand))) reps l).length
        ≤ max reps.length (c.2.2.length + 1) := by
  intro l
  induction l with
  | nil => intro reps; exact le_max_left _ _
  | cons a s ih =>
      intro reps
      rw [List.foldl_cons]
      refine le_trans (ih _) ?_
      have h1 := length_cosetAdd_le (c, (reps, a))
      exact max_le (le_trans h1 (max_le_max_right _ (le_refl _))) (le_max_right _ _)

theorem length_cosetRound_le (c : CosetParam) (reps : RawGens) :
    (cosetRound (c, reps)).length ≤ max reps.length (c.2.2.length + 1) :=
  length_cosetFold_le c _ reps

/-- **At most `j + 1` representatives**, for `j = js.length`. -/
theorem length_rawCosetReps_le (c : CosetParam) :
    (rawCosetReps c).length ≤ c.2.2.length + 1 := by
  have key : ∀ (l : List ℕ) (start : RawGens), start.length ≤ c.2.2.length + 1 →
      (List.foldl (fun reps _ => cosetRound (c, reps)) start l).length
        ≤ c.2.2.length + 1 := by
    intro l
    induction l with
    | nil => intro start h; exact h
    | cons a s ih =>
        intro start h
        exact ih _ (le_trans (length_cosetRound_le c start) (max_le h (le_refl _)))
  exact key c.2.2 [rawOne c.1.1] (by simp)

/-! ## The size of the list of representatives

Two facts bound the state of the search.  The guard keeps the list short, and every entry is a
product of a previous entry with a generator, so its length is a generator's length and its
own entries are entries of a previous entry or of a generator.  Nothing grows. -/

theorem mem_cosetAdd_cases (p : CosetParam × (RawGens × RawPerm)) :
    cosetAdd p = p.2.1 ∨ cosetAdd p = p.2.1 ++ [p.2.2] := by
  rw [cosetAdd]
  by_cases h : cosetNew p
  · exact Or.inr (by rw [if_pos h])
  · exact Or.inl (by rw [if_neg h])

theorem mem_cosetAdd {p : CosetParam × (RawGens × RawPerm)} {x : RawPerm}
    (h : x ∈ cosetAdd p) : x ∈ p.2.1 ∨ x = p.2.2 := by
  rw [cosetAdd] at h
  by_cases hn : cosetNew p
  · rw [if_pos hn] at h
    rcases List.mem_append.1 h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.1 h1)
  · rw [if_neg hn] at h; exact Or.inl h

theorem mem_cosetFold (c : CosetParam) :
    ∀ (l : RawGens) (reps : RawGens) (x : RawPerm),
      x ∈ List.foldl (fun acc cand => cosetAdd (c, (acc, cand))) reps l →
        x ∈ reps ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro reps x h; exact Or.inl h
  | cons a s ih =>
      intro reps x h
      rw [List.foldl_cons] at h
      rcases ih _ x h with h1 | h1
      · rcases mem_cosetAdd h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by rw [h2]; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- The entries of a candidate are entries of a representative or of a generator, and its
length is a generator's length. -/
theorem cosetCands_bounds {reps gens : RawGens} {N : ℕ}
    (hg : ∀ g ∈ gens, g.length ≤ N ∧ ∀ y ∈ g, Enc.size y ≤ N)
    (hr : ∀ z ∈ reps, z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N) :
    ∀ x ∈ cosetCands (reps, gens), x.length ≤ N ∧ ∀ y ∈ x, Enc.size y ≤ N := by
  intro x hx
  obtain ⟨r, hrmem, g, hgmem, rfl⟩ := mem_cosetCands hx
  refine ⟨by rw [length_rawMul]; exact (hg g hgmem).1, ?_⟩
  intro y hy
  rcases mem_rawMul hy with h1 | h1
  · exact (hr r hrmem).2 y h1
  · exact (hg g hgmem).2 y h1

theorem cosetRound_bounds (cc : CosetParam) {N : ℕ}
    (hg : ∀ g ∈ cc.1.2, g.length ≤ N ∧ ∀ y ∈ g, Enc.size y ≤ N)
    (hjs : cc.2.2.length ≤ N) {reps : RawGens} (h1 : reps.length ≤ N + 1)
    (h2 : ∀ z ∈ reps, z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N) :
    (cosetRound (cc, reps)).length ≤ N + 1 ∧
      ∀ z ∈ cosetRound (cc, reps), z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N := by
  refine ⟨le_trans (length_cosetRound_le cc reps) (max_le h1 (by omega)), ?_⟩
  intro z hz
  rcases mem_cosetFold cc _ reps z hz with h3 | h3
  · exact h2 z h3
  · exact cosetCands_bounds hg h2 z h3

theorem cosetOuter_bounds (cc : CosetParam) {N : ℕ}
    (hg : ∀ g ∈ cc.1.2, g.length ≤ N ∧ ∀ y ∈ g, Enc.size y ≤ N)
    (hjs : cc.2.2.length ≤ N) :
    ∀ (l : List ℕ) (reps : RawGens), reps.length ≤ N + 1 →
      (∀ z ∈ reps, z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N) →
      (List.foldl (fun y (_ : ℕ) => cosetRound (cc, y)) reps l).length ≤ N + 1 ∧
        ∀ z ∈ List.foldl (fun y (_ : ℕ) => cosetRound (cc, y)) reps l,
          z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N := by
  intro l
  induction l with
  | nil => intro reps h1 h2; exact ⟨h1, h2⟩
  | cons a s ih =>
      intro reps h1 h2
      rw [List.foldl_cons]
      obtain ⟨k1, k2⟩ := cosetRound_bounds cc hg hjs h1 h2
      exact ih _ k1 k2

/-! ## The running time -/

theorem polyFun_cosetCands : PolyFun cosetCands := by
  have hf : PolyFun (fun z : RawGens × RawPerm => rawGensMul (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_rawGensMul
  exact (((polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam hf)).comp
    polyFun_flatten).of_eq (fun _ => rfl)

theorem polyFun_cosetNew : PolyFun cosetNew := by
  have hq : PolyFun (fun z : ((List ℕ × RawGens) × RawPerm) × RawPerm =>
      rawMem (z.1.1, rawMul (z.1.2, rawInv z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_rawInv)).comp
        polyFun_rawMul)).comp polyFun_rawMem
  have hfil : PolyFun (fun p : CosetParam × (RawGens × RawPerm) =>
      (p.2.1.filter
        (fun r => rawMem ((p.1.1.1, p.1.2.1), rawMul (p.2.2, rawInv r)))).isEmpty) :=
    (((((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair
        (polyFun_snd.comp polyFun_snd)).pair
          (polyFun_snd.comp polyFun_fst)).comp (PolyFun.filterParam hq)).comp
            polyFun_isEmpty)
  have hlen : PolyFun (fun p : CosetParam × (RawGens × RawPerm) =>
      decide (p.2.1.length ≤ p.1.2.2.length)) :=
    (((polyFun_snd.comp polyFun_fst).comp polyFun_length).pair
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_length)).comp polyFun_le
  refine (PolyFun.ite hlen hfil (polyFun_const false)).of_eq (fun p => ?_)
  rw [cosetNew]
  cases h : decide (p.2.1.length ≤ p.1.2.2.length) <;> simp [h]

theorem polyFun_cosetAdd : PolyFun cosetAdd := by
  have hadd : PolyFun (fun p : CosetParam × (RawGens × RawPerm) => p.2.1 ++ [p.2.2]) :=
    ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_singleton)).comp polyFun_append
  exact (PolyFun.ite polyFun_cosetNew hadd (polyFun_snd.comp polyFun_fst)).of_eq
    (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_cosetRound : PolyFun cosetRound := by
  have hacc : ∀ (cc : CosetParam) (x : RawGens) (r : RawGens) (j : ℕ),
      Enc.size (List.foldl (fun y a => cosetAdd (cc, (y, a))) x (r.take j))
        ≤ (fun m => 1 + (m + 1) * (2 * m + 1))
            (Enc.size ((cc, (x, r)) : CosetParam × (RawGens × RawGens))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) : CosetParam × (RawGens × RawGens)) with hN
    have hcc : Enc.size cc ≤ N := Combine.size_fst_le cc ((x, r) : RawGens × RawGens)
    have hxr : Enc.size ((x, r) : RawGens × RawGens) ≤ N :=
      Combine.size_snd_le cc ((x, r) : RawGens × RawGens)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hr : Enc.size r ≤ N := le_trans (Combine.size_snd_le x r) hxr
    have hjs : cc.2.2.length ≤ N := by
      have h1 : Enc.size cc.2 ≤ Enc.size cc := Combine.size_snd_le cc.1 cc.2
      have h2 : Enc.size cc.2.2 ≤ Enc.size cc.2 := Combine.size_snd_le cc.2.1 cc.2.2
      have h3 := length_le_size cc.2.2
      omega
    have hlen : (List.foldl (fun y a => cosetAdd (cc, (y, a))) x (r.take j)).length ≤ N + 1 := by
      refine le_trans (length_cosetFold_le cc (r.take j) x) (max_le ?_ (by omega))
      have := length_le_size x
      omega
    have hent : ∀ z ∈ List.foldl (fun y a => cosetAdd (cc, (y, a))) x (r.take j),
        Enc.size z ≤ N := by
      intro z hz
      rcases mem_cosetFold cc (r.take j) x z hz with h1 | h1
      · exact le_trans (size_mem_le h1) hx
      · exact le_trans (size_mem_le (List.mem_of_mem_take h1)) hr
    have hsize := size_list_le_of_entries _ N hent
    have hmul : (List.foldl (fun y a => cosetAdd (cc, (y, a))) x (r.take j)).length
        * (2 * N + 1) ≤ (N + 1) * (2 * N + 1) := Nat.mul_le_mul_right _ hlen
    dsimp only
    omega
  have hpb : PolyBound (fun m => 1 + (m + 1) * (2 * m + 1)) :=
    (polyBound_const 1).add ((polyBound_id.add (polyBound_const 1)).mul
      (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))
  have hfold := PolyFun.foldlParam polyFun_cosetAdd (p := fun m => 1 + (m + 1) * (2 * m + 1))
    hpb hacc
  have hin : PolyFun (fun p : CosetParam × RawGens =>
      ((p.1, ((p.2, cosetCands (p.2, p.1.1.2)) : RawGens × RawGens)) :
        CosetParam × (RawGens × RawGens))) :=
    polyFun_fst.pair (polyFun_snd.pair ((polyFun_snd.pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).comp polyFun_cosetCands))
  exact (hin.comp hfold).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawCosetReps : PolyFun rawCosetReps := by
  have hacc : ∀ (cc : CosetParam) (x : RawGens) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y (_ : ℕ) => cosetRound (cc, y)) x (r.take j))
        ≤ (fun m => 1 + (m + 1) * (2 * (1 + m * (2 * m + 1)) + 1))
            (Enc.size ((cc, (x, r)) : CosetParam × (RawGens × List ℕ))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) : CosetParam × (RawGens × List ℕ)) with hN
    have hcc : Enc.size cc ≤ N := Combine.size_fst_le cc ((x, r) : RawGens × List ℕ)
    have hxr : Enc.size ((x, r) : RawGens × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : RawGens × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hjs : cc.2.2.length ≤ N := by
      have h1 : Enc.size cc.2 ≤ Enc.size cc := Combine.size_snd_le cc.1 cc.2
      have h2 : Enc.size cc.2.2 ≤ Enc.size cc.2 := Combine.size_snd_le cc.2.1 cc.2.2
      have h3 := length_le_size cc.2.2
      omega
    have hg : ∀ g ∈ cc.1.2, g.length ≤ N ∧ ∀ y ∈ g, Enc.size y ≤ N := by
      intro g hgm
      have h1 : Enc.size cc.1 ≤ Enc.size cc := Combine.size_fst_le cc.1 cc.2
      have h2 : Enc.size cc.1.2 ≤ Enc.size cc.1 := Combine.size_snd_le cc.1.1 cc.1.2
      have h3 : Enc.size g ≤ Enc.size cc.1.2 := size_mem_le hgm
      have h4 := length_le_size g
      exact ⟨by omega, fun y hy => le_trans (size_mem_le hy) (by omega)⟩
    have hstart1 : x.length ≤ N + 1 := by have := length_le_size x; omega
    have hstart2 : ∀ z ∈ x, z.length ≤ N ∧ ∀ y ∈ z, Enc.size y ≤ N := by
      intro z hz
      have h1 : Enc.size z ≤ N := le_trans (size_mem_le hz) hx
      have h2 := length_le_size z
      exact ⟨by omega, fun y hy => le_trans (size_mem_le hy) h1⟩
    obtain ⟨hlen, hent⟩ := cosetOuter_bounds cc hg hjs (r.take j) x hstart1 hstart2
    have hzsize : ∀ z ∈ List.foldl (fun y (_ : ℕ) => cosetRound (cc, y)) x (r.take j),
        Enc.size z ≤ 1 + N * (2 * N + 1) := by
      intro z hz
      obtain ⟨hzl, hzy⟩ := hent z hz
      have h1 := size_list_le_of_entries z N hzy
      have h2 : z.length * (2 * N + 1) ≤ N * (2 * N + 1) := Nat.mul_le_mul_right _ hzl
      omega
    have hsize := size_list_le_of_entries _ (1 + N * (2 * N + 1)) hzsize
    have hmul : (List.foldl (fun y (_ : ℕ) => cosetRound (cc, y)) x (r.take j)).length
        * (2 * (1 + N * (2 * N + 1)) + 1)
        ≤ (N + 1) * (2 * (1 + N * (2 * N + 1)) + 1) := Nat.mul_le_mul_right _ hlen
    dsimp only
    omega
  have hpb : PolyBound (fun m => 1 + (m + 1) * (2 * (1 + m * (2 * m + 1)) + 1)) :=
    (polyBound_const 1).add ((polyBound_id.add (polyBound_const 1)).mul
      (((polyBound_const 2).mul ((polyBound_const 1).add
        (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add
          (polyBound_const 1))))).add (polyBound_const 1)))
  have hstep : PolyFun (fun z : CosetParam × (RawGens × ℕ) => cosetRound (z.1, z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_cosetRound
  have hfold := PolyFun.foldlParam hstep
    (p := fun m => 1 + (m + 1) * (2 * (1 + m * (2 * m + 1)) + 1)) hpb hacc
  have hin : PolyFun (fun c : CosetParam =>
      ((c, ((([rawOne c.1.1] : RawGens), c.2.2) : RawGens × List ℕ)) :
        CosetParam × (RawGens × List ℕ))) :=
    polyFun_id.pair ((((polyFun_fst.comp polyFun_fst).comp polyFun_rawOne).comp
      polyFun_singleton).pair (polyFun_snd.comp polyFun_snd))
  exact (hin.comp hfold).of_eq (fun _ => rfl)

theorem polyFun_rawCosetRep : PolyFun rawCosetRep :=
  (((polyFun_rawCosetReps.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_length)).pair
    ((polyFun_fst.comp polyFun_fst).comp polyFun_rawOne)).comp polyFun_getD).of_eq
    (fun _ => rfl)



/-! ## The covering half

`Algo.rawCosetReps_sound` says that the representatives lie in different right cosets of `H`.
What is left is that there are enough of them: the list found after `j` rounds has `j + 1`
entries as long as `j + 1` does not exceed the index, and once `j + 1` reaches the index every
element of `G` lies in one of the listed cosets.

The proof is the connectivity of the Cayley graph on the cosets, in three steps.

1. `Algo.covMonoid` — the set of group elements that map the union of the listed cosets into
   itself under right multiplication is a submonoid, hence (the group being finite) closed
   under inverses, hence a subgroup.  So if every representative times every generator stays
   inside the union, the union is all of `G`.
2. `Algo.cosetRound_length_lt` — therefore, while the union is not all of `G` and the guard of
   `Algo.cosetNew` still allows adding, one round of the search adds at least one entry.
3. `Algo.cosetOuter_progress` — so after `j` rounds either the union is all of `G` or the list
   has `j + 1` entries.

Counting the two halves against each other is done through the space of **right** cosets,
`Quotient (QuotientGroup.rightRel (H.subgroupOf G))`, whose cardinality is `|G : H|`
(`QuotientGroup.quotientRightRelEquivQuotientLeftRel`).

**The side.**  These are Lean's right cosets `H r`, because right multiplication is what
permutes them.  Proposition 11.1.6 as Lean states it
(`Babai.descent_of_cover`) asks instead for a cover `G = ⋃ σ • H` by Lean's *left* cosets.
The two are exchanged by inversion — `G = ⋃ H r` gives `G = G⁻¹ = ⋃ r⁻¹ H` — so a descent
round has to invert the representative (`Algo.rawInv`) before handing it to the child. -/

section Cover

open Equiv (Perm)

variable {n : ℕ}

/-- The union of the right cosets `H r` over the representatives `r` found so far. -/
def covSet (n : ℕ) (H : Subgroup (Perm (Fin n))) (l : RawGens) : Set (Perm (Fin n)) :=
  {τ | ∃ r ∈ l, τ * (decPerm n r)⁻¹ ∈ H}

theorem mem_covSet {H : Subgroup (Perm (Fin n))} {l : RawGens} {τ : Perm (Fin n)} :
    τ ∈ covSet n H l ↔ ∃ r ∈ l, τ * (decPerm n r)⁻¹ ∈ H := Iff.rfl

theorem covSet_mono {H : Subgroup (Perm (Fin n))} {l l' : RawGens} (h : ∀ r ∈ l, r ∈ l') :
    covSet n H l ⊆ covSet n H l' := by
  rintro τ ⟨r, hr, hτ⟩
  exact ⟨r, h r hr, hτ⟩

/-- A representative lies in its own coset. -/
theorem mem_covSet_self {H : Subgroup (Perm (Fin n))} {l : RawGens} {r : RawPerm} (hr : r ∈ l) :
    decPerm n r ∈ covSet n H l :=
  ⟨r, hr, by rw [mul_inv_cancel]; exact one_mem _⟩

/-- **Right multiplication that keeps every listed representative inside the union keeps the
whole union inside itself.** -/
theorem covSet_mul_mem {H : Subgroup (Perm (Fin n))} {l : RawGens} {τ g : Perm (Fin n)}
    (hτ : τ ∈ covSet n H l) (hg : ∀ r ∈ l, decPerm n r * g ∈ covSet n H l) :
    τ * g ∈ covSet n H l := by
  obtain ⟨r, hr, hh⟩ := hτ
  obtain ⟨r', hr', hh'⟩ := hg r hr
  refine ⟨r', hr', ?_⟩
  have : τ * g * (decPerm n r')⁻¹
      = (τ * (decPerm n r)⁻¹) * (decPerm n r * g * (decPerm n r')⁻¹) := by group
  rw [this]
  exact mul_mem hh hh'

/-- The elements that keep the union of the listed cosets inside itself under right
multiplication.  It is a submonoid by construction. -/
def covMonoid (n : ℕ) (H : Subgroup (Perm (Fin n))) (l : RawGens) : Submonoid (Perm (Fin n)) where
  carrier := {g | ∀ τ ∈ covSet n H l, τ * g ∈ covSet n H l}
  one_mem' := by intro τ hτ; simpa using hτ
  mul_mem' := by
    intro a b ha hb τ hτ
    have : τ * (a * b) = (τ * a) * b := by group
    rw [this]
    exact hb _ (ha τ hτ)

/-- **The submonoid is a subgroup**, because the group is finite: an inverse is a power. -/
theorem inv_mem_covMonoid {H : Subgroup (Perm (Fin n))} {l : RawGens} {g : Perm (Fin n)}
    (hg : g ∈ covMonoid n H l) : g⁻¹ ∈ covMonoid n H l := by
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hmem : g⁻¹ ∈ Submonoid.powers g :=
    hfin.mem_powers_iff_mem_zpowers.2 (inv_mem (Subgroup.mem_zpowers g))
  obtain ⟨k, hk⟩ := hmem
  rw [← hk]
  exact Submonoid.pow_mem _ hg k

/-- The subgroup of elements that keep the union of the listed cosets inside itself. -/
def covSubgroup (n : ℕ) (H : Subgroup (Perm (Fin n))) (l : RawGens) : Subgroup (Perm (Fin n)) where
  carrier := covMonoid n H l
  one_mem' := (covMonoid n H l).one_mem
  mul_mem' := fun ha hb => (covMonoid n H l).mul_mem ha hb
  inv_mem' := fun hx => inv_mem_covMonoid hx

/-- **If the union of the listed cosets is closed under the generators, it is all of `G`.**
This is the connectivity of the Cayley graph on the cosets. -/
theorem covSet_eq_of_closed {H : Subgroup (Perm (Fin n))}
    {gensG : List (Perm (Fin n))} {l : RawGens} {r₀ : RawPerm} (hr₀ : r₀ ∈ l)
    (hr₀G : decPerm n r₀ ∈ genGroup gensG)
    (hclosed : ∀ r ∈ l, ∀ g ∈ gensG, decPerm n r * g ∈ covSet n H l) :
    ∀ σ ∈ genGroup gensG, σ ∈ covSet n H l := by
  have hgen : genGroup gensG ≤ covSubgroup n H l := by
    rw [genGroup]
    refine Subgroup.closure_le _ |>.2 ?_
    intro g hg τ hτ
    exact covSet_mul_mem hτ (fun r hr => hclosed r hr g hg)
  intro σ hσ
  have hfac : σ = decPerm n r₀ * ((decPerm n r₀)⁻¹ * σ) := by group
  have hmem : (decPerm n r₀)⁻¹ * σ ∈ genGroup gensG :=
    mul_mem (inv_mem hr₀G) hσ
  rw [hfac]
  exact hgen hmem (decPerm n r₀) (mem_covSet_self hr₀)

/-! ### One round adds an entry -/

variable {dom : List ℕ} {gensG gensH : List (Perm (Fin n))} {js : List ℕ}

/-- The test `Algo.cosetNew` fires on a candidate outside the union of the listed cosets. -/
theorem cosetNew_of_not_mem_covSet (hdom : dom.length = n) {reps : RawGens} {cand : RawPerm}
    (hreps : ∀ r ∈ reps, RawPerm.WF n r) (hcand : RawPerm.WF n cand)
    (hlen : reps.length ≤ js.length)
    (h : decPerm n cand ∉ covSet n (genGroup gensH) reps) :
    cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
      (reps, cand)) = true := by
  rw [cosetNew, Bool.and_eq_true, List.isEmpty_iff, List.filter_eq_nil_iff]
  refine ⟨decide_eq_true hlen, ?_⟩
  intro r hr
  have hwfr := hreps r hr
  have hrw : rawMul (cand, rawInv r) = encPerm n (decPerm n cand * (decPerm n r)⁻¹) := by
    rw [← encPerm_decPerm hcand, ← encPerm_decPerm hwfr, rawInv_encPerm, rawMul_encPerm,
      encPerm_decPerm hcand, encPerm_decPerm hwfr]
  simp only [hrw, Bool.not_eq_true]
  rw [Bool.eq_false_iff, ne_eq, rawMem_spec dom hdom gensH _]
  exact fun hc => h ⟨r, hr, hc⟩

/-- A candidate the test rejects (while the guard still allows adding) already lies in the
union of the listed cosets. -/
theorem mem_covSet_of_not_cosetNew (hdom : dom.length = n) {reps : RawGens} {cand : RawPerm}
    (hreps : ∀ r ∈ reps, RawPerm.WF n r) (hcand : RawPerm.WF n cand)
    (hlen : reps.length ≤ js.length)
    (h : cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
      (reps, cand)) = false) :
    decPerm n cand ∈ covSet n (genGroup gensH) reps := by
  by_contra hc
  rw [cosetNew_of_not_mem_covSet (gensG := gensG) hdom hreps hcand hlen hc] at h
  exact absurd h (by simp)

/-- The fold over the candidates of a round only appends. -/
theorem cosetFold_append (c : CosetParam) :
    ∀ (l reps : RawGens), ∃ e : RawGens,
      List.foldl (fun acc cand => cosetAdd (c, (acc, cand))) reps l = reps ++ e := by
  intro l
  induction l with
  | nil => intro reps; exact ⟨[], by simp⟩
  | cons a s ih =>
      intro reps
      rw [List.foldl_cons]
      rcases mem_cosetAdd_cases (c, (reps, a)) with h | h
      · rw [h]
        obtain ⟨e, he⟩ := ih reps
        exact ⟨e, he⟩
      · rw [h]
        obtain ⟨e, he⟩ := ih (reps ++ [a])
        exact ⟨a :: e, by rw [he, List.append_assoc]; rfl⟩

/-- **The fold over the candidates adds an entry** as soon as one candidate lies outside the
union of the listed cosets. -/
theorem cosetFold_length_lt (hdom : dom.length = n) :
    ∀ (cands reps : RawGens),
      (∀ r ∈ reps, RawPerm.WF n r) → (∀ x ∈ cands, RawPerm.WF n x) →
      reps.length ≤ js.length →
      (∃ x ∈ cands, decPerm n x ∉ covSet n (genGroup gensH) reps) →
      reps.length <
        (List.foldl (fun acc cand =>
          cosetAdd (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), (acc, cand)))
          reps cands).length := by
  intro cands
  induction cands with
  | nil => intro reps _ _ _ h; obtain ⟨x, hx, -⟩ := h; simp at hx
  | cons a s ih =>
      intro reps hreps hcands hlen h
      rw [List.foldl_cons]
      by_cases hnew : cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
          (reps, a))
      · have hadd : cosetAdd (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
            (reps, a)) = reps ++ [a] := by rw [cosetAdd, if_pos hnew]
        rw [hadd]
        obtain ⟨e, he⟩ := cosetFold_append
          (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js))) s (reps ++ [a])
        rw [he]
        simp only [List.length_append, List.length_singleton]
        omega
      · have hfalse : cosetNew (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
            (reps, a)) = false := by simpa using hnew
        have hacov : decPerm n a ∈ covSet n (genGroup gensH) reps :=
          mem_covSet_of_not_cosetNew (gensG := gensG) hdom hreps
            (hcands a List.mem_cons_self) hlen hfalse
        have hkeep : cosetAdd (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
            (reps, a)) = reps := by rw [cosetAdd, if_neg hnew]
        rw [hkeep]
        obtain ⟨x, hx, hxc⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact absurd hacov hxc
        · exact ih reps hreps (fun z hz => hcands z (List.mem_cons_of_mem _ hz)) hlen
            ⟨x, hx', hxc⟩

/-- **One round adds an entry** while the union of the listed cosets is not all of `G` and the
guard still allows adding. -/
theorem cosetRound_length_lt (hdom : dom.length = n) {reps : RawGens}
    (hok : RepsOK n (genGroup gensG) (genGroup gensH) reps) {r₀ : RawPerm} (hr₀ : r₀ ∈ reps)
    (hlen : reps.length ≤ js.length)
    (hnc : ∃ σ ∈ genGroup gensG, σ ∉ covSet n (genGroup gensH) reps) :
    reps.length <
      (cosetRound (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps)).length := by
  obtain ⟨σ, hσ, hσc⟩ := hnc
  have hclosed : ¬ ∀ r ∈ reps, ∀ g ∈ gensG, decPerm n r * g ∈ covSet n (genGroup gensH) reps := by
    intro hc
    exact hσc (covSet_eq_of_closed hr₀ (hok.1 r₀ hr₀).2 hc σ hσ)
  simp only [not_forall, Classical.not_imp] at hclosed
  obtain ⟨r, hrmem, g, hgmem, hgc⟩ := hclosed
  have hwfr := (hok.1 r hrmem).1
  have hcand : rawMul (r, encPerm n g) ∈ cosetCands (reps, gensG.map (encPerm n)) := by
    rw [cosetCands, List.mem_flatten]
    exact ⟨rawGensMul (r, gensG.map (encPerm n)), List.mem_map_of_mem hrmem,
      List.mem_map_of_mem (List.mem_map_of_mem hgmem)⟩
  have hdec : decPerm n (rawMul (r, encPerm n g)) = decPerm n r * g := by
    rw [rawMul_of_wf hwfr (wf_encPerm n g), decPerm_encPerm, decPerm_encPerm]
  exact cosetFold_length_lt (gensG := gensG) hdom _ reps (fun z hz => (hok.1 z hz).1)
    (fun x hx => (cosetCands_sound hok.1 x hx).1) hlen
    ⟨_, hcand, by rw [hdec]; exact hgc⟩

/-! ### The progress of the search -/

/-- **After `k` rounds either the union of the listed cosets is all of `G`, or the list has
`k + 1` entries** (truncated at the guard `js.length + 1`). -/
theorem cosetOuter_progress (hdom : dom.length = n) :
    ∀ (l : List ℕ) (start : RawGens), RepsOK n (genGroup gensG) (genGroup gensH) start →
      (∃ r₀, r₀ ∈ start) →
      (∀ σ ∈ genGroup gensG, σ ∈ covSet n (genGroup gensH)
          (List.foldl (fun reps _ => cosetRound
            (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps)) start l)) ∨
        min (js.length + 1) (start.length + l.length) ≤
          (List.foldl (fun reps _ => cosetRound
            (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps))
            start l).length := by
  intro l
  induction l with
  | nil => intro start _ _; exact Or.inr (by simp)
  | cons a s ih =>
      intro start hok hne
      set c : CosetParam := ((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)) with hc
      have hstep : List.foldl (fun reps (_ : ℕ) => cosetRound (c, reps)) start (a :: s)
          = List.foldl (fun reps (_ : ℕ) => cosetRound (c, reps)) (cosetRound (c, start)) s := by
        rw [List.foldl_cons]
      -- the list only grows along the outer fold
      have hgrow : ∀ (t : List ℕ) (x : RawGens), ∃ e : RawGens,
          List.foldl (fun reps (_ : ℕ) => cosetRound (c, reps)) x t = x ++ e := by
        intro t
        induction t with
        | nil => intro x; exact ⟨[], by simp⟩
        | cons b u ihu =>
            intro x
            rw [List.foldl_cons]
            obtain ⟨e₁, he₁⟩ := cosetFold_append c (cosetCands (x, c.1.2)) x
            obtain ⟨e₂, he₂⟩ := ihu (cosetRound (c, x))
            refine ⟨e₁ ++ e₂, ?_⟩
            rw [he₂, show cosetRound (c, x) = x ++ e₁ from he₁, List.append_assoc]
      obtain ⟨e₀, he₀⟩ := hgrow s (cosetRound (c, start))
      obtain ⟨e₁, he₁⟩ := cosetFold_append c (cosetCands (start, c.1.2)) start
      have hpref : ∀ r ∈ start,
          r ∈ List.foldl (fun reps (_ : ℕ) => cosetRound (c, reps)) start (a :: s) := by
        intro r hr
        rw [hstep, he₀, show cosetRound (c, start) = start ++ e₁ from he₁]
        exact List.mem_append_left _ (List.mem_append_left _ hr)
      by_cases hcov : ∀ σ ∈ genGroup gensG, σ ∈ covSet n (genGroup gensH) start
      · exact Or.inl (fun σ hσ => covSet_mono hpref (hcov σ hσ))
      · by_cases hguard : start.length ≤ js.length
        · obtain ⟨r₀, hr₀⟩ := hne
          have hlt := cosetRound_length_lt hdom hok hr₀ hguard
            (by simp only [not_forall] at hcov
                obtain ⟨σ, hσ1, hσ2⟩ := hcov; exact ⟨σ, hσ1, hσ2⟩)
          rw [← hc] at hlt
          have hok' : RepsOK n (genGroup gensG) (genGroup gensH) (cosetRound (c, start)) :=
            cosetRound_sound hdom hok
          have hne' : ∃ r, r ∈ cosetRound (c, start) := by
            refine ⟨r₀, ?_⟩
            rw [show cosetRound (c, start) = start ++ e₁ from he₁]
            exact List.mem_append_left _ hr₀
          rcases ih (cosetRound (c, start)) hok' hne' with h | h
          · exact Or.inl (by rw [hstep]; exact h)
          · refine Or.inr ?_
            rw [hstep]
            refine le_trans ?_ h
            simp only [List.length_cons]
            exact min_le_min (le_refl _) (by omega)
        · refine Or.inr ?_
          rw [hstep, he₀, show cosetRound (c, start) = start ++ e₁ from he₁]
          simp only [List.length_append]
          omega

/-! ### Counting against the index -/

/-- The right coset of `H` in `G` of the `i`-th representative. -/
noncomputable def repClass (H G : Subgroup (Perm (Fin n))) (l : RawGens)
    (hmem : ∀ r ∈ l, decPerm n r ∈ G) (i : Fin l.length) :
    Quotient (QuotientGroup.rightRel (H.subgroupOf G)) :=
  Quotient.mk _ ⟨decPerm n l[(i : ℕ)], hmem _ (List.getElem_mem i.isLt)⟩

theorem card_rightQuotient (H G : Subgroup (Perm (Fin n))) :
    Nat.card (Quotient (QuotientGroup.rightRel (H.subgroupOf G))) = H.relIndex G := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf G))]
  exact (Subgroup.index_eq_card _).symm

theorem injective_repClass {H G : Subgroup (Perm (Fin n))} {l : RawGens}
    (hmem : ∀ r ∈ l, decPerm n r ∈ G)
    (hpw : l.Pairwise (fun a b => decPerm n b * (decPerm n a)⁻¹ ∉ H)) :
    Function.Injective (repClass H G l hmem) := by
  have hget := List.pairwise_iff_getElem.1 hpw
  have key : ∀ i j : Fin l.length, (i : ℕ) < (j : ℕ) →
      repClass H G l hmem i ≠ repClass H G l hmem j := by
    intro i j hij hEq
    have h := QuotientGroup.rightRel_apply.mp (Quotient.exact hEq)
    rw [Subgroup.mem_subgroupOf] at h
    exact hget (i : ℕ) (j : ℕ) i.isLt j.isLt hij (by simpa using h)
  intro i j hEq
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · exact absurd hEq (key i j h)
  · exact Fin.ext h
  · exact absurd hEq.symm (key j i h)

/-- **Distinct cosets: at most `|G : H|` representatives.** -/
theorem length_le_relIndex {H G : Subgroup (Perm (Fin n))} {l : RawGens}
    (hmem : ∀ r ∈ l, decPerm n r ∈ G)
    (hpw : l.Pairwise (fun a b => decPerm n b * (decPerm n a)⁻¹ ∉ H)) :
    l.length ≤ H.relIndex G := by
  have h := Nat.card_le_card_of_injective _ (injective_repClass hmem hpw)
  rwa [Nat.card_fin, card_rightQuotient] at h

/-- **Covering: at least `|G : H|` representatives.** -/
theorem relIndex_le_length_of_cover {H G : Subgroup (Perm (Fin n))} {l : RawGens}
    (hmem : ∀ r ∈ l, decPerm n r ∈ G)
    (hcov : ∀ σ ∈ G, ∃ r ∈ l, σ * (decPerm n r)⁻¹ ∈ H) :
    H.relIndex G ≤ l.length := by
  have hsurj : Function.Surjective (repClass H G l hmem) := by
    intro q
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    obtain ⟨r, hr, hσ⟩ := hcov (σ : Perm (Fin n)) σ.2
    obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
    refine ⟨⟨i, hi⟩, ?_⟩
    refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
    rw [Subgroup.mem_subgroupOf]
    simpa [hri] using hσ
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_fin, card_rightQuotient] at h

/-! ### The two statements -/

variable (dom gensG gensH js)

/-- **(a) The search finds a new coset at every round**, as long as the number of rounds does
not exceed the index: the list at the index `j` has exactly `j + 1` entries.  Paper: the right
coset representatives of Prop. 11.1.6 and Thm. 11.1.9 (§11.1). -/
theorem length_rawCosetReps_eq (hdom : dom.length = n)
    (hidx : js.length + 1 ≤ (genGroup gensH).relIndex (genGroup gensG)) :
    (rawCosetReps ((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js))).length
      = js.length + 1 := by
  have hstart : RepsOK n (genGroup gensG) (genGroup gensH) [rawOne dom] := by
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro r hr
    rw [List.mem_singleton.1 hr, rawOne_eq dom, hdom]
    exact ⟨wf_encPerm n 1, by rw [decPerm_encPerm]; exact Subgroup.one_mem _⟩
  have hup : (rawCosetReps ((dom, gensG.map (encPerm n)),
      (gensH.map (encPerm n), js))).length ≤ js.length + 1 := length_rawCosetReps_le _
  have hsound := rawCosetReps_sound (gensG := gensG) (gensH := gensH) (js := js) hdom
  rw [rawCosetReps_eq] at hup ⊢
  rcases cosetOuter_progress (gensG := gensG) (gensH := gensH) (js := js) hdom js [rawOne dom]
      hstart ⟨rawOne dom, List.mem_singleton_self _⟩ with hcov | hlen
  · rw [rawCosetReps_eq] at hsound
    have hge := relIndex_le_length_of_cover (fun r hr => (hsound.1 r hr).2)
      (fun σ hσ => hcov σ hσ)
    omega
  · have hlen' : js.length + 1 ≤ _ :=
      le_trans (le_min (le_refl (js.length + 1)) (by simp)) hlen
    omega

/-- **(b) The search covers `G`** once the index is reached: every `σ ∈ G` lies in the right
coset `H · r` of one of the representatives listed at the index `j = js.length`.  With
`Algo.rawCosetReps_sound` this says that the list at the index `|G : H| - 1` is a right
transversal of `H` in `G`.  Paper: the right coset representatives of Prop. 11.1.6 and
Thm. 11.1.9 (§11.1). -/
theorem rawCosetReps_cover (hdom : dom.length = n)
    (hidx : (genGroup gensH).relIndex (genGroup gensG) ≤ js.length + 1) :
    ∀ σ ∈ genGroup gensG,
      ∃ r ∈ rawCosetReps ((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)),
        σ * (decPerm n r)⁻¹ ∈ genGroup gensH := by
  have hstart : RepsOK n (genGroup gensG) (genGroup gensH) [rawOne dom] := by
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro r hr
    rw [List.mem_singleton.1 hr, rawOne_eq dom, hdom]
    exact ⟨wf_encPerm n 1, by rw [decPerm_encPerm]; exact Subgroup.one_mem _⟩
  have hup : (rawCosetReps ((dom, gensG.map (encPerm n)),
      (gensH.map (encPerm n), js))).length ≤ js.length + 1 := length_rawCosetReps_le _
  have hsound := rawCosetReps_sound (gensG := gensG) (gensH := gensH) (js := js) hdom
  rw [rawCosetReps_eq] at hup hsound ⊢
  rcases cosetOuter_progress (gensG := gensG) (gensH := gensH) (js := js) hdom js [rawOne dom]
      hstart ⟨rawOne dom, List.mem_singleton_self _⟩ with hcov | hlen
  · exact fun σ hσ => hcov σ hσ
  · -- the list is full, and it is injective into the coset space, so it is onto
    set l := List.foldl (fun reps (_ : ℕ) =>
      cosetRound (((dom, gensG.map (encPerm n)), (gensH.map (encPerm n), js)), reps))
      [rawOne dom] js with hl
    have hle := length_le_relIndex (fun r hr => (hsound.1 r hr).2) hsound.2
    have hlen' : js.length + 1 ≤ l.length :=
      le_trans (le_min (le_refl (js.length + 1)) (by simp)) hlen
    have hcard : (genGroup gensH).relIndex (genGroup gensG) ≤ Nat.card (Fin l.length) := by
      rw [Nat.card_fin]
      omega
    have hbij : Function.Bijective
        (repClass (genGroup gensH) (genGroup gensG) l (fun r hr => (hsound.1 r hr).2)) :=
      Function.Injective.bijective_of_nat_card_le
        (injective_repClass (fun r hr => (hsound.1 r hr).2) hsound.2)
        (by rwa [card_rightQuotient])
    intro σ hσ
    obtain ⟨i, hi⟩ := hbij.2 (Quotient.mk _ ⟨σ, hσ⟩)
    refine ⟨l[(i : ℕ)], List.getElem_mem i.isLt, ?_⟩
    have h := QuotientGroup.rightRel_apply.mp (Quotient.exact hi)
    rw [Subgroup.mem_subgroupOf] at h
    exact h

end Cover

end Algo
