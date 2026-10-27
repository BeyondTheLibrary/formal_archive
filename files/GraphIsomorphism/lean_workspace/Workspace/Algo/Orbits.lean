/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: orbits of a list of generators on raw data.
-/
import Workspace.Algo.Perm
import Workspace.Machine.ListOps3

/-!
# Orbits on raw data

The paper never states this routine, and never proves anything about it, but almost every
algorithm of Secs. 11–15 uses it: the Chain Rule (Prop. 11.1.7), Eq. (64), Theorem 11.1.9 and
Observation 11.1.11 all speak of "the orbits of `G`".  `Workspace/Algo/DESIGN.md`, item 2,
class D, lists it first among the routines that have to be **proved**, since the paper cites no
source for them.  This file is that proof, work package A3.

Everything is on the raw types of `Workspace/Algo/Encodings.lean`, where the degree `n` is read
off the data rather than carried in a type index, because `RAM.PolyFun` is a statement about one
function between two fixed encodable types.

## The loop, and why it stops

`Algo.rawOrbit (gs, i)` starts from the one-point list `[i]` and runs rounds.  One round sends
every point found so far through every generator and adds the points that are new
(`Algo.rawOrbitStep`).  The number of rounds is the length of `gs.flatten`, which for
well-formed generators is `|gs| · n`, hence at least `n` as soon as there is one generator.
That is enough: a round that does not close the set adds at least one point, and there are at
most `n` points, so after `n` rounds the set is closed (`Algo.rawOrbit_closed`).  The round
count arrives as the *length of a list*, never as a machine natural, for the reason recorded at
the end of `Workspace/Machine/DESIGN.md`.

## Closure under the group

Being closed under every generator is not, on the face of it, being closed under the generated
group: a group needs inverses.  Finiteness supplies them.  A generator maps the closed set into
itself injectively, so it maps it **onto** itself, and the permutations that map a fixed finite
set onto itself form a subgroup (`Algo.setStabilizer`).  The generated group is inside that
subgroup, which is `Algo.image_eq_of_mem_genGroup`.

## Main definitions

`Algo.rawOrbitImages`, `Algo.rawOrbitStep`, `Algo.rawOrbit`, `Algo.rawIsTransitive`,
`Algo.rawIsInvariant`, `Algo.rawOrbitsStep`, `Algo.rawOrbits`.

## Main results

* `Algo.mem_rawOrbit_iff`, `Algo.rawOrbit_spec` — the entries of `Algo.rawOrbit` are exactly the
  orbit of the point under `Algo.decGroup`;
* `Algo.rawOrbits_mem`, `Algo.rawOrbits_pairwise`, `Algo.rawOrbits_cover`,
  `Algo.rawOrbits_spec` — the entries of `Algo.rawOrbits` are the orbits, each listed once;
* `Algo.polyFun_rawOrbit`, `Algo.polyFun_rawOrbits`, `Algo.polyFun_rawIsTransitive`,
  `Algo.polyFun_rawIsInvariant`;
* `Algo.rawIsTransitive_eq_true_iff` against `Babai.IsTransitive`, and
  `Algo.rawIsInvariant_eq_true_iff` against `Babai.IsInvariant`.

Every routine is total: on raw data that is not well formed it answers junk, and no
specification lemma claims anything about that answer.  No axiom, no `sorry`, no running-time
claim outside `RAM.PolyFun`.
-/

namespace Algo

open RAM RAM.Targets

/-! ## A finite set that every generator preserves

The permutations mapping a fixed finite set of points onto itself form a subgroup.  Closure
under inverses is free here, because the condition is an *equality* of images; what needs
finiteness is passing from "maps into" to "maps onto", and that is done once, per generator, in
`Algo.image_eq_of_mem_genGroup`. -/

/-- The setwise stabilizer of a finite set of points inside the full symmetric group. -/
def setStabilizer {n : ℕ} (T : Finset (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | T.image (σ : Equiv.Perm (Fin n)) = T}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [show ((a * b : Equiv.Perm (Fin n)) : Fin n → Fin n) = (a : Fin n → Fin n) ∘ b from rfl,
      ← Finset.image_image, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Finset.image_image]
    simp [Function.comp_def]

/-- **Closed under the generators means invariant under the group.**  A generator maps the finite
set `T` into itself and is injective, so it maps `T` onto `T`; the permutations that do so form a
subgroup, which therefore contains the whole generated group. -/
theorem image_eq_of_mem_genGroup {n : ℕ} (T : Finset (Fin n))
    (gens : List (Equiv.Perm (Fin n))) (hclosed : ∀ g ∈ gens, ∀ y ∈ T, g y ∈ T)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ genGroup gens) : T.image σ = T := by
  classical
  have hgen : {g : Equiv.Perm (Fin n) | g ∈ gens} ⊆ (setStabilizer T : Set (Equiv.Perm (Fin n))) := by
    intro g hg
    have hsub : T.image g ⊆ T := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact hclosed g hg z hz
    have hcard : T.card ≤ (T.image g).card := by
      rw [Finset.card_image_of_injective _ g.injective]
    exact Finset.eq_of_subset_of_card_le hsub hcard
  have hle : genGroup gens ≤ setStabilizer T := by
    rw [genGroup]
    exact (Subgroup.closure_le _).2 hgen
  exact hle hσ

/-- A generator of a raw group decodes to an element of the decoded group. -/
theorem decPerm_mem_decGroup {n : ℕ} {gs : RawGens} {g : RawPerm} (hg : g ∈ gs) :
    decPerm n g ∈ decGroup n gs :=
  Subgroup.subset_closure (List.mem_map_of_mem hg)

/-- An orbit is closed under the group. -/
theorem smul_mem_orbit {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {x y : Fin n}
    (hy : y ∈ MulAction.orbit G x) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ G) :
    σ y ∈ MulAction.orbit G x := by
  obtain ⟨g, hg⟩ := hy
  have hg' : (g : G) • x = y := hg
  refine ⟨(⟨σ, hσ⟩ : G) * g, ?_⟩
  have h2 : ((⟨σ, hσ⟩ : G) * g) • x = (⟨σ, hσ⟩ : G) • (g • x) := mul_smul _ _ _
  have h3 : ((⟨σ, hσ⟩ : G) * g) • x = σ y := by rw [h2, hg']; rfl
  exact h3

/-! ## One round

`Algo.rawImages` of `Workspace/Algo/Perm.lean` sends one point through every generator.  One
round does that for every point found so far — a map with a parameter, followed by a flattening
— and inserts the answers without repetition. -/

/-- **The images of every point of a list under every generator.** -/
def rawOrbitImages (p : RawGens × List ℕ) : List ℕ :=
  (p.2.map (fun j => rawImages (j, p.1))).flatten

/-- **One round of the closure loop**: the points found so far, together with the points their
images add. -/
def rawOrbitStep (p : RawGens × List ℕ) : List ℕ :=
  dedupInto (p.2, rawOrbitImages p)

/-- **The orbit of a point under a list of generators.**  The number of rounds is the length of
`gs.flatten`; see the header for why that is enough, and why the count may not be a machine
natural. -/
def rawOrbit (p : RawGens × ℕ) : List ℕ :=
  List.foldl (fun acc (_ : ℕ) => rawOrbitStep (p.1, acc)) [p.2] p.1.flatten

theorem mem_rawOrbitImages_iff (gs : RawGens) (acc : List ℕ) (k : ℕ) :
    k ∈ rawOrbitImages (gs, acc) ↔ ∃ j ∈ acc, ∃ g ∈ gs, k = rawApply (g, j) := by
  constructor
  · intro h
    rw [rawOrbitImages, List.mem_flatten] at h
    obtain ⟨u, hu, hk⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
    simp only [rawImages, List.mem_map] at hk
    obtain ⟨g, hg, hgk⟩ := hk
    exact ⟨j, hj, g, hg, hgk.symm⟩
  · rintro ⟨j, hj, g, hg, rfl⟩
    rw [rawOrbitImages, List.mem_flatten]
    refine ⟨rawImages (j, gs), List.mem_map_of_mem hj, ?_⟩
    simp only [rawImages, List.mem_map]
    exact ⟨g, hg, rfl⟩

theorem mem_rawOrbitStep_iff (gs : RawGens) (acc : List ℕ) (k : ℕ) :
    k ∈ rawOrbitStep (gs, acc) ↔ k ∈ acc ∨ ∃ j ∈ acc, ∃ g ∈ gs, k = rawApply (g, j) := by
  rw [rawOrbitStep, dedupInto, mem_dedupInto, mem_rawOrbitImages_iff]

/-- The step only adds points. -/
theorem mem_rawOrbitStep_of_mem {gs : RawGens} {acc : List ℕ} {k : ℕ} (h : k ∈ acc) :
    k ∈ rawOrbitStep (gs, acc) :=
  (mem_rawOrbitStep_iff gs acc k).2 (Or.inl h)

/-- The step sees the accumulator only through its entries. -/
theorem mem_rawOrbitStep_congr (gs : RawGens) {a b : List ℕ} (h : ∀ k, k ∈ a ↔ k ∈ b) (k : ℕ) :
    k ∈ rawOrbitStep (gs, a) ↔ k ∈ rawOrbitStep (gs, b) := by
  simp only [mem_rawOrbitStep_iff]
  constructor
  · rintro (h1 | ⟨j, hj, g, hg, hk⟩)
    · exact Or.inl ((h k).1 h1)
    · exact Or.inr ⟨j, (h j).1 hj, g, hg, hk⟩
  · rintro (h1 | ⟨j, hj, g, hg, hk⟩)
    · exact Or.inl ((h k).2 h1)
    · exact Or.inr ⟨j, (h j).2 hj, g, hg, hk⟩

/-! ## The loop as an iteration

A fold that ignores the entries of the list it runs over is an iteration; the list is there only
to supply the number of rounds. -/

theorem foldl_const_eq_iterate {g : List ℕ → List ℕ} : ∀ (l : List ℕ) (x : List ℕ),
    List.foldl (fun y (_ : ℕ) => g y) x l = g^[l.length] x := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

theorem rawOrbit_eq_iterate (gs : RawGens) (i : ℕ) :
    rawOrbit (gs, i) = (fun acc => rawOrbitStep (gs, acc))^[gs.flatten.length] [i] :=
  foldl_const_eq_iterate _ _

/-- **The shape of the accumulator along the loop.**  Whatever the start, the points added are
free of repetitions and all of them are entries of the generators.  This is what bounds the
accumulator, and what makes the counting argument below possible. -/
theorem rawOrbitIter_struct (gs : RawGens) (x : List ℕ) : ∀ m : ℕ,
    ∃ e : List ℕ, (fun acc => rawOrbitStep (gs, acc))^[m] x = e ++ x ∧ e.Nodup ∧
      (∀ k ∈ e, k ∉ x) ∧ (∀ k ∈ e, k ∈ gs.flatten) := by
  intro m
  induction m with
  | zero => exact ⟨[], by simp, by simp, by simp, by simp⟩
  | succ m ih =>
      obtain ⟨e, he, hnd, hnx, hmem⟩ := ih
      rw [Function.iterate_succ_apply', he]
      obtain ⟨e', he', hnd', hnx', hmem'⟩ :=
        dedupInto_struct (rawOrbitImages (gs, e ++ x)) (e ++ x)
      have hstep : rawOrbitStep (gs, e ++ x) = e' ++ (e ++ x) := he'
      have hflat : ∀ k ∈ e', k ∈ gs.flatten := by
        intro k hk
        have hnotin : k ∉ e ++ x := hnx' k hk
        have himg := hmem' k hk
        obtain ⟨j, hj, g, hg, hkj⟩ := (mem_rawOrbitImages_iff gs (e ++ x) k).1 himg
        by_cases hlt : j < g.length
        · have hk2 : k = g[j] := by
            rw [hkj]
            show g.getD j j = g[j]
            exact List.getD_eq_getElem _ _ hlt
          exact hk2 ▸ List.mem_flatten.2 ⟨g, hg, List.getElem_mem hlt⟩
        · have hk2 : k = j := by
            rw [hkj]
            show g.getD j j = j
            exact List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
          exact absurd (hk2 ▸ hj) hnotin
      refine ⟨e' ++ e, by rw [hstep, List.append_assoc], ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd', hnd, ?_⟩
        intro b hb c hc hbc
        exact (hnx' b hb) (hbc ▸ List.mem_append_left x hc)
      · intro k hk
        rcases List.mem_append.1 hk with hk1 | hk1
        · exact fun hx => (hnx' k hk1) (List.mem_append_right e hx)
        · exact hnx k hk1
      · intro k hk
        rcases List.mem_append.1 hk with hk1 | hk1
        · exact hflat k hk1
        · exact hmem k hk1

/-- The entries of the accumulator, at any round. -/
theorem mem_rawOrbitIter_of_mem (gs : RawGens) (x : List ℕ) (m : ℕ) {k : ℕ} (h : k ∈ x) :
    k ∈ (fun acc => rawOrbitStep (gs, acc))^[m] x := by
  obtain ⟨e, he, _, _, _⟩ := rawOrbitIter_struct gs x m
  rw [he]
  exact List.mem_append_right e h

/-- The loop is monotone. -/
theorem mem_rawOrbitIter_succ (gs : RawGens) (x : List ℕ) (m : ℕ) {k : ℕ}
    (h : k ∈ (fun acc => rawOrbitStep (gs, acc))^[m] x) :
    k ∈ (fun acc => rawOrbitStep (gs, acc))^[m + 1] x := by
  rw [Function.iterate_succ_apply']
  exact mem_rawOrbitStep_of_mem h

theorem nodup_rawOrbit (gs : RawGens) (i : ℕ) : (rawOrbit (gs, i)).Nodup := by
  rw [rawOrbit_eq_iterate]
  obtain ⟨e, he, hnd, hnx, _⟩ := rawOrbitIter_struct gs [i] gs.flatten.length
  rw [he, List.nodup_append]
  refine ⟨hnd, List.nodup_singleton i, ?_⟩
  intro b hb c hc hbc
  exact (hnx b hb) (hbc ▸ hc)

theorem mem_rawOrbit_self (gs : RawGens) (i : ℕ) : i ∈ rawOrbit (gs, i) := by
  rw [rawOrbit_eq_iterate]
  exact mem_rawOrbitIter_of_mem gs [i] _ (List.mem_singleton_self i)

/-! ## The entries lie in the orbit

Every point the loop finds is reached from `i` by a product of generators, so it lies in the
orbit.  The induction is on the number of rounds. -/

theorem rawOrbitIter_mem_orbit {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {i : ℕ}
    (hi : i < n) : ∀ (m : ℕ) (k : ℕ),
      k ∈ (fun acc => rawOrbitStep (gs, acc))^[m] [i] →
        ∃ h : k < n, (⟨k, h⟩ : Fin n) ∈ MulAction.orbit (decGroup n gs) ⟨i, hi⟩ := by
  intro m
  induction m with
  | zero =>
      intro k hk
      rw [Function.iterate_zero_apply, List.mem_singleton] at hk
      subst hk
      exact ⟨hi, MulAction.mem_orbit_self _⟩
  | succ m ih =>
      intro k hk
      rw [Function.iterate_succ_apply', mem_rawOrbitStep_iff] at hk
      rcases hk with hk | ⟨j, hj, g, hg, rfl⟩
      · exact ih k hk
      · obtain ⟨hjn, hjorb⟩ := ih j hj
        have hwf : RawPerm.WF n g := hgs g hg
        have happ : rawApply (g, j) = ((decPerm n g ⟨j, hjn⟩ : Fin n) : ℕ) :=
          rawApply_of_wf hwf hjn
        refine ⟨by rw [happ]; exact (decPerm n g ⟨j, hjn⟩).isLt, ?_⟩
        have hfin : (⟨rawApply (g, j), by rw [happ]; exact (decPerm n g ⟨j, hjn⟩).isLt⟩ : Fin n)
            = decPerm n g ⟨j, hjn⟩ := Fin.ext happ
        rw [hfin]
        exact smul_mem_orbit hjorb (decPerm_mem_decGroup hg)

/-! ## The loop closes

The counting argument: a round that does not close the point set adds a point, and there are at
most `n` points. -/

/-- A member of a list of lists is no longer than the flattened list. -/
theorem length_le_length_flatten {g : List ℕ} : ∀ {gs : List (List ℕ)}, g ∈ gs →
    g.length ≤ gs.flatten.length := by
  intro gs
  induction gs with
  | nil => intro h; exact absurd h (by simp)
  | cons a t ih =>
      intro h
      rw [List.flatten_cons, List.length_append]
      rcases List.mem_cons.1 h with rfl | h'
      · omega
      · have := ih h'; omega

/-- **The counting step.**  Either some round has already closed the set, or the set has grown by
one point in each of the rounds so far. -/
theorem stable_or_card_le (gs : RawGens) (i : ℕ) :
    ∀ M : ℕ,
      (∃ m < M, ∀ k, k ∈ (fun acc => rawOrbitStep (gs, acc))^[m + 1] [i] ↔
          k ∈ (fun acc => rawOrbitStep (gs, acc))^[m] [i]) ∨
      M + 1 ≤ (((fun acc => rawOrbitStep (gs, acc))^[M] [i]).toFinset).card := by
  classical
  intro M
  induction M with
  | zero =>
      right
      have hmem : i ∈ ((fun acc => rawOrbitStep (gs, acc))^[0] [i]).toFinset := by
        rw [List.mem_toFinset, Function.iterate_zero_apply]
        exact List.mem_singleton_self i
      exact Finset.card_pos.2 ⟨i, hmem⟩
  | succ M ih =>
      rcases ih with ⟨m, hm, hstab⟩ | hcard
      · exact Or.inl ⟨m, by omega, hstab⟩
      · by_cases hst : ∀ k, k ∈ (fun acc => rawOrbitStep (gs, acc))^[M + 1] [i] ↔
            k ∈ (fun acc => rawOrbitStep (gs, acc))^[M] [i]
        · exact Or.inl ⟨M, by omega, hst⟩
        · right
          have hsub : ((fun acc => rawOrbitStep (gs, acc))^[M] [i]).toFinset ⊆
              ((fun acc => rawOrbitStep (gs, acc))^[M + 1] [i]).toFinset := by
            intro k hk
            rw [List.mem_toFinset] at hk ⊢
            exact mem_rawOrbitIter_succ gs [i] M hk
          have hne : ((fun acc => rawOrbitStep (gs, acc))^[M] [i]).toFinset ≠
              ((fun acc => rawOrbitStep (gs, acc))^[M + 1] [i]).toFinset := by
            intro heq
            apply hst
            intro k
            constructor
            · intro hk
              have : k ∈ ((fun acc => rawOrbitStep (gs, acc))^[M + 1] [i]).toFinset := by
                rw [List.mem_toFinset]; exact hk
              rw [← heq, List.mem_toFinset] at this
              exact this
            · intro hk
              exact mem_rawOrbitIter_succ gs [i] M hk
          have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
          omega

/-- **The loop closes.**  Every generator maps the answer into itself. -/
theorem rawOrbit_closed {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {i : ℕ} (hi : i < n)
    {k : ℕ} (hk : k ∈ rawOrbit (gs, i)) {g : RawPerm} (hg : g ∈ gs) :
    rawApply (g, k) ∈ rawOrbit (gs, i) := by
  classical
  set F : List ℕ → List ℕ := fun acc => rawOrbitStep (gs, acc) with hF
  set M : ℕ := gs.flatten.length with hM
  have hMn : n ≤ M := by
    have h1 : g.length ≤ gs.flatten.length := length_le_length_flatten hg
    have h2 : g.length = n := (hgs g hg).length
    omega
  -- the point set never leaves `[0, n)`
  have hrange : ∀ m : ℕ, (F^[m] [i]).toFinset ⊆ Finset.range n := by
    intro m a ha
    rw [List.mem_toFinset] at ha
    obtain ⟨han, _⟩ := rawOrbitIter_mem_orbit hgs hi m a ha
    simpa using han
  -- so the counting alternative of `stable_or_card_le` cannot hold at `M`
  have hcard : (F^[M] [i]).toFinset.card ≤ n := by
    have := Finset.card_le_card (hrange M)
    simpa using this
  rcases stable_or_card_le gs i M with ⟨m, hm, hstab⟩ | hbig
  · -- once a round changes nothing, no later round changes anything
    have hlift : ∀ d k', k' ∈ F^[m + d] [i] ↔ k' ∈ F^[m] [i] := by
      intro d
      induction d with
      | zero => intro k'; rw [Nat.add_zero]
      | succ d ihd =>
          intro k'
          have h1 : F^[m + (d + 1)] [i] = rawOrbitStep (gs, F^[m + d] [i]) := by
            rw [show m + (d + 1) = (m + d) + 1 from rfl, Function.iterate_succ_apply']
          have h2 : F^[m + 1] [i] = rawOrbitStep (gs, F^[m] [i]) := by
            rw [Function.iterate_succ_apply']
          rw [h1, mem_rawOrbitStep_congr gs ihd k', ← h2]
          exact hstab k'
    have hMm : m + (M - m) = M := by omega
    have hMm1 : m + (M + 1 - m) = M + 1 := by omega
    have hkM : k ∈ F^[M] [i] := by rw [rawOrbit_eq_iterate] at hk; exact hk
    have hstepmem : rawApply (g, k) ∈ F^[M + 1] [i] := by
      rw [Function.iterate_succ_apply']
      exact (mem_rawOrbitStep_iff gs (F^[M] [i]) _).2 (Or.inr ⟨k, hkM, g, hg, rfl⟩)
    have h1 : rawApply (g, k) ∈ F^[m] [i] := by
      rw [← hMm1] at hstepmem
      exact (hlift (M + 1 - m) _).1 hstepmem
    have h2 : rawApply (g, k) ∈ F^[M] [i] := by
      rw [← hMm]
      exact (hlift (M - m) _).2 h1
    rw [rawOrbit_eq_iterate]
    exact h2
  · have hbig' : M + 1 ≤ (F^[M] [i]).toFinset.card := hbig
    omega

/-! ## The specification -/

/-- **The specification of `Algo.rawOrbit`.**  On well-formed generators, the entries of the
answer are exactly the orbit of the point under `Algo.decGroup`. -/
theorem mem_rawOrbit_iff {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {i : ℕ} (hi : i < n)
    (k : ℕ) :
    k ∈ rawOrbit (gs, i) ↔
      ∃ h : k < n, (⟨k, h⟩ : Fin n) ∈ MulAction.orbit (decGroup n gs) ⟨i, hi⟩ := by
  classical
  constructor
  · intro hk
    rw [rawOrbit_eq_iterate] at hk
    exact rawOrbitIter_mem_orbit hgs hi _ k hk
  · rintro ⟨hkn, hkorb⟩
    set T : Finset (Fin n) := Finset.univ.filter (fun y : Fin n => (y : ℕ) ∈ rawOrbit (gs, i))
      with hT
    have hmemT : ∀ y : Fin n, y ∈ T ↔ (y : ℕ) ∈ rawOrbit (gs, i) := by
      intro y; rw [hT]; simp
    have hclosed : ∀ σ ∈ gs.map (decPerm n), ∀ y ∈ T, σ y ∈ T := by
      intro σ hσ y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hσ
      have hyorb : (y : ℕ) ∈ rawOrbit (gs, i) := (hmemT y).1 hy
      have happ : rawApply (g, (y : ℕ)) = ((decPerm n g y : Fin n) : ℕ) := by
        have := rawApply_of_wf (hgs g hg) y.isLt
        simpa using this
      rw [hmemT]
      rw [← happ]
      exact rawOrbit_closed hgs hi hyorb hg
    have hiT : (⟨i, hi⟩ : Fin n) ∈ T := (hmemT _).2 (mem_rawOrbit_self gs i)
    obtain ⟨σ, hσ⟩ := hkorb
    have hσmem : (σ : Equiv.Perm (Fin n)) ∈ decGroup n gs := σ.2
    have himg : T.image (σ : Equiv.Perm (Fin n)) = T :=
      image_eq_of_mem_genGroup T (gs.map (decPerm n)) hclosed hσmem
    have hin : (σ : Equiv.Perm (Fin n)) (⟨i, hi⟩ : Fin n) ∈ T := by
      rw [← himg]
      exact Finset.mem_image.2 ⟨⟨i, hi⟩, hiT, rfl⟩
    have hval : (σ : Equiv.Perm (Fin n)) (⟨i, hi⟩ : Fin n) = (⟨k, hkn⟩ : Fin n) := hσ
    rw [hval, hmemT] at hin
    exact hin

/-- **The specification of `Algo.rawOrbit`, as sets.** -/
theorem rawOrbit_spec {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {i : ℕ} (hi : i < n) :
    {k | k ∈ rawOrbit (gs, i)}
      = (fun y : Fin n => (y : ℕ)) '' MulAction.orbit (decGroup n gs) ⟨i, hi⟩ := by
  ext k
  rw [Set.mem_setOf_eq, mem_rawOrbit_iff hgs hi k]
  constructor
  · rintro ⟨hkn, hkorb⟩
    exact ⟨⟨k, hkn⟩, hkorb, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.isLt, by simpa using hy⟩

/-! ## The `PolyFun` statements -/

theorem polyFun_rawOrbitImages : PolyFun rawOrbitImages :=
  (PolyFun.flatMapParam ((polyFun_snd.pair polyFun_fst).comp polyFun_rawImages)).of_eq
    (fun _ => rfl)

theorem polyFun_rawOrbitStep : PolyFun rawOrbitStep :=
  ((polyFun_snd.pair polyFun_rawOrbitImages).comp polyFun_dedupInto).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
/-- **The orbit routine is a `RAM.PolyFun`.**  The accumulator is bounded by
`Algo.rawOrbitIter_struct`: the points added are distinct and all of them are entries of the
generators, so there are at most as many as the flattened generator list is long. -/
theorem polyFun_rawOrbit : PolyFun rawOrbit := by
  have hf : PolyFun (fun z : RawGens × (List ℕ × ℕ) => rawOrbitStep (z.1, z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawOrbitStep
  have hacc : ∀ (cc : RawGens) (x : List ℕ) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => (fun z : RawGens × (List ℕ × ℕ) =>
            rawOrbitStep (z.1, z.2.1)) (cc, (y, a))) x (r.take j))
        ≤ (fun m => 1 + m * (2 * (1 + m * (2 * m + 1)) + 1) + m)
            (Enc.size ((cc, (x, r)) : RawGens × (List ℕ × List ℕ))) := by
    intro cc x r j
    show Enc.size (List.foldl (fun y (_ : ℕ) => rawOrbitStep (cc, y)) x (r.take j)) ≤ _
    rw [foldl_const_eq_iterate]
    obtain ⟨e, he, hnd, _, hmem⟩ := rawOrbitIter_struct cc x (r.take j).length
    rw [he]
    set N := Enc.size ((cc, (x, r)) : RawGens × (List ℕ × List ℕ)) with hN
    have hcc : Enc.size cc ≤ N := Combine.size_fst_le cc ((x, r) : List ℕ × List ℕ)
    have hxr : Enc.size ((x, r) : List ℕ × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : List ℕ × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hflatlen : cc.flatten.length ≤ N :=
      le_trans (length_flatten_le_size cc) hcc
    have hflatsize : Enc.size cc.flatten ≤ 1 + N * (2 * N + 1) := by
      have h1 := size_flatten_le cc
      have h2 : Enc.size cc * (2 * Enc.size cc + 1) ≤ N * (2 * N + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hsub : e ⊆ cc.flatten := fun k hk => hmem k hk
    have hlen : e.length ≤ cc.flatten.length :=
      List.Subperm.length_le (List.subperm_of_subset hnd hsub)
    have hentry : ∀ k ∈ e, Enc.size k ≤ 1 + N * (2 * N + 1) := by
      intro k hk
      have := size_mem_le (hmem k hk)
      omega
    have hsize := size_list_le_of_entries e (1 + N * (2 * N + 1)) hentry
    have hmul : e.length * (2 * (1 + N * (2 * N + 1)) + 1) ≤ N * (2 * (1 + N * (2 * N + 1)) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have happ := size_append_le e x
    dsimp only
    omega
  have hfold := PolyFun.foldlParam hf
    (p := fun m => 1 + m * (2 * (1 + m * (2 * m + 1)) + 1) + m)
    (((polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul ((polyBound_const 1).add (polyBound_id.mul
        (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1))))).add
        (polyBound_const 1)))).add polyBound_id)
    hacc
  have hin : PolyFun (fun p : RawGens × ℕ =>
      ((p.1, (([p.2] : List ℕ), p.1.flatten)) : RawGens × (List ℕ × List ℕ))) :=
    polyFun_fst.pair ((polyFun_snd.comp polyFun_singleton).pair
      (polyFun_fst.comp polyFun_flatten))
  exact (hin.comp hfold).of_eq (fun p => rfl)

/-! ## Transitivity

"Transitive" in this development is the paper's notion, `Babai.IsTransitive`: *exactly one*
orbit, so an action on the empty set is not transitive.  The test therefore rejects the degree
`0` outright, and otherwise compares the orbit of the point `0` with the whole domain.  Testing
one point is enough, because `Babai.isTransitive_iff` says that one orbit is everything exactly
when every orbit is. -/

/-- **The transitivity test.**  The second component is a list over the domain, which is where
the degree `n` is read off; `Algo.rawOne` of `Workspace/Algo/Perm.lean` follows the same
convention, and for the same reason. -/
def rawIsTransitive (p : RawGens × List ℕ) : Bool :=
  if 1 ≤ p.2.length then decide ((rawOrbit (p.1, 0)).length = p.2.length) else false

/-- **The specification of `Algo.rawIsTransitive`**, against the paper's notion of transitivity
(`Babai.IsTransitive`: exactly one orbit). -/
theorem rawIsTransitive_eq_true_iff {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    {w : List ℕ} (hw : w.length = n) :
    rawIsTransitive (gs, w) = true ↔ Babai.IsTransitive (decGroup n gs) := by
  classical
  rw [rawIsTransitive]
  by_cases hn : 1 ≤ n
  · have hpos : 1 ≤ w.length := by omega
    rw [if_pos hpos]
    have h0 : (0 : ℕ) < n := hn
    set L : List ℕ := rawOrbit (gs, 0) with hL
    have hnd : L.Nodup := nodup_rawOrbit gs 0
    have hlt : ∀ k ∈ L, k < n := by
      intro k hk
      obtain ⟨hkn, _⟩ := (mem_rawOrbit_iff hgs h0 k).1 hk
      exact hkn
    -- the entries of `L` fill the domain exactly when its length is `n`
    have hsub : L.toFinset ⊆ Finset.range n := by
      intro a ha
      rw [List.mem_toFinset] at ha
      simpa using hlt a ha
    have hcardL : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
    have hkey : L.length = n ↔ ∀ k < n, k ∈ L := by
      constructor
      · intro hlen
        have hcard : (Finset.range n).card ≤ L.toFinset.card := by
          rw [hcardL, Finset.card_range]; omega
        have heq : L.toFinset = Finset.range n := Finset.eq_of_subset_of_card_le hsub hcard
        intro k hk
        have : k ∈ L.toFinset := by rw [heq]; simpa using hk
        simpa using this
      · intro hall
        have hsup : Finset.range n ⊆ L.toFinset := by
          intro a ha
          rw [List.mem_toFinset]
          exact hall a (by simpa using ha)
        have heq : L.toFinset = Finset.range n :=
          Finset.Subset.antisymm hsub hsup
        rw [← hcardL, heq, Finset.card_range]
    haveI : Nonempty (Fin n) := ⟨⟨0, h0⟩⟩
    rw [hw, decide_eq_true_eq, hkey]
    constructor
    · intro hall
      rw [Babai.isTransitive_iff_orbit_eq_univ]
      intro y
      have horb : MulAction.orbit (decGroup n gs) (⟨0, h0⟩ : Fin n) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro z
        obtain ⟨_, hz⟩ := (mem_rawOrbit_iff hgs h0 (z : ℕ)).1 (hall (z : ℕ) z.isLt)
        simpa using hz
      exact (Babai.isTransitive_iff_orbit_eq_univ (decGroup n gs)).1 ⟨⟨0, h0⟩, horb⟩ y
    · intro htr k hk
      have horb :=
        (Babai.isTransitive_iff_orbit_eq_univ (decGroup n gs)).1 htr (⟨0, h0⟩ : Fin n)
      have hmem : (⟨k, hk⟩ : Fin n) ∈ MulAction.orbit (decGroup n gs) (⟨0, h0⟩ : Fin n) := by
        rw [horb]; trivial
      exact (mem_rawOrbit_iff hgs h0 k).2 ⟨hk, hmem⟩
  · have hn0 : n = 0 := by omega
    subst hn0
    have hw0 : ((gs, w) : RawGens × List ℕ).2.length = 0 := hw
    rw [if_neg (by omega)]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨y, _⟩
      exact absurd y.isLt (by omega)

theorem polyFun_rawIsTransitive : PolyFun rawIsTransitive := by
  have hcond : PolyFun (fun p : RawGens × List ℕ => decide (1 ≤ p.2.length)) :=
    PolyFun.le (polyFun_const 1) (polyFun_snd.comp polyFun_length)
  have hthen : PolyFun (fun p : RawGens × List ℕ =>
      decide ((rawOrbit (p.1, 0)).length = p.2.length)) :=
    PolyFun.natEq
      (((polyFun_fst.pair (polyFun_const 0)).comp polyFun_rawOrbit).comp polyFun_length)
      (polyFun_snd.comp polyFun_length)
  refine (PolyFun.ite hcond hthen (polyFun_const false)).of_eq (fun p => ?_)
  by_cases h : 1 ≤ p.2.length <;> simp [rawIsTransitive, h]

/-! ## Invariance of a window

Def. 11.1.3 calls a window `Δ ⊆ Ω` admissible when it is `G`-invariant.  The test is the same
round as the orbit loop, run once: the window is invariant exactly when no generator sends a
point of the window outside it. -/

/-- **The invariance test for a raw subset.** -/
def rawIsInvariant (p : RawGens × List ℕ) : Bool :=
  ((rawOrbitImages p).filter (fun k => !decide (k ∈ p.2))).isEmpty

/-- What the test says, spelled out on raw data. -/
theorem rawIsInvariant_eq_true_iff' (gs : RawGens) (Δ : List ℕ) :
    rawIsInvariant (gs, Δ) = true ↔ ∀ j ∈ Δ, ∀ g ∈ gs, rawApply (g, j) ∈ Δ := by
  rw [rawIsInvariant]
  simp only [List.isEmpty_iff, List.filter_eq_nil_iff, Bool.not_eq_true', decide_eq_false_iff_not,
    Decidable.not_not]
  constructor
  · intro h j hj g hg
    exact h _ ((mem_rawOrbitImages_iff gs Δ _).2 ⟨j, hj, g, hg, rfl⟩)
  · intro h k hk
    obtain ⟨j, hj, g, hg, rfl⟩ := (mem_rawOrbitImages_iff gs Δ k).1 hk
    exact h j hj g hg

/-- **The specification of `Algo.rawIsInvariant`**, against `Babai.IsInvariant`. -/
theorem rawIsInvariant_eq_true_iff {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    {Δ : List ℕ} (hΔ : ∀ k ∈ Δ, k < n) :
    rawIsInvariant (gs, Δ) = true ↔
      Babai.IsInvariant (decGroup n gs) {y : Fin n | (y : ℕ) ∈ Δ} := by
  classical
  rw [rawIsInvariant_eq_true_iff']
  constructor
  · intro h
    set T : Finset (Fin n) := Finset.univ.filter (fun y : Fin n => (y : ℕ) ∈ Δ) with hT
    have hmemT : ∀ y : Fin n, y ∈ T ↔ (y : ℕ) ∈ Δ := by intro y; rw [hT]; simp
    have hclosed : ∀ σ ∈ gs.map (decPerm n), ∀ y ∈ T, σ y ∈ T := by
      intro σ hσ y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hσ
      have happ : rawApply (g, (y : ℕ)) = ((decPerm n g y : Fin n) : ℕ) := by
        have := rawApply_of_wf (hgs g hg) y.isLt
        simpa using this
      rw [hmemT, ← happ]
      exact h _ ((hmemT y).1 hy) g hg
    rw [Babai.isInvariant_iff_mem]
    intro σ hσ y
    have himg : T.image (σ : Equiv.Perm (Fin n)) = T :=
      image_eq_of_mem_genGroup T (gs.map (decPerm n)) hclosed hσ
    constructor
    · intro hy
      have hyT : y ∈ T := (hmemT y).2 hy
      have : σ y ∈ T := by rw [← himg]; exact Finset.mem_image.2 ⟨y, hyT, rfl⟩
      exact (hmemT _).1 this
    · intro hy
      have hsy : σ y ∈ T := (hmemT _).2 hy
      rw [← himg] at hsy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 hsy
      have : z = y := σ.injective hzy
      exact (hmemT y).1 (this ▸ hz)
  · intro h j hj g hg
    have hjn : j < n := hΔ j hj
    have hσ : decPerm n g ∈ decGroup n gs := decPerm_mem_decGroup hg
    have hmem : (⟨j, hjn⟩ : Fin n) ∈ {y : Fin n | (y : ℕ) ∈ Δ} := hj
    have := (Babai.isInvariant_iff_mem (decGroup n gs) {y : Fin n | (y : ℕ) ∈ Δ}).1 h
      (decPerm n g) hσ ⟨j, hjn⟩
    have himg : (decPerm n g ⟨j, hjn⟩ : Fin n) ∈ {y : Fin n | (y : ℕ) ∈ Δ} := this.1 hmem
    have happ : rawApply (g, j) = ((decPerm n g ⟨j, hjn⟩ : Fin n) : ℕ) :=
      rawApply_of_wf (hgs g hg) hjn
    rw [happ]
    exact himg

theorem polyFun_rawIsInvariant : PolyFun rawIsInvariant := by
  have hq : PolyFun (fun z : List ℕ × ℕ => (!decide (z.2 ∈ z.1) : Bool)) := by
    refine (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
      (polyFun_const false) (polyFun_const true)).of_eq (fun z => ?_)
    by_cases h : z.2 ∈ z.1 <;> simp [h]
  refine (((polyFun_snd.pair polyFun_rawOrbitImages).comp (PolyFun.filterParam hq)).comp
    polyFun_isEmpty).of_eq (fun _ => rfl)

/-! ## The orbit partition

The orbits of `G` are what the Chain Rule (Prop. 11.1.7) and Eq. (64) run over, so the routine
that lists them once each is needed as often as the orbit of a single point.  It is the obvious
loop: walk through the domain, and whenever the point is not yet covered, put its orbit on the
list. -/

/-- One round of the orbit partition: add the orbit of the point, unless it is already
covered. -/
def rawOrbitsStep (p : RawGens × (List (List ℕ) × ℕ)) : List (List ℕ) :=
  if p.2.2 ∈ p.2.1.flatten then p.2.1 else p.2.1 ++ [rawOrbit (p.1, p.2.2)]

/-- **The orbit partition.**  As in `Algo.rawIsTransitive`, the second component is a list over
the domain, from which the degree `n` is read off. -/
def rawOrbits (p : RawGens × List ℕ) : List (List ℕ) :=
  List.foldl (fun acc j => rawOrbitsStep (p.1, (acc, j))) [] (List.range p.2.length)

/-- **The shape of the accumulator along the partition loop**: the orbits found are appended,
one per point of the list at most, and each of them is the orbit of one of those points.  This
is what bounds the accumulator. -/
theorem rawOrbits_fold_struct (cc : RawGens) : ∀ (l : List ℕ) (x : List (List ℕ)),
    ∃ e : List (List ℕ),
      List.foldl (fun y a => rawOrbitsStep (cc, (y, a))) x l = x ++ e ∧
      e.length ≤ l.length ∧ ∀ u ∈ e, ∃ j ∈ l, u = rawOrbit (cc, j) := by
  intro l
  induction l with
  | nil => intro x; exact ⟨[], by simp, by simp, by simp⟩
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      by_cases ha : a ∈ x.flatten
      · have hstep : rawOrbitsStep (cc, (x, a)) = x := by simp [rawOrbitsStep, ha]
        rw [hstep]
        obtain ⟨e, he, hlen, hmem⟩ := ih x
        refine ⟨e, he, by simp; omega, ?_⟩
        intro u hu
        obtain ⟨j, hj, hju⟩ := hmem u hu
        exact ⟨j, List.mem_cons_of_mem a hj, hju⟩
      · have hstep : rawOrbitsStep (cc, (x, a)) = x ++ [rawOrbit (cc, a)] := by
          simp [rawOrbitsStep, ha]
        rw [hstep]
        obtain ⟨e, he, hlen, hmem⟩ := ih (x ++ [rawOrbit (cc, a)])
        refine ⟨rawOrbit (cc, a) :: e, ?_, ?_, ?_⟩
        · rw [he, List.append_assoc]; rfl
        · simp only [List.length_cons, List.length_cons]; omega
        · intro u hu
          rcases List.mem_cons.1 hu with rfl | hu'
          · exact ⟨a, List.mem_cons_self .., rfl⟩
          · obtain ⟨j, hj, hju⟩ := hmem u hu'
            exact ⟨j, List.mem_cons_of_mem a hj, hju⟩

set_option maxHeartbeats 1000000 in
theorem polyFun_rawOrbitsStep : PolyFun rawOrbitsStep := by
  have hcond : PolyFun (fun p : RawGens × (List (List ℕ) × ℕ) =>
      decide (p.2.2 ∈ p.2.1.flatten)) :=
    ((polyFun_snd.comp polyFun_snd).pair
      ((polyFun_snd.comp polyFun_fst).comp polyFun_flatten)).comp polyFun_natListMem
  have helse : PolyFun (fun p : RawGens × (List (List ℕ) × ℕ) =>
      p.2.1 ++ [rawOrbit (p.1, p.2.2)]) :=
    ((polyFun_snd.comp polyFun_fst).pair
      (((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawOrbit).comp
        polyFun_singleton)).comp polyFun_append
  refine (PolyFun.ite hcond (polyFun_snd.comp polyFun_fst) helse).of_eq (fun p => ?_)
  by_cases h : p.2.2 ∈ p.2.1.flatten <;> simp [rawOrbitsStep, h]

set_option maxHeartbeats 1000000 in
/-- **The orbit partition is a `RAM.PolyFun`.** -/
theorem polyFun_rawOrbits : PolyFun rawOrbits := by
  obtain ⟨c, d, hc⟩ := polyFun_rawOrbit.size
  have hMb : PolyBound (fun m => c * (4 * m + 1) ^ d) :=
    (polyBound_witness c d).comp ((polyBound_const 4).mul polyBound_id)
  have hacc : ∀ (cc : RawGens) (x : List (List ℕ)) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawOrbitsStep (cc, (y, a))) x (r.take j))
        ≤ (fun m => m + (1 + m * (2 * (c * (4 * m + 1) ^ d) + 1)))
            (Enc.size ((cc, (x, r)) : RawGens × (List (List ℕ) × List ℕ))) := by
    intro cc x r j
    obtain ⟨e, he, hlen, hmem⟩ := rawOrbits_fold_struct cc (r.take j) x
    rw [he]
    set N := Enc.size ((cc, (x, r)) : RawGens × (List (List ℕ) × List ℕ)) with hN
    have hcc : Enc.size cc ≤ N := Combine.size_fst_le cc ((x, r) : List (List ℕ) × List ℕ)
    have hxr : Enc.size ((x, r) : List (List ℕ) × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : List (List ℕ) × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hr : Enc.size r ≤ N := le_trans (Combine.size_snd_le x r) hxr
    have hentry : ∀ u ∈ e, Enc.size u ≤ c * (4 * N + 1) ^ d := by
      intro u hu
      obtain ⟨jj, hjj, rfl⟩ := hmem u hu
      have hj1 : Enc.size jj ≤ Enc.size (r.take j) := size_mem_le hjj
      have hj2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
      have hpair : Enc.size ((cc, jj) : RawGens × ℕ) ≤ 2 * Enc.size cc + 2 * Enc.size jj :=
        Combine.size_pair_le _ _
      have h4 := hc ((cc, jj) : RawGens × ℕ)
      have h5 : (Enc.size ((cc, jj) : RawGens × ℕ) + 1) ^ d ≤ (4 * N + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h6 := Nat.mul_le_mul_left c h5
      omega
    have hsize := size_list_le_of_entries e (c * (4 * N + 1) ^ d) hentry
    have hlen2 : e.length ≤ N := by
      have h1 : (r.take j).length ≤ r.length := by
        rw [List.length_take]; exact min_le_right _ _
      have h2 : r.length ≤ Enc.size r := length_le_size r
      omega
    have hmul : e.length * (2 * (c * (4 * N + 1) ^ d) + 1)
        ≤ N * (2 * (c * (4 * N + 1) ^ d) + 1) := Nat.mul_le_mul_right _ hlen2
    have happ := size_append_le x e
    dsimp only
    omega
  have hfold := PolyFun.foldlParam polyFun_rawOrbitsStep
    (p := fun m => m + (1 + m * (2 * (c * (4 * m + 1) ^ d) + 1)))
    (polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul hMb).add (polyBound_const 1)))))
    hacc
  have hin : PolyFun (fun p : RawGens × List ℕ =>
      ((p.1, (([] : List (List ℕ)), List.range p.2.length)) :
        RawGens × (List (List ℕ) × List ℕ))) :=
    polyFun_fst.pair (polyFun_nil.pair (polyFun_snd.comp polyFun_rangeLength))
  exact (hin.comp hfold).of_eq (fun p => rfl)

/-! ### What the partition is

Two orbits that meet are the same orbit, so a point that is not yet covered starts a genuinely
new one.  That is the only group-theoretic input; everything else is the induction along the
fold. -/

/-- Two orbits that share a point are the same orbit. -/
theorem mem_rawOrbit_of_mem_mem {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {a b : ℕ}
    (ha : a < n) (hb : b < n) {k : ℕ} (hka : k ∈ rawOrbit (gs, a))
    (hkb : k ∈ rawOrbit (gs, b)) : a ∈ rawOrbit (gs, b) := by
  obtain ⟨hkn, hkorba⟩ := (mem_rawOrbit_iff hgs ha k).1 hka
  obtain ⟨hkn', hkorbb⟩ := (mem_rawOrbit_iff hgs hb k).1 hkb
  have h1 : MulAction.orbit (decGroup n gs) (⟨k, hkn⟩ : Fin n)
      = MulAction.orbit (decGroup n gs) (⟨a, ha⟩ : Fin n) := MulAction.orbit_eq_iff.2 hkorba
  have h2 : MulAction.orbit (decGroup n gs) (⟨k, hkn'⟩ : Fin n)
      = MulAction.orbit (decGroup n gs) (⟨b, hb⟩ : Fin n) := MulAction.orbit_eq_iff.2 hkorbb
  have hkk : (⟨k, hkn⟩ : Fin n) = (⟨k, hkn'⟩ : Fin n) := rfl
  have h3 : MulAction.orbit (decGroup n gs) (⟨a, ha⟩ : Fin n)
      = MulAction.orbit (decGroup n gs) (⟨b, hb⟩ : Fin n) := by
    rw [← h1, hkk, h2]
  exact (mem_rawOrbit_iff hgs hb a).2 ⟨ha, MulAction.orbit_eq_iff.1 h3⟩

/-- **The invariant of the partition loop.**  Everything on the list is an orbit of a point of
the domain, no two entries meet, the list only grows, and every point the loop has walked past
is covered. -/
theorem rawOrbits_fold_inv {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) :
    ∀ (l : List ℕ), (∀ j ∈ l, j < n) → ∀ (x : List (List ℕ)),
      (∀ u ∈ x, ∃ j, j < n ∧ u = rawOrbit (gs, j)) →
      x.Pairwise (fun u v => ∀ k, k ∈ u → k ∉ v) →
      (∀ u ∈ List.foldl (fun y a => rawOrbitsStep (gs, (y, a))) x l,
          ∃ j, j < n ∧ u = rawOrbit (gs, j)) ∧
        (List.foldl (fun y a => rawOrbitsStep (gs, (y, a))) x l).Pairwise
          (fun u v => ∀ k, k ∈ u → k ∉ v) ∧
        (∀ k ∈ x.flatten,
          k ∈ (List.foldl (fun y a => rawOrbitsStep (gs, (y, a))) x l).flatten) ∧
        (∀ j ∈ l, j ∈ (List.foldl (fun y a => rawOrbitsStep (gs, (y, a))) x l).flatten) := by
  intro l
  induction l with
  | nil =>
      intro _ x hx hp
      exact ⟨hx, hp, fun k hk => hk, by simp⟩
  | cons a t ih =>
      intro hlt x hx hp
      have hat : ∀ j ∈ t, j < n := fun j hj => hlt j (List.mem_cons_of_mem a hj)
      have han : a < n := hlt a (List.mem_cons_self ..)
      rw [List.foldl_cons]
      by_cases ha : a ∈ x.flatten
      · have hstep : rawOrbitsStep (gs, (x, a)) = x := by simp [rawOrbitsStep, ha]
        rw [hstep]
        obtain ⟨h1, h2, h3, h4⟩ := ih hat x hx hp
        refine ⟨h1, h2, h3, ?_⟩
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · exact h3 j ha
        · exact h4 j hj'
      · have hstep : rawOrbitsStep (gs, (x, a)) = x ++ [rawOrbit (gs, a)] := by
          simp [rawOrbitsStep, ha]
        rw [hstep]
        have hx' : ∀ u ∈ x ++ [rawOrbit (gs, a)], ∃ j, j < n ∧ u = rawOrbit (gs, j) := by
          intro u hu
          rcases List.mem_append.1 hu with hu1 | hu1
          · exact hx u hu1
          · rw [List.mem_singleton] at hu1
            exact ⟨a, han, hu1⟩
        have hdisj : ∀ u ∈ x, ∀ v ∈ [rawOrbit (gs, a)], ∀ k, k ∈ u → k ∉ v := by
          intro u hu v hv k hku hkv
          rw [List.mem_singleton] at hv
          subst hv
          obtain ⟨b, hbn, rfl⟩ := hx u hu
          have : a ∈ rawOrbit (gs, b) := mem_rawOrbit_of_mem_mem hgs han hbn hkv hku
          exact ha (List.mem_flatten.2 ⟨rawOrbit (gs, b), hu, this⟩)
        have hp' : (x ++ [rawOrbit (gs, a)]).Pairwise (fun u v => ∀ k, k ∈ u → k ∉ v) := by
          rw [List.pairwise_append]
          exact ⟨hp, List.pairwise_singleton _ _, hdisj⟩
        obtain ⟨h1, h2, h3, h4⟩ := ih hat (x ++ [rawOrbit (gs, a)]) hx' hp'
        have hmono : ∀ k ∈ x.flatten, k ∈ (x ++ [rawOrbit (gs, a)]).flatten := by
          intro k hk
          rw [List.flatten_append]
          exact List.mem_append_left _ hk
        refine ⟨h1, h2, fun k hk => h3 k (hmono k hk), ?_⟩
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · refine h3 j ?_
          rw [List.flatten_append]
          exact List.mem_append_right _ (by simpa using mem_rawOrbit_self gs j)
        · exact h4 j hj'

/-- **Every entry of `Algo.rawOrbits` is the orbit of a point of the domain.** -/
theorem rawOrbits_mem {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {w : List ℕ}
    (hw : w.length = n) {u : List ℕ} (hu : u ∈ rawOrbits (gs, w)) :
    ∃ j, j < n ∧ u = rawOrbit (gs, j) := by
  have h := rawOrbits_fold_inv hgs (List.range w.length)
    (fun j hj => by rw [← hw]; simpa using hj) [] (by simp) (by simp)
  exact h.1 u hu

/-- **No two entries of `Algo.rawOrbits` meet**: each orbit is listed once. -/
theorem rawOrbits_pairwise {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {w : List ℕ}
    (hw : w.length = n) :
    (rawOrbits (gs, w)).Pairwise (fun u v => ∀ k, k ∈ u → k ∉ v) :=
  (rawOrbits_fold_inv hgs (List.range w.length)
    (fun j hj => by rw [← hw]; simpa using hj) [] (by simp) (by simp)).2.1

/-- **Every point of the domain is covered.** -/
theorem rawOrbits_cover {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {w : List ℕ}
    (hw : w.length = n) {j : ℕ} (hj : j < n) : j ∈ (rawOrbits (gs, w)).flatten :=
  (rawOrbits_fold_inv hgs (List.range w.length)
    (fun j hj => by rw [← hw]; simpa using hj) [] (by simp) (by simp)).2.2.2 j
      (by simpa using (by omega : j < w.length))

/-- **The specification of `Algo.rawOrbits`.**  Every entry is, as a set of points, an orbit of
`Algo.decGroup`. -/
theorem rawOrbits_spec {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) {w : List ℕ}
    (hw : w.length = n) {u : List ℕ} (hu : u ∈ rawOrbits (gs, w)) :
    ∃ (j : ℕ) (hj : j < n),
      {k | k ∈ u} = (fun y : Fin n => (y : ℕ)) '' MulAction.orbit (decGroup n gs) ⟨j, hj⟩ := by
  obtain ⟨j, hj, rfl⟩ := rawOrbits_mem hgs hw hu
  exact ⟨j, hj, rawOrbit_spec hgs hj⟩

end Algo
