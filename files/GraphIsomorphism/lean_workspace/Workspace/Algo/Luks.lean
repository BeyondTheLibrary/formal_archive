/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Luks's Chain Rule over the orbits, as a computable round.
-/
import Workspace.Algo.Coset
import Workspace.Machine.ListOps4
import Workspace.Algo.Round
import Workspace.Luks.Framework

/-!
# The Chain Rule round (§15, line 1 step 3; §11.1, Prop. 11.1.7 and Eq. (64))

Proposition 11.1.7 (Chain Rule) says that the window isomorphisms for `Δ₁ ∪ Δ₂` are the
window isomorphisms for `Δ₂` of the *answer* for `Δ₁`:

> `Iso^{Δ₁ ∪ Δ₂}_G(x,y) = Iso^{Δ₂}_{G₁σ}(x,y) = Iso^{Δ₂}_{G₁}(x, y^{σ⁻¹})σ`,  (63)

where `Iso^{Δ₁}_G(x,y) = G₁σ`.  Eq. (64) applies it to the orbits of `G`: the window is cut
into the orbits and they are processed one after the other.  This file writes that round as
an `Algo.Round` and proves the `Algo.Implements` link.

## The first form of Eq. (63), not the second

The round uses the *middle* term of Eq. (63), `Iso^{Δ₂}_{G₁σ}(x,y)`: the candidate set of
the child is the **coset** the parent has reached, and the strings are not shifted.  This is
what `Babai.SIInstance` allows (`Def. 11.1.2`: the candidate set is "a group or a coset"),
and the chain is then simply

`C₀ = G`,  `C_{j+1} = Iso^{Δ_j}_{C_j}(x,y)`,  answer `C_k`   (`Algo.cosetChain`).

The reason is not taste.  `Algo.Implements` asks the raw round to walk the *same* tree for
**every** raw answer that decodes to the true answer of a child (`Algo.LoopMatch.call`).
With the second form of Eq. (63) the next instance is `⟨G₁, Δ_{j+1}, x, y^{σ⁻¹}⟩`, which
depends on the *representative* `σ` and not only on the coset `G₁σ`; two raw answers
encoding the same coset with different representatives would give different instances, and no
reduction `Set (Perm Ω) → SIReduction` could match both.  With the first form the child
instance is `⟨C_j, Δ_j, x, y⟩`, a function of the coset alone, and the match goes through.
The two forms are the same statement, Eq. (63) itself.

A raw instance therefore carries the coset in the paper's own shape — generators of the group
and one representative — and decodes to `σ • G` (`Algo.decWinSI`).

## The round is a branch, so it takes the rest of the procedure as a parameter

The Chain Rule is applied at line 1 step 3 of Sec. 15 *when `G` is intransitive on the
window*.  With one orbit it would call itself on the same window, so the round stops
(`Algo.winChild` returns `none`) and hands the instance to `solve`, the parameter standing
for the rest of Procedure String-Isomorphism.  This is the shape of `Algo.leafRound`, whose
answer function is a parameter in the same way.

## Main definitions

* `Algo.RawWinSI`, `Algo.decWinSI`, `Algo.WinWF` — raw instances of String Isomorphism with a
  window, their decoding as `Babai.SIInstance (Fin n) ℕ`, and their well-formedness;
* `Algo.normPerm`, `Algo.normGens` — the sanitizers: a raw permutation is capped and, if it is
  still not a permutation, replaced by the identity, which changes nothing after decoding;
* `Algo.winOrbits` — the orbits of the group inside the window, Eq. (64);
* `Algo.cosetChain` — the mathematical round, Eq. (63) iterated;
* `Algo.chainRound` — the computable round.

## Main results

* `Algo.run_cosetChain` — Eq. (63) iterated: the chain computes `Iso^{⋃Δ_j}_C(x,y)`;
* `Algo.implements_chainRound` — **the link**: the raw round walks the tree of `cosetChain`;
* `Algo.run_chainRoundReduction` — the tree computes the answer of the instance, so
  `Algo.roundValue_eq` applies.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## Strings with letters in `ℕ`

The raw layer stores a letter as a natural, so the typed strings of this file are
`Fin n → ℕ`; `Babai.strAct` and `Babai.wIso` are stated for an arbitrary alphabet. -/

/-- The string a raw string describes. -/
def decStrN (n : ℕ) (l : RawStr) : Fin n → ℕ := fun i => l.getD (i : ℕ) 0

/-- The raw form of a string with letters in `ℕ`. -/
def encStrN {n : ℕ} (f : Fin n → ℕ) : RawStr := List.ofFn f

@[simp] theorem length_encStrN {n : ℕ} (f : Fin n → ℕ) : (encStrN f).length = n := by
  simp [encStrN]

@[simp] theorem decStrN_encStrN {n : ℕ} (f : Fin n → ℕ) : decStrN n (encStrN f) = f := by
  funext i
  rw [decStrN, encStrN, List.getD_eq_getElem _ _ (by simp [i.isLt])]
  simp

theorem encStrN_decStrN {l : RawStr} (h : l.length = n) : encStrN (decStrN n l) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp only [encStrN, List.getElem_ofFn, decStrN]
    rw [List.getD_eq_getElem _ _ hi']

/-- **The specification of `Algo.rawStrAct`** for strings with letters in `ℕ`, against
`Babai.strAct` (Eq. (55)). -/
theorem rawStrAct_encStrN {n : ℕ} (σ : Perm (Fin n)) (f : Fin n → ℕ) :
    rawStrAct (encPerm n σ, encStrN f) = encStrN (Babai.strAct f σ) := by
  have h0 : rawStrAct (encPerm n σ, encStrN f)
      = (encPerm n σ⁻¹).map (fun i => rawGet (encStrN f, i)) := by
    show (rawInv (encPerm n σ)).map _ = _
    rw [rawInv_encPerm]
  rw [h0, encPerm, List.map_ofFn, encStrN]
  refine congrArg List.ofFn (funext fun i => ?_)
  show rawGet (encStrN f, ((σ⁻¹ i : Fin n) : ℕ)) = Babai.strAct f σ i
  have hlt : ((σ⁻¹ i : Fin n) : ℕ) < (encStrN f).length := by
    rw [length_encStrN]; exact (σ⁻¹ i).isLt
  rw [rawGet, List.getD_eq_getElem _ _ hlt]
  simp [encStrN, Babai.strAct]

/-! ## Sanitizing a raw permutation

A round is a total function, so `Algo.winChild` receives an arbitrary raw state and must
still produce a well-formed instance.  `Algo.normPerm` does that **without changing the
decoded permutation**, which is what makes the link to the mathematical layer work for every
raw answer, well formed or not.

The two steps are: cap the list to `n` entries, each capped below `n` — this is exactly
`Algo.rawFun`, so the decoding does not move — and then, if the result is still not a
permutation, replace it by the identity, which is what `Algo.decPerm` decodes a
non-permutation to anyway. -/

/-- The raw list capped to the shape of a permutation of `[0, n)`: `n` entries, each below
`n`.  It has the same `Algo.rawFun`, hence the same decoding. -/
def capPerm (p : RawStr × RawPerm) : RawPerm :=
  (rawOne p.1).map (fun i => min (rawGet (p.2, i)) (p.1.length - 1))

/-- **The sanitizer**: a well-formed raw permutation with the same decoding. -/
def normPerm (p : RawStr × RawPerm) : RawPerm :=
  if rawIsPerm (capPerm p) then capPerm p else rawOne p.1

theorem capPerm_eq_ofFn (p : RawStr × RawPerm) :
    capPerm p = List.ofFn (fun i : Fin p.1.length =>
      min (rawGet (p.2, (i : ℕ))) (p.1.length - 1)) := by
  rw [capPerm, rawOne_eq, encPerm, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  simp

@[simp] theorem length_capPerm (p : RawStr × RawPerm) : (capPerm p).length = p.1.length := by
  rw [capPerm_eq_ofFn, List.length_ofFn]

theorem mem_capPerm {p : RawStr × RawPerm} {a : ℕ} (h : a ∈ capPerm p) :
    a ≤ p.1.length - 1 := by
  rw [capPerm_eq_ofFn, List.mem_ofFn'] at h
  obtain ⟨i, rfl⟩ := h
  exact min_le_right _ _

theorem getD_capPerm (p : RawStr × RawPerm) {i : ℕ} (hi : i < p.1.length) :
    (capPerm p).getD i 0 = min (rawGet (p.2, i)) (p.1.length - 1) := by
  rw [capPerm_eq_ofFn, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- The value of `Algo.rawFun` needs only the length and the entry bound, not `Nodup`. -/
theorem rawFun_val_of_bounds {l : RawPerm} (hlen : l.length = n) (hb : ∀ a ∈ l, a < n)
    (i : Fin n) : (rawFun n l i : ℕ) = l[(i : ℕ)]'(by rw [hlen]; exact i.isLt) := by
  have hi : (i : ℕ) < l.length := by rw [hlen]; exact i.isLt
  have h1 : l.getD (i : ℕ) 0 = l[(i : ℕ)] := List.getD_eq_getElem _ _ hi
  have h2 : l[(i : ℕ)] < n := hb _ (List.getElem_mem hi)
  simp only [rawFun, h1]
  omega

theorem rawFun_capPerm {x : RawStr} (hx : x.length = n) (l : RawPerm) :
    rawFun n (capPerm (x, l)) = rawFun n l := by
  funext i
  have hi : (i : ℕ) < x.length := by rw [hx]; exact i.isLt
  have hget : (capPerm (x, l)).getD (i : ℕ) 0 = min (l.getD (i : ℕ) 0) (n - 1) := by
    have h0 := getD_capPerm (x, l) hi
    simp only [hx] at h0
    exact h0
  apply Fin.ext
  show min ((capPerm (x, l)).getD (i : ℕ) 0) (n - 1) = min (l.getD (i : ℕ) 0) (n - 1)
  rw [hget]
  omega

theorem decPerm_capPerm {x : RawStr} (hx : x.length = n) (l : RawPerm) :
    decPerm n (capPerm (x, l)) = decPerm n l := by
  classical
  rw [decPerm, decPerm, rawFun_capPerm hx l]

/-- The capped list is a permutation exactly when the raw list decodes to a permutation. -/
theorem rawIsPerm_capPerm_of_bijective {x : RawStr} (hx : x.length = n) {l : RawPerm}
    (hb : Function.Bijective (rawFun n l)) : rawIsPerm (capPerm (x, l)) = true := by
  have hlen : (capPerm (x, l)).length = n := by rw [length_capPerm, hx]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : capPerm (x, l) = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [hlen, hn]
    rw [this]; rfl
  have hbd : ∀ a ∈ capPerm (x, l), a < n := by
    intro a ha
    have := mem_capPerm ha
    simp only at this
    omega
  have hbij : Function.Bijective (rawFun n (capPerm (x, l))) := by
    rw [rawFun_capPerm hx l]; exact hb
  rw [rawIsPerm_eq_true_iff, hlen]
  refine ⟨hlen, hbd, ?_⟩
  refine List.pairwise_iff_getElem.2 ?_
  intro a b ha hb' hab hcon
  have ha' : a < n := by rw [hlen] at ha; exact ha
  have hb'' : b < n := by rw [hlen] at hb'; exact hb'
  have heq : rawFun n (capPerm (x, l)) ⟨a, ha'⟩ = rawFun n (capPerm (x, l)) ⟨b, hb''⟩ := by
    apply Fin.ext
    rw [rawFun_val_of_bounds hlen hbd ⟨a, ha'⟩, rawFun_val_of_bounds hlen hbd ⟨b, hb''⟩]
    exact hcon
  have := hbij.injective heq
  have : a = b := congrArg Fin.val this
  omega

/-- **The sanitizer does not change the decoding.** -/
theorem decPerm_normPerm {x : RawStr} (hx : x.length = n) (l : RawPerm) :
    decPerm n (normPerm (x, l)) = decPerm n l := by
  classical
  rw [normPerm]
  by_cases h : rawIsPerm (capPerm (x, l))
  · rw [if_pos h, decPerm_capPerm hx l]
  · rw [if_neg h]
    have hnb : ¬ Function.Bijective (rawFun n l) := fun hb =>
      h (rawIsPerm_capPerm_of_bijective hx hb)
    show decPerm n (rawOne x) = decPerm n l
    rw [rawOne_eq, hx, decPerm_encPerm, decPerm, dif_neg hnb]

/-- **The sanitizer produces a well-formed raw permutation.** -/
theorem wf_normPerm {x : RawStr} (hx : x.length = n) (l : RawPerm) :
    RawPerm.WF n (normPerm (x, l)) := by
  rw [normPerm]
  by_cases h : rawIsPerm (capPerm (x, l))
  · rw [if_pos h]
    have := (rawIsPerm_eq_true_iff _).1 h
    rwa [length_capPerm, hx] at this
  · rw [if_neg h]
    have := wf_rawOne x
    rwa [hx] at this

/-- The sanitizer on a list of generators. -/
def normGens (p : RawStr × RawGens) : RawGens := p.2.map (fun g => normPerm (p.1, g))

theorem wf_normGens {x : RawStr} (hx : x.length = n) (gs : RawGens) :
    RawGens.WF n (normGens (x, gs)) := by
  intro g hg
  obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
  exact wf_normPerm hx g'

theorem decGroup_normGens {x : RawStr} (hx : x.length = n) (gs : RawGens) :
    decGroup n (normGens (x, gs)) = decGroup n gs := by
  rw [decGroup, decGroup, normGens, List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro g _
  exact decPerm_normPerm hx g

/-! ## Shortening a sanitized generating list

`Algo.rawShorten` is stated for encoded generators; on well-formed raw generators it is the
same statement, because a well-formed list *is* an encoded list. -/

theorem map_encPerm_decPerm {gs : RawGens} (h : RawGens.WF n gs) :
    (gs.map (decPerm n)).map (encPerm n) = gs := by
  rw [List.map_map]
  refine List.map_congr_left ?_ |>.trans (List.map_id _)
  intro g hg
  exact encPerm_decPerm (h g hg)

theorem rawShorten_wf {x : RawStr} (hx : x.length = n) {gs : RawGens}
    (hgs : RawGens.WF n gs) : RawGens.WF n (rawShorten (x, gs)) := by
  have hrw : rawShorten (x, gs)
      = (entriesList (buildTable n (gs.map (decPerm n)))).map (encPerm n) := by
    conv_lhs => rw [← map_encPerm_decPerm hgs]
    rw [rawShorten, rawBuildTable_spec x hx (gs.map (decPerm n)), rawEntries_encMTable]
  rw [hrw]
  exact wf_map_encPerm n _

theorem length_rawShorten_wf {x : RawStr} (hx : x.length = n) {gs : RawGens}
    (hgs : RawGens.WF n gs) : (rawShorten (x, gs)).length ≤ n * n := by
  conv_lhs => rw [← map_encPerm_decPerm hgs]
  exact length_rawShorten_le x hx (gs.map (decPerm n))

theorem decGroup_rawShorten_wf {x : RawStr} (hx : x.length = n) {gs : RawGens}
    (hgs : RawGens.WF n gs) : decGroup n (rawShorten (x, gs)) = decGroup n gs := by
  conv_lhs => rw [← map_encPerm_decPerm hgs]
  rw [decGroup_rawShorten x hx (gs.map (decPerm n))]
  rfl

/-- The sanitize-and-shorten step used by the round: a well-formed generating list of at most
`n²` entries generating the same group. -/
def tidyGens (p : RawStr × RawGens) : RawGens := rawShorten (p.1, normGens p)

theorem wf_tidyGens {x : RawStr} (hx : x.length = n) (gs : RawGens) :
    RawGens.WF n (tidyGens (x, gs)) := rawShorten_wf hx (wf_normGens hx gs)

theorem length_tidyGens {x : RawStr} (hx : x.length = n) (gs : RawGens) :
    (tidyGens (x, gs)).length ≤ n * n := length_rawShorten_wf hx (wf_normGens hx gs)

theorem decGroup_tidyGens {x : RawStr} (hx : x.length = n) (gs : RawGens) :
    decGroup n (tidyGens (x, gs)) = decGroup n gs := by
  rw [tidyGens, decGroup_rawShorten_wf hx (wf_normGens hx gs), decGroup_normGens hx]

/-! ## Raw instances with a window -/

/-- A raw instance of String Isomorphism with a window: the window `Δ` as a repetition-free
list of points, generators of a group `G`, a representative `σ`, and the two strings.  Its
candidate set is the coset `G σ` of Def. 11.1.2, which is `σ • G` in Lean. -/
abbrev RawWinSI := List ℕ × RawGens × RawPerm × RawStr × RawStr

/-- The instance a raw instance describes.  Paper: Definition 11.1.2 (String Isomorphism). -/
noncomputable def decWinSI (n : ℕ) (I : RawWinSI) : Babai.SIInstance (Fin n) ℕ where
  K := decCoset n (some (I.2.1, I.2.2.1))
  Δ := winSet n I.1
  x := decStrN n I.2.2.2.1
  y := decStrN n I.2.2.2.2

theorem decCoset_some (n : ℕ) (a : RawGens) (σ : RawPerm) :
    decCoset n (some (a, σ)) = decPerm n σ • (decGroup n a : Set (Perm (Fin n))) := by
  ext τ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

/-- **Well-formed raw instances.**  The round is a total function; nothing is claimed off
this predicate. -/
def WinWF (n : ℕ) (I : RawWinSI) : Prop :=
  I.2.2.2.1.length = n ∧ I.2.2.2.2.length = n ∧
    I.1.Nodup ∧ (∀ u ∈ I.1, u < n) ∧
    RawGens.WF n I.2.1 ∧ I.2.1.length ≤ n * n ∧
    RawPerm.WF n I.2.2.1 ∧ rawIsInvariant (I.2.1, I.1) = true

/-! ## The orbits inside the window, Eq. (64)

`Algo.rawOrbits` walks the whole domain; here the loop walks the window instead, so what it
lists is the orbit partition of the window.  All its invariants are the ones of
`Algo.rawOrbits_fold_inv`, which is already stated for an arbitrary list of points. -/

/-- **The orbits of the group inside the window**, Eq. (64). -/
def winOrbits (p : RawGens × List ℕ) : List (List ℕ) :=
  List.foldl (fun acc j => rawOrbitsStep (p.1, (acc, j))) [] p.2

/-- Every orbit listed is the orbit of a point of the window. -/
theorem winOrbits_mem {gs : RawGens} {Δ : List ℕ} {u : List ℕ} (hu : u ∈ winOrbits (gs, Δ)) :
    ∃ j ∈ Δ, u = rawOrbit (gs, j) := by
  obtain ⟨e, he, -, hmem⟩ := rawOrbits_fold_struct gs Δ []
  rw [winOrbits, he] at hu
  simp only [List.nil_append] at hu
  exact hmem u hu

theorem winOrbits_pairwise {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hΔ : ∀ j ∈ Δ, j < n) :
    (winOrbits (gs, Δ)).Pairwise (fun u v => ∀ k, k ∈ u → k ∉ v) :=
  (rawOrbits_fold_inv hgs Δ hΔ [] (by simp) (by simp)).2.1

theorem winOrbits_cover {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hΔ : ∀ j ∈ Δ, j < n) {j : ℕ} (hj : j ∈ Δ) : j ∈ (winOrbits (gs, Δ)).flatten :=
  (rawOrbits_fold_inv hgs Δ hΔ [] (by simp) (by simp)).2.2.2 j hj

/-- An orbit inside the window stays inside the window, because the window is invariant. -/
theorem winOrbits_subset {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hΔ : ∀ j ∈ Δ, j < n) (hinv : rawIsInvariant (gs, Δ) = true) {u : List ℕ}
    (hu : u ∈ winOrbits (gs, Δ)) : ∀ k ∈ u, k ∈ Δ := by
  obtain ⟨j, hj, rfl⟩ := winOrbits_mem hu
  intro k hk
  have hjn : j < n := hΔ j hj
  obtain ⟨hkn, hkorb⟩ := (mem_rawOrbit_iff hgs hjn k).1 hk
  have hI := (rawIsInvariant_eq_true_iff hgs hΔ).1 hinv
  have hmemj : (⟨j, hjn⟩ : Fin n) ∈ {y : Fin n | (y : ℕ) ∈ Δ} := hj
  obtain ⟨g, hg⟩ := hkorb
  have := (Babai.isInvariant_iff_mem (decGroup n gs) {y : Fin n | (y : ℕ) ∈ Δ}).1 hI
    (g : Perm (Fin n)) g.2 ⟨j, hjn⟩
  have hgj : (g : Perm (Fin n)) (⟨j, hjn⟩ : Fin n) = (⟨k, hkn⟩ : Fin n) := hg
  have : (⟨k, hkn⟩ : Fin n) ∈ {y : Fin n | (y : ℕ) ∈ Δ} := by rw [← hgj]; exact this.1 hmemj
  exact this

theorem winOrbits_lt {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hΔ : ∀ j ∈ Δ, j < n) (hinv : rawIsInvariant (gs, Δ) = true) {u : List ℕ}
    (hu : u ∈ winOrbits (gs, Δ)) : ∀ k ∈ u, k < n :=
  fun k hk => hΔ k (winOrbits_subset hgs hΔ hinv hu k hk)

theorem winOrbits_nodup {gs : RawGens} {Δ : List ℕ} {u : List ℕ}
    (hu : u ∈ winOrbits (gs, Δ)) : u.Nodup := by
  obtain ⟨j, -, rfl⟩ := winOrbits_mem hu
  exact nodup_rawOrbit gs j

theorem winOrbits_ne_nil {gs : RawGens} {Δ : List ℕ} {u : List ℕ}
    (hu : u ∈ winOrbits (gs, Δ)) : u ≠ [] := by
  obtain ⟨j, -, rfl⟩ := winOrbits_mem hu
  intro hc
  have := mem_rawOrbit_self gs j
  rw [hc] at this
  simp at this

/-- **An orbit is a proper part of the window** as soon as there are at least two of them.
This is the progress of the Chain Rule round: Eq. (64) cuts the window strictly. -/
theorem winOrbits_length_lt {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hnd : Δ.Nodup) (hΔ : ∀ j ∈ Δ, j < n) (hinv : rawIsInvariant (gs, Δ) = true)
    {j : ℕ} (hj : j < (winOrbits (gs, Δ)).length) (h2 : 1 < (winOrbits (gs, Δ)).length) :
    ((winOrbits (gs, Δ))[j]'hj).length < Δ.length := by
  classical
  obtain ⟨i, hi, hij⟩ : ∃ i, i < (winOrbits (gs, Δ)).length ∧ i ≠ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  have hpw := List.pairwise_iff_getElem.1 (winOrbits_pairwise hgs hΔ (Δ := Δ))
  have hdisj : ∀ k ∈ (winOrbits (gs, Δ))[i]'hi, k ∉ (winOrbits (gs, Δ))[j]'hj := by
    rcases lt_trichotomy i j with h | h | h
    · exact fun k hk => hpw i j hi hj h k hk
    · exact absurd h hij
    · intro k hk hk'
      exact hpw j i hj hi h k hk' hk
  obtain ⟨a, ha⟩ : ∃ a, a ∈ (winOrbits (gs, Δ))[i]'hi := by
    rcases hne : (winOrbits (gs, Δ))[i]'hi with _ | ⟨a, t⟩
    · exact absurd hne (winOrbits_ne_nil (List.getElem_mem hi))
    · exact ⟨a, List.mem_cons_self⟩
  have haΔ : a ∈ Δ := winOrbits_subset hgs hΔ hinv (List.getElem_mem hi) a ha
  have hanot : a ∉ (winOrbits (gs, Δ))[j]'hj := hdisj a ha
  have hsub : ∀ k ∈ (winOrbits (gs, Δ))[j]'hj, k ∈ Δ :=
    winOrbits_subset hgs hΔ hinv (List.getElem_mem hj)
  have hjnd : ((winOrbits (gs, Δ))[j]'hj).Nodup := winOrbits_nodup (List.getElem_mem hj)
  have hins : insert a ((winOrbits (gs, Δ))[j]'hj).toFinset ⊆ Δ.toFinset := by
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb'
    · simpa using haΔ
    · exact List.mem_toFinset.2 (hsub b (List.mem_toFinset.1 hb'))
  have h1 : (((winOrbits (gs, Δ))[j]'hj).toFinset).card = ((winOrbits (gs, Δ))[j]'hj).length :=
    List.toFinset_card_of_nodup hjnd
  have h2' : (insert a ((winOrbits (gs, Δ))[j]'hj).toFinset).card
      = ((winOrbits (gs, Δ))[j]'hj).toFinset.card + 1 :=
    Finset.card_insert_of_notMem (by simpa using hanot)
  have h3 : (insert a ((winOrbits (gs, Δ))[j]'hj).toFinset).card ≤ Δ.toFinset.card :=
    Finset.card_le_card hins
  have h4 : Δ.toFinset.card = Δ.length := List.toFinset_card_of_nodup hnd
  omega

/-! ## The mathematical round: Eq. (63) iterated

The chain is a fold: the candidate set of the next call is the answer of the previous one.
`Babai.SIInstance` takes an arbitrary set of candidates (Def. 11.1.2), so the coset needs no
representative here. -/

/-- **Luks's Chain Rule over a list of windows**, Eq. (63) iterated: the `j`-th call is the
instance with the coset reached so far as its candidate set, and the answer is the last
coset. -/
noncomputable def cosetChain {Ω A : Type*} (x y : Ω → A) :
    List (Set Ω) → Set (Perm Ω) → Babai.SIReduction Ω A (Set (Perm Ω))
  | [], C => .done C
  | Δ :: rest, C =>
      if C = ∅ then .done ∅
      else .call ⟨C, Δ, x, y⟩ fun ans => cosetChain x y rest ans

/-- **Proposition 11.1.7 iterated, Eq. (63)**: the chain computes the window isomorphisms for
the union of the windows. -/
theorem run_cosetChain {Ω A : Type*} (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)),
      (cosetChain x y Δs C).run = Babai.wIso (⋃ Δ ∈ Δs, Δ) C x y := by
  intro Δs
  induction Δs with
  | nil =>
      intro C
      rw [cosetChain, Babai.SIReduction.run_done]
      simp only [List.not_mem_nil, Set.iUnion_of_empty, Set.iUnion_empty]
      ext τ
      simp [Babai.wIso]
  | cons Δ rest ih =>
      intro C
      rw [cosetChain]
      by_cases hC : C = ∅
      · rw [if_pos hC, Babai.SIReduction.run_done, hC]
        symm
        rw [Set.eq_empty_iff_forall_notMem]
        exact fun τ hτ => hτ.1
      rw [if_neg hC, Babai.SIReduction.run_call]
      have hans : (⟨C, Δ, x, y⟩ : Babai.SIInstance Ω A).answer = Babai.wIso Δ C x y := rfl
      rw [hans, ih]
      have hunion : (⋃ Δ' ∈ (Δ :: rest), Δ') = Δ ∪ ⋃ Δ' ∈ rest, Δ' := by
        ext u
        simp only [Set.mem_iUnion, List.mem_cons, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨Δ', (rfl | hΔ'), hu⟩
          · exact Or.inl hu
          · exact Or.inr ⟨Δ', hΔ', hu⟩
        · rintro (hu | ⟨Δ', hΔ', hu⟩)
          · exact ⟨Δ, Or.inl rfl, hu⟩
          · exact ⟨Δ', Or.inr hΔ', hu⟩
      rw [hunion, Babai.wIso_window_union]
      ext τ
      simp only [Babai.mem_wIso, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hC, h1⟩, h2⟩; exact ⟨⟨hC, h1⟩, ⟨hC, h2⟩⟩
      · rintro ⟨⟨hC, h1⟩, ⟨-, h2⟩⟩; exact ⟨⟨hC, h1⟩, h2⟩

/-! ## The computable round -/

/-- The `j`-th child of the Chain Rule round: the instance whose window is the `j`-th orbit
and whose candidate set is the coset the fold has reached.  It is `none` when the index is
past the last orbit, when there is only one orbit (the Chain Rule would not make progress),
when the fold has already failed, and when the state is so malformed that the orbit is not
invariant under the group it names. -/
def winChild (p : RawWinSI × ℕ × RawCoset) : Option RawWinSI :=
  p.2.2.bind fun q =>
    if (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [] = [] then none
    else if (winOrbits (p.1.2.1, p.1.1)).length ≤ 1 then none
    else if rawIsInvariant (tidyGens (p.1.2.2.2.1, q.1),
        (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 []) then
      some ((winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [], tidyGens (p.1.2.2.2.1, q.1),
        normPerm (p.1.2.2.2.1, q.2), p.1.2.2.2.1, p.1.2.2.2.2)
    else none

/-- The state of the fold is the coset reached so far; the answer of a child replaces it. -/
def winCombine (p : RawWinSI × ℕ × RawCoset × RawCoset) : RawCoset := p.2.2.2

/-- **What `Algo.winChild` returns.**  The child exists only when the state is a coset, the
index names an orbit, there are at least two orbits, and the orbit is invariant under the
group the state names. -/
theorem winChild_eq_some {p : RawWinSI × ℕ × RawCoset} {J : RawWinSI}
    (h : winChild p = some J) :
    ∃ g τ, p.2.2 = some (g, τ) ∧
      (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [] ≠ [] ∧
      1 < (winOrbits (p.1.2.1, p.1.1)).length ∧
      rawIsInvariant (tidyGens (p.1.2.2.2.1, g),
        (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 []) = true ∧
      J = ((winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [], tidyGens (p.1.2.2.2.1, g),
        normPerm (p.1.2.2.2.1, τ), p.1.2.2.2.1, p.1.2.2.2.2) := by
  rw [winChild] at h
  rcases hs : p.2.2 with _ | ⟨g, τ⟩
  · rw [hs, Option.bind_none] at h; exact absurd h (by simp)
  · rw [hs, Option.bind_some] at h
    by_cases h1 : (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [] = []
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (winOrbits (p.1.2.1, p.1.1)).length ≤ 1
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        by_cases h3 : rawIsInvariant (tidyGens (p.1.2.2.2.1, g),
            (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 []) = true
        · rw [if_pos h3] at h
          exact ⟨g, τ, by first | rfl | exact hs, h1, by omega, h3, (Option.some.inj h).symm⟩
        · rw [if_neg h3] at h; exact absurd h (by simp)

/-- The child exists when everything the round tests is in order. -/
theorem winChild_eq_some_of {p : RawWinSI × ℕ × RawCoset} {g : RawGens} {τ : RawPerm}
    (hs : p.2.2 = some (g, τ))
    (h1 : (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [] ≠ [])
    (h2 : 1 < (winOrbits (p.1.2.1, p.1.1)).length)
    (h3 : rawIsInvariant (tidyGens (p.1.2.2.2.1, g),
      (winOrbits (p.1.2.1, p.1.1)).getD p.2.1 []) = true) :
    winChild p = some ((winOrbits (p.1.2.1, p.1.1)).getD p.2.1 [], tidyGens (p.1.2.2.2.1, g),
      normPerm (p.1.2.2.2.1, τ), p.1.2.2.2.1, p.1.2.2.2.2) := by
  rw [winChild, hs, Option.bind_some, if_neg h1, if_neg (by omega : ¬ _ ≤ 1), if_pos h3]

/-- The index of a child is the index of an orbit. -/
theorem winChild_index_lt {p : RawWinSI × ℕ × RawCoset} {J : RawWinSI}
    (h : winChild p = some J) : p.2.1 < (winOrbits (p.1.2.1, p.1.1)).length := by
  obtain ⟨g, τ, -, h1, -, -, -⟩ := winChild_eq_some h
  by_contra hcon
  exact h1 (List.getD_eq_default _ _ (by omega))

/-- **The Chain Rule round over the orbits** (§15 line 1 step 3; §11.1, Prop. 11.1.7 and
Eq. (64)).  `solve` is the rest of Procedure String-Isomorphism: it answers an instance whose
group is transitive on the window, where the Chain Rule has nothing to say.

`ground` is the size of the pair of strings, not the domain size `n`.  The alphabet here is
`ℕ`, so one letter can be arbitrarily large and `n` alone bounds no instance.  The two strings
are copied unchanged into every child, so this `ground` is constant along the recursion, which
is what `Algo.Round.child_ground` asks, and it is at least `n`, so a polynomial in it bounds
everything else in a well-formed instance (`Algo.chainCost`). -/
def chainRound (n : ℕ) (solve : RawWinSI → RawCoset) : Round RawWinSI RawCoset RawCoset where
  WF := WinWF n
  ground := fun I => Enc.size I.2.2.2
  measure := fun I => I.1.length
  width := fun I => (winOrbits (I.2.1, I.1)).length
  child := winChild
  init := fun I => some (I.2.1, I.2.2.1)
  combine := winCombine
  finish := fun p =>
    if (winOrbits (p.1.2.1, p.1.1)).length ≤ 1 then solve p.1 else p.2
  bot := none
  child_eq_none := by
    intro I j s hj
    rw [winChild]
    cases s with
    | none => rw [Option.bind_none]
    | some gt =>
        have hd : (winOrbits (I.2.1, I.1)).getD j [] = [] := List.getD_eq_default _ _ hj
        rw [Option.bind_some, if_pos hd]
  child_wf := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, h1, h2, h3, rfl⟩ := winChild_eq_some (p := (I, j, s)) hc
    obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI
    have hjl : j < (winOrbits (I.2.1, I.1)).length := winChild_index_lt (p := (I, j, s)) hc
    have hmem : (winOrbits (I.2.1, I.1)).getD j [] ∈ winOrbits (I.2.1, I.1) := by
      rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
    exact ⟨hx, hy, winOrbits_nodup hmem, winOrbits_lt hgs hlt hinv hmem,
      wf_tidyGens hx g, length_tidyGens hx g, wf_normPerm hx τ, h3⟩
  child_measure := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, h1, h2, h3, rfl⟩ := winChild_eq_some (p := (I, j, s)) hc
    obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI
    have hjl : j < (winOrbits (I.2.1, I.1)).length := winChild_index_lt (p := (I, j, s)) hc
    show ((winOrbits (I.2.1, I.1)).getD j []).length < I.1.length
    rw [List.getD_eq_getElem _ _ hjl]
    exact winOrbits_length_lt hgs hnd hlt hinv hjl h2
  child_ground := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, -, -, -, rfl⟩ := winChild_eq_some (p := (I, j, s)) hc
    exact le_refl _


/-! ## The link to the mathematical layer

`Algo.Implements` asks the fold of the raw round to walk the tree of `Algo.cosetChain` step by
step.  The invariant carried along the fold is `Algo.StateOK`: the raw state decodes to the
coset the tree has reached, that coset lies inside the candidate set of the instance, and the
group the state names is inside the group of the instance — which is what makes the invariance
test of `Algo.winChild` succeed. -/

/-- The orbit of a point, as a subset of the domain, is invariant. -/
theorem isInvariant_rawOrbit {gs : RawGens} (hgs : RawGens.WF n gs) {p : ℕ} (hp : p < n) :
    Babai.IsInvariant (decGroup n gs) {y : Fin n | (y : ℕ) ∈ rawOrbit (gs, p)} := by
  have hset : {y : Fin n | (y : ℕ) ∈ rawOrbit (gs, p)}
      = MulAction.orbit (decGroup n gs) (⟨p, hp⟩ : Fin n) := by
    ext y
    rw [Set.mem_setOf_eq, mem_rawOrbit_iff hgs hp]
    constructor
    · rintro ⟨h, hy⟩
      have : (⟨(y : ℕ), h⟩ : Fin n) = y := rfl
      rwa [this] at hy
    · intro hy
      exact ⟨y.isLt, hy⟩
  rw [hset]
  exact Babai.isInvariant_orbit _ _

theorem isInvariant_of_le {G M : Subgroup (Perm (Fin n))} {S : Set (Fin n)}
    (h : Babai.IsInvariant G S) (hMG : M ≤ G) : Babai.IsInvariant M S :=
  fun σ hσ => h σ (hMG hσ)

/-- **The group named by a raw coset inside a coset of `G` lies in `G`.** -/
theorem decGroup_le_of_subset {G : Subgroup (Perm (Fin n))} {σ₀ : Perm (Fin n)}
    {g : RawGens} {τ : Perm (Fin n)}
    (h : {ρ : Perm (Fin n) | ∃ u ∈ decGroup n g, ρ = τ * u}
      ⊆ {ρ : Perm (Fin n) | ∃ u ∈ G, ρ = σ₀ * u}) :
    decGroup n g ≤ G := by
  intro a ha
  obtain ⟨v, hv, hveq⟩ := h (show τ ∈ {ρ : Perm (Fin n) | ∃ u ∈ decGroup n g, ρ = τ * u} from
    ⟨1, one_mem _, by rw [mul_one]⟩)
  obtain ⟨u, hu, hueq⟩ := h (show τ * a ∈ {ρ : Perm (Fin n) | ∃ u ∈ decGroup n g, ρ = τ * u} from
    ⟨a, ha, rfl⟩)
  have : a = v⁻¹ * u := by
    have h1 : τ = σ₀ * v := hveq
    have h2 : τ * a = σ₀ * u := hueq
    rw [h1] at h2
    have := congrArg (fun z => (σ₀ * v)⁻¹ * z) h2
    simpa [mul_assoc] using this
  rw [this]
  exact mul_mem (inv_mem hv) hu

/-- The invariant carried along the fold of the Chain Rule round. -/
def StateOK (n : ℕ) (I : RawWinSI) (C : Set (Perm (Fin n))) (s : RawCoset) : Prop :=
  decCoset n s = C ∧ C ⊆ (decWinSI n I).K ∧
    ∀ g τ, s = some (g, τ) → decGroup n g ≤ decGroup n I.2.1

/-- The mathematical round the Chain Rule round implements: Eq. (63) iterated over the orbits
of Eq. (64) when there are at least two of them, and otherwise the leaf that hands the
instance to the rest of Procedure String-Isomorphism. -/
noncomputable def chainRoundReduction (n : ℕ) (solve : RawWinSI → RawCoset) (I : RawWinSI) :
    Babai.SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if (winOrbits (I.2.1, I.1)).length ≤ 1 then .done (decCoset n (solve I))
  else cosetChain (decStrN n I.2.2.2.1) (decStrN n I.2.2.2.2)
    ((winOrbits (I.2.1, I.1)).map (winSet n)) (decWinSI n I).K

/-- **The fold of the raw round walks the chain.** -/
theorem loopMatch_chainRound (n : ℕ) (solve : RawWinSI → RawCoset) {I : RawWinSI}
    (hI : WinWF n I) (h2 : 1 < (winOrbits (I.2.1, I.1)).length) :
    ∀ (k j : ℕ), j + k = (winOrbits (I.2.1, I.1)).length →
      ∀ (C : Set (Perm (Fin n))) (s : RawCoset), StateOK n I C s →
        LoopMatch (chainRound n solve) (decWinSI n) (decCoset n) I k j s
          (cosetChain (decStrN n I.2.2.2.1) (decStrN n I.2.2.2.2)
            (((winOrbits (I.2.1, I.1)).drop j).map (winSet n)) C) := by
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI
  intro k
  induction k with
  | zero =>
      intro j hj C s hs
      have hdrop : (winOrbits (I.2.1, I.1)).drop j = [] := by
        apply List.drop_eq_nil_of_le; omega
      rw [hdrop, List.map_nil, cosetChain]
      refine LoopMatch.done 0 j s C ?_ ?_
      · exact (chainRound n solve).child_eq_none I j s
          (by show (winOrbits (I.2.1, I.1)).length ≤ j; omega)
      · show decCoset n (if (winOrbits (I.2.1, I.1)).length ≤ 1 then solve I else s) = C
        rw [if_neg (by omega)]
        exact hs.1
  | succ k ih =>
      intro j hj C s hs
      have hjl : j < (winOrbits (I.2.1, I.1)).length := by omega
      have hdrop : (winOrbits (I.2.1, I.1)).drop j
          = ((winOrbits (I.2.1, I.1))[j]'hjl) :: (winOrbits (I.2.1, I.1)).drop (j + 1) :=
        List.drop_eq_getElem_cons hjl
      rw [hdrop, List.map_cons, cosetChain]
      cases s with
      | none =>
        -- the fold has already failed; the coset is empty and both stop
        have hCe : C = ∅ := by rw [← hs.1]; rfl
        rw [if_pos hCe]
        refine LoopMatch.done (k + 1) j none ∅ ?_ ?_
        · show winChild (I, j, none) = none
          rfl
        · show decCoset n (if (winOrbits (I.2.1, I.1)).length ≤ 1 then solve I
            else (none : RawCoset)) = ∅
          rw [if_neg (by omega)]
          rfl
      | some q =>
        obtain ⟨g, τ⟩ := q
        have hsv : (some (g, τ) : RawCoset) = some (g, τ) := rfl
        -- the fold is alive: the coset is nonempty and both call
        have hCne : C ≠ ∅ := by
          rw [← hs.1]
          intro hc
          have : decPerm n τ ∈ decCoset n (some (g, τ)) := ⟨1, one_mem _, by rw [mul_one]⟩
          rw [hc] at this
          exact this
        rw [if_neg hCne]
        -- the guards of `winChild`
        have hgetd : (winOrbits (I.2.1, I.1)).getD j [] = (winOrbits (I.2.1, I.1))[j]'hjl :=
          List.getD_eq_getElem _ _ hjl
        have hmemw : (winOrbits (I.2.1, I.1))[j]'hjl ∈ winOrbits (I.2.1, I.1) :=
          List.getElem_mem hjl
        have hne : (winOrbits (I.2.1, I.1)).getD j [] ≠ [] := by
          rw [hgetd]; exact winOrbits_ne_nil hmemw
        have hgle : decGroup n g ≤ decGroup n I.2.1 := hs.2.2 g τ hsv
        have htidy : decGroup n (tidyGens (I.2.2.2.1, g)) = decGroup n g :=
          decGroup_tidyGens hx g
        have hinvw : rawIsInvariant (tidyGens (I.2.2.2.1, g),
            (winOrbits (I.2.1, I.1)).getD j []) = true := by
          rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g)
            (by rw [hgetd]; exact winOrbits_lt hgs hlt hinv hmemw)]
          obtain ⟨p, hp, hpe⟩ := winOrbits_mem hmemw
          have hpn : p < n := hlt p hp
          have hset : {y : Fin n | (y : ℕ) ∈ (winOrbits (I.2.1, I.1)).getD j []}
              = {y : Fin n | (y : ℕ) ∈ rawOrbit (I.2.1, p)} := by
            rw [hgetd, hpe]
          rw [hset, htidy]
          exact isInvariant_of_le (isInvariant_rawOrbit hgs hpn) hgle
        have hchild : winChild (I, j, (some (g, τ) : RawCoset))
            = some ((winOrbits (I.2.1, I.1)).getD j [], tidyGens (I.2.2.2.1, g),
              normPerm (I.2.2.2.1, τ), I.2.2.2.1, I.2.2.2.2) :=
          winChild_eq_some_of (p := (I, j, (some (g, τ) : RawCoset))) hsv hne h2 hinvw
        set J : RawWinSI := ((winOrbits (I.2.1, I.1)).getD j [], tidyGens (I.2.2.2.1, g),
          normPerm (I.2.2.2.1, τ), I.2.2.2.1, I.2.2.2.2) with hJ
        have hdec : decWinSI n J
            = ⟨C, winSet n ((winOrbits (I.2.1, I.1))[j]'hjl),
                decStrN n I.2.2.2.1, decStrN n I.2.2.2.2⟩ := by
          have hK : decCoset n (some (tidyGens (I.2.2.2.1, g), normPerm (I.2.2.2.1, τ))) = C := by
            rw [← hs.1, hsv]
            show {ρ | ∃ u ∈ decGroup n (tidyGens (I.2.2.2.1, g)),
              ρ = decPerm n (normPerm (I.2.2.2.1, τ)) * u} = _
            rw [htidy, decPerm_normPerm hx τ]
            rfl
          rw [decWinSI, hJ]
          simp only
          rw [hK, hgetd]
        rw [← hdec]
        refine LoopMatch.call k j (some (g, τ)) J _
          (show (chainRound n solve).child (I, j, (some (g, τ) : RawCoset)) = some J from
            hchild) ?_
        intro a ha
        have hans : (decWinSI n J).answer
            = Babai.wIso (winSet n ((winOrbits (I.2.1, I.1))[j]'hjl)) C
                (decStrN n I.2.2.2.1) (decStrN n I.2.2.2.2) := by
          rw [Babai.SIInstance.answer, hdec]
        have hsub : (decWinSI n J).answer ⊆ C := by
          rw [hans]; exact fun ρ hρ => hρ.1
        refine ih (j + 1) (by omega) ((decWinSI n J).answer) a ?_
        refine ⟨ha, le_trans hsub hs.2.1, ?_⟩
        intro g₂ τ₂ ha2
        refine decGroup_le_of_subset (σ₀ := decPerm n I.2.2.1) (τ := decPerm n τ₂) ?_
        have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I).K := by
          rw [← ha2, ha]
          exact le_trans hsub hs.2.1
        exact h1

/-- **The link (Prop. 11.1.7 with Eq. (64)).**  The Chain Rule round implements the chain of
Eq. (63) over the orbits. -/
theorem implements_chainRound (n : ℕ) (solve : RawWinSI → RawCoset) :
    Implements (chainRound n solve) id (decWinSI n) (decCoset n) (chainRoundReduction n solve) := by
  intro I hI
  show LoopMatch (chainRound n solve) (decWinSI n) (decCoset n) I
    (winOrbits (I.2.1, I.1)).length 0 (some (I.2.1, I.2.2.1)) (chainRoundReduction n solve I)
  rw [chainRoundReduction]
  by_cases h2 : (winOrbits (I.2.1, I.1)).length ≤ 1
  · rw [if_pos h2]
    refine LoopMatch.done _ 0 _ _ ?_ ?_
    · show winChild (I, 0, (some (I.2.1, I.2.2.1) : RawCoset)) = none
      rw [winChild, Option.bind_some]
      by_cases hd : (winOrbits (I.2.1, I.1)).getD 0 [] = []
      · rw [if_pos hd]
      · rw [if_neg hd, if_pos h2]
    · show decCoset n (if (winOrbits (I.2.1, I.1)).length ≤ 1 then solve I else _)
        = decCoset n (solve I)
      rw [if_pos h2]
  · rw [if_neg h2]
    have h2' : 1 < (winOrbits (I.2.1, I.1)).length := by omega
    have := loopMatch_chainRound n solve hI h2' (winOrbits (I.2.1, I.1)).length 0 (by omega)
      (decWinSI n I).K (some (I.2.1, I.2.2.1)) ⟨rfl, le_refl _, ?_⟩
    · simpa using this
    · intro g τ hgt
      have : g = I.2.1 := congrArg (fun z => (Option.getD z (I.2.1, I.2.2.1)).1) hgt.symm
      rw [this]


/-! ## The round computes the answer

`Algo.roundValue_eq` needs the tree to be correct on every well-formed instance.  For the
Chain Rule that is Eq. (63) iterated (`Algo.run_cosetChain`) together with the fact that the
orbits of Eq. (64) cut the window exactly. -/

/-- **Eq. (64)**: the orbits inside the window cover it and nothing else. -/
theorem iUnion_winOrbits {gs : RawGens} (hgs : RawGens.WF n gs) {Δ : List ℕ}
    (hΔ : ∀ j ∈ Δ, j < n) (hinv : rawIsInvariant (gs, Δ) = true) :
    (⋃ S ∈ ((winOrbits (gs, Δ)).map (winSet n)), S) = winSet n Δ := by
  ext u
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨S, ⟨w, hw, rfl⟩, hu⟩
    exact winOrbits_subset hgs hΔ hinv hw (u : ℕ) hu
  · intro hu
    have := winOrbits_cover hgs hΔ (hu : (u : ℕ) ∈ Δ)
    obtain ⟨w, hw, huw⟩ := List.mem_flatten.1 this
    exact ⟨winSet n w, ⟨w, hw, rfl⟩, huw⟩

/-- **The mathematical round is correct**: its value is the answer of the instance, provided
the parameter `solve` answers the instances the Chain Rule leaves alone. -/
theorem run_chainRoundReduction (n : ℕ) (solve : RawWinSI → RawCoset) {I : RawWinSI}
    (hI : WinWF n I)
    (hsolve : (winOrbits (I.2.1, I.1)).length ≤ 1 →
      decCoset n (solve I) = (decWinSI n I).answer) :
    (chainRoundReduction n solve I).run = (decWinSI n I).answer := by
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI
  rw [chainRoundReduction]
  by_cases h2 : (winOrbits (I.2.1, I.1)).length ≤ 1
  · rw [if_pos h2, Babai.SIReduction.run_done]
    exact hsolve h2
  · rw [if_neg h2, run_cosetChain, iUnion_winOrbits hgs hlt hinv]
    rfl

/-! ## The running time

Every routine of the round is a `RAM.PolyFun`, hence a `RAM.QuasiPolyFun`
(`RAM.PolyFun.quasiPolyFun`), which is what `Algo.Round.Cost` asks of `child`, `init`,
`combine` and `finish`. -/

theorem polyFun_capPerm : PolyFun capPerm := by
  have hstep : PolyFun (fun z : (RawPerm × ℕ) × ℕ => min (rawGet (z.1.1, z.2)) z.1.2) :=
    ((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawGet).pair
      (polyFun_fst.comp polyFun_snd)).comp polyFun_min
  have hin : PolyFun (fun p : RawStr × RawPerm =>
      (((p.2, p.1.length - 1) : RawPerm × ℕ), rawOne p.1)) :=
    (polyFun_snd.pair (((polyFun_fst.comp polyFun_length).pair (polyFun_const 1)).comp
      polyFun_sub)).pair (polyFun_fst.comp polyFun_rawOne)
  exact (hin.comp (PolyFun.mapParam hstep)).of_eq (fun _ => rfl)

theorem polyFun_normPerm : PolyFun normPerm :=
  (PolyFun.ite (polyFun_capPerm.comp polyFun_rawIsPerm) polyFun_capPerm
    (polyFun_fst.comp polyFun_rawOne)).of_eq (fun p => by
      by_cases h : rawIsPerm (capPerm p) = true <;> simp [normPerm, h])

theorem polyFun_normGens : PolyFun normGens :=
  (PolyFun.mapParam polyFun_normPerm).of_eq (fun _ => rfl)

theorem polyFun_tidyGens : PolyFun tidyGens :=
  ((polyFun_fst.pair polyFun_normGens).comp polyFun_rawShorten).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
/-- **The orbit partition of the window is a `RAM.PolyFun`.**  This is
`Algo.polyFun_rawOrbits` with the loop running over the window instead of the whole
domain. -/
theorem polyFun_winOrbits : PolyFun winOrbits := by
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
      ((p.1, (([] : List (List ℕ)), p.2)) : RawGens × (List (List ℕ) × List ℕ))) :=
    polyFun_fst.pair (polyFun_nil.pair polyFun_snd)
  exact (hin.comp hfold).of_eq (fun p => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_winChild : PolyFun winChild := by
  have horb : PolyFun (fun p : RawWinSI × ℕ => winOrbits (p.1.2.1, p.1.1)) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits
  have hd : PolyFun (fun p : RawWinSI × ℕ => (winOrbits (p.1.2.1, p.1.1)).getD p.2 []) :=
    ((horb.pair polyFun_snd).pair (polyFun_const ([] : List ℕ))).comp polyFun_getD
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
      if (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [] = [] then (none : Option RawWinSI)
      else if (winOrbits (z.2.1.2.1, z.2.1.1)).length ≤ 1 then none
      else if rawIsInvariant (tidyGens (z.2.1.2.2.2.1, z.1.1),
          (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 []) then
        some ((winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [], tidyGens (z.2.1.2.2.2.1, z.1.1),
          normPerm (z.2.1.2.2.2.1, z.1.2), z.2.1.2.2.2.1, z.2.1.2.2.2.2)
      else none) := by
    have hdz : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 []) := polyFun_snd.comp hd
    have hx : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
      ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
        polyFun_snd).comp polyFun_fst
    have hy : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) => z.2.1.2.2.2.2) :=
      ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
        polyFun_snd).comp polyFun_snd
    have htg : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        tidyGens (z.2.1.2.2.2.1, z.1.1)) :=
      (hx.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_tidyGens
    have hnp : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        normPerm (z.2.1.2.2.2.1, z.1.2)) :=
      (hx.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_normPerm
    have hc1 : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        decide ((winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [] = [])) :=
      (hdz.pair (polyFun_const ([] : List ℕ))).comp polyFun_listNatEq
    have hc2 : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        decide ((winOrbits (z.2.1.2.1, z.2.1.1)).length ≤ 1)) :=
      (((polyFun_snd.comp horb).comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
    have hc3 : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        rawIsInvariant (tidyGens (z.2.1.2.2.2.1, z.1.1),
          (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [])) :=
      (htg.pair hdz).comp polyFun_rawIsInvariant
    have hsome : PolyFun (fun z : (RawGens × RawPerm) × (RawWinSI × ℕ) =>
        (some ((winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [], tidyGens (z.2.1.2.2.2.1, z.1.1),
          normPerm (z.2.1.2.2.2.1, z.1.2), z.2.1.2.2.2.1, z.2.1.2.2.2.2) : Option RawWinSI)) :=
      (hdz.pair (htg.pair (hnp.pair (hx.pair hy)))).comp polyFun_some
    refine (PolyFun.ite hc1 (polyFun_const (none : Option RawWinSI))
      (PolyFun.ite hc2 (polyFun_const (none : Option RawWinSI))
        (PolyFun.ite hc3 hsome (polyFun_const (none : Option RawWinSI))))).of_eq (fun z => ?_)
    by_cases h1 : (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 [] = []
    · simp [h1]
    · by_cases h2 : (winOrbits (z.2.1.2.1, z.2.1.1)).length ≤ 1
      · simp [h1, h2]
      · by_cases h3 : rawIsInvariant (tidyGens (z.2.1.2.2.2.1, z.1.1),
            (winOrbits (z.2.1.2.1, z.2.1.1)).getD z.2.2 []) <;> simp [h1, h2, h3]
  have hopt := PolyFun.optionElim (polyFun_const (none : Option RawWinSI)) hbody
  have hin : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      ((p.2.2, ((p.1, p.2.1) : RawWinSI × ℕ)) : RawCoset × (RawWinSI × ℕ))) :=
    (polyFun_snd.comp polyFun_snd).pair (polyFun_fst.pair (polyFun_snd.comp polyFun_fst))
  refine (hin.comp hopt).of_eq (fun p => ?_)
  rw [winChild]
  cases hq : p.2.2 with
  | none => rfl
  | some q => rfl

theorem polyFun_winCombine : PolyFun winCombine :=
  ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).of_eq (fun _ => rfl)

/-! ## The cost of the round

`Algo.Round.Cost` asks for one polynomial that bounds instances, states and answers in terms
of `ground`.  Here it is `Algo.chainBound`: a window of at most `n` points, at most `n * n`
generators of length `n`, one representative of length `n`, and the two strings. -/

/-- A list of at most `L` naturals, all below `m`, is small. -/
theorem size_natList_le {l : List ℕ} {L m : ℕ} (hlen : l.length ≤ L) (hlt : ∀ a ∈ l, a < m) :
    Enc.size l ≤ 1 + L * (2 * (m + 2) + 1) := by
  have h1 : ∀ a ∈ l, Enc.size a ≤ m + 2 := by
    intro a ha
    have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
    have h3 : Nat.size a ≤ a := size_le_self a
    have h4 := hlt a ha
    omega
  have h5 := size_list_le_of_entries l (m + 2) h1
  have h6 : l.length * (2 * (m + 2) + 1) ≤ L * (2 * (m + 2) + 1) :=
    Nat.mul_le_mul_right _ hlen
  omega

/-- The size of a list of at most `m` naturals below `m`: a window, a permutation. -/
def strBound (m : ℕ) : ℕ := 1 + m * (2 * (m + 2) + 1)

/-- The size of a list of at most `m * m` permutations. -/
def gensBound (m : ℕ) : ℕ := 1 + m * m * (2 * strBound m + 1)

/-- **The size bound of the Chain Rule round.** -/
def chainBound (m : ℕ) : ℕ := 16 * (gensBound m + m + 1)

theorem strBound_le_gensBound (m : ℕ) : strBound m ≤ gensBound m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [strBound, gensBound]
  · have h1 : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 1 * (2 * strBound m + 1) ≤ m * m * (2 * strBound m + 1) :=
      Nat.mul_le_mul_right _ h1
    have h3 : gensBound m = 1 + m * m * (2 * strBound m + 1) := rfl
    omega

theorem polyBound_chainBound : PolyBound chainBound := by
  have hS : PolyBound strBound :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1)))
  have hG : PolyBound gensBound :=
    (polyBound_const 1).add ((polyBound_id.mul polyBound_id).mul
      (((polyBound_const 2).mul hS).add (polyBound_const 1)))
  exact (polyBound_const 16).mul ((hG.add polyBound_id).add (polyBound_const 1))

theorem mono_chainBound : Monotone chainBound := by
  intro a b hab
  have h1 : strBound a ≤ strBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul hab (by omega)) 1
  have h2 : gensBound a ≤ gensBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul hab hab) (by omega)) 1
  exact Nat.mul_le_mul_left _ (by omega)

/-- The domain size is at most the size of the strings. -/
theorem le_size_strings {I : RawWinSI} (hI : WinWF n I) : n ≤ Enc.size I.2.2.2 := by
  have h1 := length_le_size I.2.2.2.1
  have h2 : Enc.size I.2.2.2.1 ≤ Enc.size I.2.2.2 := size_fst_le' I.2.2.2
  have h3 : I.2.2.2.1.length = n := hI.1
  omega

theorem size_win_le {I : RawWinSI} (hI : WinWF n I) :
    Enc.size I.1 ≤ strBound (Enc.size I.2.2.2) := by
  have hnm := le_size_strings hI
  exact size_natList_le (le_trans (length_le_of_nodup_lt hI.2.2.1 hI.2.2.2.1) hnm)
    (fun a ha => lt_of_lt_of_le (hI.2.2.2.1 a ha) hnm)

theorem size_rep_le {I : RawWinSI} (hI : WinWF n I) :
    Enc.size I.2.2.1 ≤ strBound (Enc.size I.2.2.2) := by
  have hnm := le_size_strings hI
  have hσ : RawPerm.WF n I.2.2.1 := hI.2.2.2.2.2.2.1
  exact size_natList_le (by rw [hσ.length]; exact hnm)
    (fun a ha => lt_of_lt_of_le (hσ.lt ha) hnm)

theorem size_gens_le {I : RawWinSI} (hI : WinWF n I) :
    Enc.size I.2.1 ≤ gensBound (Enc.size I.2.2.2) := by
  have hnm := le_size_strings hI
  have hgs : RawGens.WF n I.2.1 := hI.2.2.2.2.1
  have hgl : I.2.1.length ≤ n * n := hI.2.2.2.2.2.1
  set m := Enc.size I.2.2.2 with hm
  have hentry : ∀ g ∈ I.2.1, Enc.size g ≤ strBound m := by
    intro g hg
    exact size_natList_le (by rw [(hgs g hg).length]; exact hnm)
      (fun a ha => lt_of_lt_of_le ((hgs g hg).lt ha) hnm)
  have h1 := size_list_le_of_entries I.2.1 (strBound m) hentry
  have h2 : I.2.1.length * (2 * strBound m + 1) ≤ m * m * (2 * strBound m + 1) :=
    Nat.mul_le_mul_right _ (le_trans hgl (Nat.mul_le_mul hnm hnm))
  have h3 : gensBound m = 1 + m * m * (2 * strBound m + 1) := rfl
  omega

/-- **A well-formed instance is small**: everything in it is a list of at most `n * n` lists
of at most `n` naturals below `n`, and `n` is at most the size of the strings. -/
theorem size_winSI_le {I : RawWinSI} (hI : WinWF n I) :
    Enc.size I ≤ chainBound (Enc.size I.2.2.2) := by
  have hΔ := size_win_le hI
  have hσs := size_rep_le hI
  have hgens := size_gens_le hI
  have hp1 : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 :=
    Combine.size_pair_le I.1 I.2
  have hp2 : Enc.size I.2 ≤ 2 * Enc.size I.2.1 + 2 * Enc.size I.2.2 :=
    Combine.size_pair_le I.2.1 I.2.2
  have hp3 : Enc.size I.2.2 ≤ 2 * Enc.size I.2.2.1 + 2 * Enc.size I.2.2.2 :=
    Combine.size_pair_le I.2.2.1 I.2.2.2
  have hSG := strBound_le_gensBound (Enc.size I.2.2.2)
  have hb : chainBound (Enc.size I.2.2.2)
      = 16 * (gensBound (Enc.size I.2.2.2) + Enc.size I.2.2.2 + 1) := rfl
  omega

/-- The number of orbits inside the window is at most the number of points of the window. -/
theorem length_winOrbits_le (gs : RawGens) (Δ : List ℕ) :
    (winOrbits (gs, Δ)).length ≤ Δ.length := by
  obtain ⟨e, he, hlen, -⟩ := rawOrbits_fold_struct gs Δ []
  rw [winOrbits, he]
  simpa using hlen

/-- **The cost data of the Chain Rule round.**  `solve` is charged for: it has to be a
`RAM.QuasiPolyFun` and to answer within the same bound. -/
def chainCost (n : ℕ) (solve : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solve)
    (hsize : ∀ I, WinWF n I → Enc.size (solve I) ≤ chainBound (Enc.size I.2.2.2)) :
    Round.Cost (chainRound n solve) where
  bound := chainBound
  polyBound_bound := polyBound_chainBound
  mono_bound := mono_chainBound
  widthBound := fun m => m
  quasiPolyBound_widthBound := polyBound_id.quasiPoly
  quasiPolyFun_child := polyFun_winChild.quasiPolyFun
  quasiPolyFun_init :=
    (((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp polyFun_some).quasiPolyFun
  quasiPolyFun_combine := polyFun_winCombine.quasiPolyFun
  quasiPolyFun_finish := by
    have horb : PolyFun (fun p : RawWinSI × RawCoset => winOrbits (p.1.2.1, p.1.1)) :=
      (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
        (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits
    have hc : PolyFun (fun p : RawWinSI × RawCoset =>
        decide ((winOrbits (p.1.2.1, p.1.1)).length ≤ 1)) :=
      ((horb.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
    exact (QuasiPolyFun.ite hc (polyFun_fst.comp_quasi hsolve)
      polyFun_snd.quasiPolyFun).of_eq (fun p => by
        by_cases h : (winOrbits (p.1.2.1, p.1.1)).length ≤ 1 <;>
          simp [chainRound, h])
  ground_le := fun I =>
    le_trans (size_snd_le' I.2.2) (le_trans (size_snd_le' I.2) (size_snd_le' I))
  size_le := fun _ hI => size_winSI_le hI
  init_le := by
    intro I hI
    have h0 : Enc.size ((chainRound n solve).init I)
        = Enc.size ((I.2.1, I.2.2.1) : RawGens × RawPerm) + 2 := size_some_eq _
    have h1 : Enc.size ((I.2.1, I.2.2.1) : RawGens × RawPerm)
        ≤ 2 * Enc.size I.2.1 + 2 * Enc.size I.2.2.1 := Combine.size_pair_le _ _
    have h3 := size_gens_le hI
    have h4 := size_rep_le hI
    have hSG := strBound_le_gensBound (Enc.size I.2.2.2)
    have h5 : chainBound (Enc.size I.2.2.2) = 16 * (gensBound (Enc.size I.2.2.2)
        + Enc.size I.2.2.2 + 1) := rfl
    show Enc.size ((chainRound n solve).init I) ≤ chainBound (Enc.size I.2.2.2)
    omega
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := by
    intro I s hI hs
    show Enc.size (if (winOrbits (I.2.1, I.1)).length ≤ 1 then solve I else s)
      ≤ chainBound (Enc.size I.2.2.2)
    by_cases h : (winOrbits (I.2.1, I.1)).length ≤ 1
    · rw [if_pos h]; exact hsize I hI
    · rw [if_neg h]; exact hs
  bot_le := by
    intro m
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 : chainBound m = 16 * (gensBound m + m + 1) := rfl
    show Enc.size (none : RawCoset) ≤ chainBound m
    omega
  width_le := by
    intro I hI
    have h1 : (winOrbits (I.2.1, I.1)).length ≤ I.1.length := length_winOrbits_le _ _
    have h2 : I.1.length ≤ n := length_le_of_nodup_lt hI.2.2.1 hI.2.2.2.1
    exact le_trans h1 (le_trans h2 (le_size_strings hI))


end Algo
