/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.2: k-ary coherent configurations, and §5.2.1: restriction.
-/
import Workspace.Higher.Configurations
import Workspace.Higher.PrelimExtra

/-!
# §5.2 `k`-ary coherent configurations

## Finiteness

Axiom (iii) of Def. 5.2.2 counts elements of `Ω`, so it is stated with `Set.ncard`, as in
§3 (`Babai.PartitionStructure.IsCoherent`).  The proofs of Prop. 5.2.3 and of
Prop. 5.2.6(c) split a count into a sum over all color vectors `i⃗' ∈ C^k`, so they use
that `Ω` and the color set `C` are finite — both are standing assumptions of the paper
("`Ω` will denote a fixed set of `n` elements", "`C` … a finite linearly ordered set").

## Restriction and the arity `k - ℓ`

The paper writes the restriction `X_x⃗` of a `k`-ary structure by `x⃗ ∈ Ω^ℓ` (`ℓ < k`) as a
`(k-ℓ)`-ary structure.  Truncated subtraction on `ℕ` would make `k - ℓ` junk for `ℓ > k`,
so the arities are written here as `l + m = k` with `0 < m`, which is the same statement
for the paper's range `ℓ < k` and needs no side condition.

## Numbering map

| Paper | Lean |
|---|---|
| Notation 5.2.1 (Substitution) | `Babai.Str.subst` (`Higher/Strings.lean`) |
| Definition 5.2.2 (`k`-ary coherent configuration) | `Babai.KAryPartStruct.IsCoherent` |
| Def. 5.2.2, the intersection numbers `γ(i⃗ j)` | `.gamma`, `.gamma_eq`, `.count_eq_of_color_eq` |
| §5.2 the functor `F3` | `Babai.KAryPartStruct.F3` (`Higher/WL.lean`) |
| Proposition 5.2.3 (Skeleton 2) | `.skeleton_isCoherent` |
| Claim 5.2.4 | `.gamma_skeleton_eq_sum` |
| Proposition 5.2.5 (Induced coherent subconfiguration) | `.induced_isCoherent` |
| "Classical coherent configurations" (`k = 2`) | `Higher/Classical.lean` |
| §5.2.1 restriction `X_x⃗` | `.restrict` |
| Proposition 5.2.6 (a), (b), (c) | `.restrict_refines_skeleton`, `.restrict_canonical`, `.restrict_isCoherent` |
| Claim 5.2.7 | `.color_take_eq_of_color_eq_of_lt` (all `ℓ < k`), `.color_take_eq_of_color_eq` (`k = ℓ + 1`) |
| §5.3 `k`-ary WL refinement | `Higher/WL.lean` |
| §5.4 (the removed subsection) | `Higher/OldDefs.lean` |

The last section of the file has no counterpart in the paper: the colorings of §5 are
determined by their kernels (the paper's silent convention that the names of the colors do
not matter, cf. §5.1.3 where `F1` renames colors), which is `isConfiguration_congr` and
`isCoherent_congr`.  Recoloring a structure by the classes of its own coloring
(`recolorKer`) makes the color type finite, and this removes the hypothesis `[Fintype C]`
from Props. 5.2.3 and 5.2.6 (c) (`skeleton_isCoherent'`, `restrict_isCoherent'`); the
output type of `k`-ary WL is not finite, so §8 uses the primed versions throughout.
-/

namespace Babai

variable {Ω Ω' C : Type*} {k l m : ℕ}

namespace KAryPartStruct

variable (X : KAryPartStruct Ω C k)

/-- The vector of colors produced by substituting `z` into each coordinate of `w⃗`:
`colorVec X w⃗ z = (c(w⃗ ¹(z)), …, c(w⃗ ᵏ(z)))`.  Axiom (iii) of Def. 5.2.2 counts the
`z ∈ Ω` with a prescribed value of this vector. -/
def colorVec (w : Str Ω k) (z : Ω) : Str C k := fun s => X.color (Str.subst w s z)

theorem colorVec_eq_iff (w : Str Ω k) (z : Ω) (i : Str C k) :
    X.colorVec w z = i ↔ ∀ t : Fin k, X.color (Str.subst w t z) = i t :=
  funext_iff

/-- Definition 5.2.2 (`k`-ary coherent configuration).  "Let `X` be a `k`-ary
configuration.  We say that `X` is a *`k`-ary coherent configuration* if additionally it
satisfies the following axiom.  (iii) There is a collection of `|C|^{k+1}` parameters,
`(γ(i⃗ j) | i⃗ = i₁ … i_k ∈ C^k, j ∈ C)` such that for all `i⃗ ∈ C^k`, `j ∈ C`, and
`x⃗ ∈ Ω^k` such that `c(x⃗) = j`,
`|{z ∈ Ω | (∀t ∈ [k])(c(x⃗ ᵗ(z)) = i_t)}| = γ(i⃗ j)`.  (Eq. (33).)
The `γ(i⃗ j)` are called the *intersection numbers* of `X`." -/
structure IsCoherent (X : KAryPartStruct Ω C k) : Prop extends X.IsConfiguration where
  /-- Axiom (iii), Eq. (33). -/
  intersection : ∃ γ : Str C k → C → ℕ, ∀ (i : Str C k) (j : C) (x : Str Ω k),
    X.color x = j → {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard = γ i j

/-- Def. 5.2.2.  The intersection numbers `γ(i⃗ j)` of a `k`-ary coherent configuration.
(On colors `j` that no string realizes the value is unconstrained, as in the paper.) -/
noncomputable def gamma {X : KAryPartStruct Ω C k} (h : X.IsCoherent) : Str C k → C → ℕ :=
  h.intersection.choose

/-- Def. 5.2.2, Eq. (33), for the chosen family `γ`. -/
theorem gamma_eq {X : KAryPartStruct Ω C k} (h : X.IsCoherent) (i : Str C k) (j : C)
    (x : Str Ω k) (hx : X.color x = j) :
    {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard = gamma h i j :=
  h.intersection.choose_spec i j x hx

/-- Def. 5.2.2, Eq. (33), in the form used in the proofs: the count depends on `x⃗` only
through its color. -/
theorem IsCoherent.count_eq_of_color_eq {X : KAryPartStruct Ω C k} (h : X.IsCoherent)
    (i : Str C k) {x y : Str Ω k} (hxy : X.color x = X.color y) :
    {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard =
      {z : Ω | ∀ t : Fin k, X.color (Str.subst y t z) = i t}.ncard := by
  rw [gamma_eq h i (X.color x) x rfl, gamma_eq h i (X.color y) y rfl, hxy]

theorem IsCoherent.ncard_colorVec_eq {X : KAryPartStruct Ω C k} (h : X.IsCoherent)
    (i : Str C k) {x y : Str Ω k} (hxy : X.color x = X.color y) :
    {z : Ω | X.colorVec x z = i}.ncard = {z : Ω | X.colorVec y z = i}.ncard := by
  have h1 : {z : Ω | X.colorVec x z = i}
      = {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t} := by
    ext z; exact X.colorVec_eq_iff x z i
  have h2 : {z : Ω | X.colorVec y z = i}
      = {z : Ω | ∀ t : Fin k, X.color (Str.subst y t z) = i t} := by
    ext z; exact X.colorVec_eq_iff y z i
  rw [h1, h2]
  exact h.count_eq_of_color_eq i hxy

open scoped Classical in
/-- The counting workhorse for Prop. 5.2.3 and Prop. 5.2.6(c): a condition on `z` that
depends on `z` only through the color vector `colorVec X w⃗ z` splits into the fibers of
that vector, and each fiber is counted by an intersection number. -/
theorem ncard_of_colorVec_cond [Fintype Ω] [Fintype C] (Q : Str C k → Prop) (w : Str Ω k) :
    {z : Ω | Q (X.colorVec w z)}.ncard =
      ∑ i ∈ Finset.univ.filter Q, {z : Ω | X.colorVec w z = i}.ncard := by
  classical
  rw [ncard_fiberwise (fun z => Q (X.colorVec w z)) (X.colorVec w) Q (fun _ hz => hz)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hQ : Q i := by simpa using hi
  congr 1
  ext z
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨h ▸ hQ, h⟩

open scoped Classical in
/-- The corollary of `ncard_of_colorVec_cond` that is used twice: for a coherent `X`, a
condition on the color vector is satisfied by equally many `z` at any two strings of the
same color. -/
theorem IsCoherent.ncard_cond_eq [Fintype Ω] [Fintype C] {X : KAryPartStruct Ω C k}
    (h : X.IsCoherent) (Q : Str C k → Prop) {x y : Str Ω k} (hxy : X.color x = X.color y) :
    {z : Ω | Q (X.colorVec x z)}.ncard = {z : Ω | Q (X.colorVec y z)}.ncard := by
  classical
  rw [X.ncard_of_colorVec_cond Q x, X.ncard_of_colorVec_cond Q y]
  exact Finset.sum_congr rfl fun i _ => h.ncard_colorVec_eq i hxy

/-- Def. 5.2.2, axiom (iii) in the form "the count depends only on the color": this is
equivalent to the existence of the family `γ` (take for `γ(i⃗ j)` the count at any string
of color `j`, and `0` if `j` is not realized). -/
theorem isCoherent_of_count_eq {Y : KAryPartStruct Ω C k} (hcfg : Y.IsConfiguration)
    (hcount : ∀ (i : Str C k) (x y : Str Ω k), Y.color x = Y.color y →
      {z : Ω | ∀ t : Fin k, Y.color (Str.subst x t z) = i t}.ncard =
        {z : Ω | ∀ t : Fin k, Y.color (Str.subst y t z) = i t}.ncard) :
    Y.IsCoherent := by
  classical
  refine ⟨hcfg, ⟨fun i j => if hj : ∃ x : Str Ω k, Y.color x = j then
    {z : Ω | ∀ t : Fin k, Y.color (Str.subst hj.choose t z) = i t}.ncard else 0, ?_⟩⟩
  intro i j x hx
  have hj : ∃ x : Str Ω k, Y.color x = j := ⟨x, hx⟩
  show _ = dite _ _ _
  rw [dif_pos hj]
  exact hcount i x hj.choose (hx.trans hj.choose_spec.symm)

/-! ### Proposition 5.2.3 (Skeleton 2) -/

section Skeleton2

/-- Eq. (35) of the proof of Prop. 5.2.3.  "For `s = ℓ, ℓ+1, …, k` define the following
transformation `τ_s ∈ 𝔐_k`.  For `q ∈ [k]` set `q^{τ_s} = q` if `q ≤ ℓ-1` and
`q^{τ_s} = s` if `q ≥ ℓ`."  (`0`-based: `q` if `q < ℓ-1`, else `s`.) -/
def tauS (l : ℕ) (s : Fin k) : Mon k := fun q => if (q : ℕ) < l - 1 then q else s

/-- Eq. (36) of the proof of Prop. 5.2.3.  "For `t ≤ ℓ-1` we have
`pad(x⃗ ᵗ(z)) = (pad(x⃗))ᵗ(z)`." -/
theorem pad_subst_of_lt (hl : 0 < l) (hlk : l ≤ k) (x : Str Ω l) (t : Fin l)
    (ht : (t : ℕ) < l - 1) (z : Ω) :
    Str.pad hl k (Str.subst x t z) = Str.subst (Str.pad hl k x) (Fin.castLE hlk t) z := by
  funext q
  rcases Nat.lt_or_ge (q : ℕ) l with hq | hq
  · rw [Str.pad_eq, Str.padIdx_of_lt hl hq]
    by_cases hqt : (q : ℕ) = (t : ℕ)
    · have h1 : (⟨(q : ℕ), hq⟩ : Fin l) = t := Fin.ext hqt
      have h2 : q = Fin.castLE hlk t := Fin.ext (by simp [hqt])
      rw [h1, h2, Str.subst_same, Str.subst_same]
    · have h1 : (⟨(q : ℕ), hq⟩ : Fin l) ≠ t := fun hc => hqt (congrArg Fin.val hc)
      have h2 : q ≠ Fin.castLE hlk t := fun hc => hqt (by simpa using congrArg Fin.val hc)
      rw [Str.subst_of_ne _ h1, Str.subst_of_ne _ h2, Str.pad_eq, Str.padIdx_of_lt hl hq]
  · have h2 : q ≠ Fin.castLE hlk t := by
      intro hc
      have : (q : ℕ) = (t : ℕ) := by simpa using congrArg Fin.val hc
      omega
    rw [Str.pad_eq, Str.padIdx_of_ge hl (by omega), Str.subst_of_ne _ h2, Str.pad_eq,
      Str.padIdx_of_ge hl (by omega), Str.subst_of_ne]
    exact fun hc => by
      have : (l : ℕ) - 1 = (t : ℕ) := congrArg Fin.val hc
      omega

/-- The step of the proof of Prop. 5.2.3 that replaces the last coordinate: for every
`s ≥ ℓ` we have `τ_s((pad(x⃗))ˢ(z)) = pad(x⃗ ℓ(z))`.  This is what makes
"`c(pad(x⃗ ℓ(z))) = i_ℓ` if and only if `f_s(c((pad(x⃗))ˢ(z))) = i_ℓ`" true, and true for
*every* `s ≥ ℓ` at once, which is the form Claim 5.2.4 uses. -/
theorem idx_tauS_subst_pad (hl : 0 < l) (_hlk : l ≤ k) (x : Str Ω l) (s : Fin k)
    (hs : l - 1 ≤ (s : ℕ)) (z : Ω) :
    Str.idx (tauS l s) (Str.subst (Str.pad hl k x) s z)
      = Str.pad hl k (Str.subst x (Str.lastIdx l hl) z) := by
  funext q
  rw [Str.idx_apply, tauS]
  by_cases hq : (q : ℕ) < l - 1
  · rw [if_pos hq]
    have hqs : q ≠ s := by
      intro hc; rw [hc] at hq; omega
    rw [Str.subst_of_ne _ hqs, Str.pad_eq, Str.padIdx_of_lt hl (by omega), Str.pad_eq,
      Str.padIdx_of_lt hl (by omega), Str.subst_of_ne]
    exact fun hc => by
      have : (q : ℕ) = l - 1 := congrArg Fin.val hc
      omega
  · rw [if_neg hq, Str.subst_same, Str.pad_eq, Str.padIdx_of_ge hl (by omega),
      Str.subst_same]

/-- The set of color vectors `i⃗' ∈ C^k` that contribute to the `ℓ`-skeleton count for a
prescribed `i⃗ ∈ C^ℓ`: the summation condition of Claim 5.2.4, "`i'_s = i_s` for
`s ≤ ℓ-1` and `f_s(i'_s) = i_ℓ` for `s ≥ ℓ`", where `f_s = η(τ_s)` (Remark 5.1.9). -/
def GoodVec (hl : 0 < l) (hlk : l ≤ k) (i : Str C l) (i' : Str C k) : Prop :=
  (∀ t : Fin l, (t : ℕ) < l - 1 → i' (Fin.castLE hlk t) = i t) ∧
    (∀ s : Fin k, l - 1 ≤ (s : ℕ) → X.eta (tauS l s) (i' s) = i (Str.lastIdx l hl))

/-- The proof of Prop. 5.2.3: the conditions "`(∀t ∈ [ℓ])(c^{(ℓ)}(x⃗ ᵗ(z)) = i_t)`" on `z`
depend on `z` only through the color vector of `pad(x⃗)`, and the condition on that vector
is `GoodVec`, which does not involve `x⃗`. -/
theorem skeleton_cond_iff (h : X.IsConfiguration) (hl : 0 < l) (hlk : l ≤ k)
    (i : Str C l) (x : Str Ω l) (z : Ω) :
    (∀ t : Fin l, (X.skeleton hl hlk).color (Str.subst x t z) = i t)
      ↔ GoodVec X hl hlk i (X.colorVec (Str.pad hl k x) z) := by
  constructor
  · intro hz
    refine ⟨fun t ht => ?_, fun s hs => ?_⟩
    · have := hz t
      rw [skeleton_color, pad_subst_of_lt hl hlk x t ht z] at this
      exact this
    · have hlast := hz (Str.lastIdx l hl)
      rw [skeleton_color, ← idx_tauS_subst_pad hl hlk x s hs z,
        color_idx_eq_eta X h] at hlast
      exact hlast
  · rintro ⟨h1, h2⟩ t
    rcases Nat.lt_or_ge (t : ℕ) (l - 1) with ht | ht
    · rw [skeleton_color, pad_subst_of_lt hl hlk x t ht z]
      exact h1 t ht
    · have htl : t = Str.lastIdx l hl := Fin.ext (by have := t.2; simp [Str.lastIdx]; omega)
      have hs : (l : ℕ) - 1 ≤ ((⟨l - 1, by omega⟩ : Fin k) : ℕ) := by simp
      have := h2 ⟨l - 1, by omega⟩ hs
      rw [colorVec, ← color_idx_eq_eta X h,
        idx_tauS_subst_pad hl hlk x ⟨l - 1, by omega⟩ hs z] at this
      rw [htl, skeleton_color]
      exact this

/-- Proposition 5.2.3 (Skeleton 2).  "For `ℓ ≤ k`, the `ℓ`-skeleton `X^{(ℓ)}` of a `k`-ary
coherent configuration `X` is an `ℓ`-ary coherent configuration."

Paper's proof: "By Prop. 5.1.11, we only need to verify item (iii) in Def. 5.2.2.  We claim
that `X^{(ℓ)}` has intersection numbers `γ^{(ℓ)}(i⃗ j)` each of which is a sum of a subset
of the intersection numbers of `X`. … Let `x⃗ ∈ Ω^ℓ` with `c^{(ℓ)}(x⃗) = j`. … We need to
show that the number `γ^{(ℓ)}(i⃗ j)` of those `z ∈ Ω` for which
`(∀t ∈ [ℓ])(c^{(ℓ)}(x⃗ ᵗ(z)) = i_t)` does not depend on the specific choice of `x⃗` except
for the assumption that `c(x⃗) = j`. … For `t ≤ ℓ-1` … `pad(x⃗ ᵗ(z)) = (pad(x⃗))ᵗ(z)` …
This is not true for `t = ℓ`, however.  Instead we have `c(pad(x⃗ ℓ(z))) = i_ℓ` if and only
if for some `s ≥ ℓ` we have `f_s(c((pad(x⃗))ˢ(z))) = i_ℓ`."

(The proof as printed reads "for some `s ≥ ℓ`", while the summation condition of
Claim 5.2.4 reads "`f_s(i'_s) = i_ℓ` for `s ≥ ℓ`", i.e. for *all* `s ≥ ℓ`.  The two agree:
`idx_tauS_subst_pad` shows that `f_s(c((pad(x⃗))ˢ(z))) = c(pad(x⃗ ℓ(z)))` for every
`s ≥ ℓ`, so one `s` gives all of them.  We use the "for all" form, which is what makes the
sum of Claim 5.2.4 correct.) -/
theorem skeleton_isCoherent [Fintype Ω] [Fintype C] (h : X.IsCoherent) (hl : 0 < l)
    (hlk : l ≤ k) : (X.skeleton hl hlk).IsCoherent := by
  refine isCoherent_of_count_eq (X.skeleton_isConfiguration h.toIsConfiguration hl hlk)
    fun i x y hxy => ?_
  have hset : ∀ w : Str Ω l,
      {z : Ω | ∀ t : Fin l, (X.skeleton hl hlk).color (Str.subst w t z) = i t}
        = {z : Ω | GoodVec X hl hlk i (X.colorVec (Str.pad hl k w) z)} := by
    intro w
    ext z
    exact skeleton_cond_iff X h.toIsConfiguration hl hlk i w z
  rw [hset x, hset y]
  exact h.ncard_cond_eq (GoodVec X hl hlk i) hxy

open scoped Classical in
/-- Claim 5.2.4.  "`γ^{(ℓ)}(i⃗ j) = ∑ γ(i⃗' j)`, where the summation is over those strings
`i⃗' = i'₁ … i'_k ∈ C^k` satisfying `i'_s = i_s` for `s ≤ ℓ-1` and `f_s(i'_s) = i_ℓ` for
`s ≥ ℓ`."  (Eq. (37).)

The intersection numbers of a coherent configuration are pinned down only at the colors
that occur (Def. 5.1.3: a partition structure has no empty relation), so the statement is
for a color `j` realized by a string `x⃗ ∈ Ω^ℓ`. -/
theorem gamma_skeleton_eq_sum [Fintype Ω] [Fintype C] (h : X.IsCoherent) (hl : 0 < l)
    (hlk : l ≤ k) (i : Str C l) (x : Str Ω l) :
    gamma (X.skeleton_isCoherent h hl hlk) i ((X.skeleton hl hlk).color x) =
      ∑ i' ∈ Finset.univ.filter (GoodVec X hl hlk i),
        gamma h i' (X.color (Str.pad hl k x)) := by
  have hL := gamma_eq (X.skeleton_isCoherent h hl hlk) i ((X.skeleton hl hlk).color x) x rfl
  rw [← hL]
  have hset : {z : Ω | ∀ t : Fin l, (X.skeleton hl hlk).color (Str.subst x t z) = i t}
      = {z : Ω | GoodVec X hl hlk i (X.colorVec (Str.pad hl k x) z)} := by
    ext z
    exact skeleton_cond_iff X h.toIsConfiguration hl hlk i x z
  rw [hset, X.ncard_of_colorVec_cond (GoodVec X hl hlk i) (Str.pad hl k x)]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [← gamma_eq h i' (X.color (Str.pad hl k x)) (Str.pad hl k x) rfl]
  congr 1
  ext z
  exact X.colorVec_eq_iff (Str.pad hl k x) z i'

end Skeleton2

/-! ### Proposition 5.2.5 (Induced coherent subconfiguration) -/

section Induced

theorem induced_color_subst (Φ : Set Ω) (y : Str Φ k) (t : Fin k) (z : Φ) :
    (X.induced Φ).color (Str.subst y t z) =
      X.color (Str.subst (tupleMap Subtype.val y) t (z : Ω)) := by
  rw [induced_color, Str.subst_tupleMap]

/-- The solutions in `Φ` of the counting condition are the solutions in `Ω` that lie in
`Φ`. -/
theorem ncard_induced_sol (Φ : Set Ω) (i : Str C k) (y : Str Φ k) :
    {z : Φ | ∀ t : Fin k, (X.induced Φ).color (Str.subst y t z) = i t}.ncard =
      ({z : Ω | ∀ t : Fin k, X.color (Str.subst (tupleMap Subtype.val y) t z) = i t}
        ∩ Φ).ncard := by
  classical
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext u
  constructor
  · rintro ⟨⟨z, hz⟩, hzmem, rfl⟩
    refine ⟨fun t => ?_, hz⟩
    have ht := hzmem t
    rw [induced_color_subst] at ht
    exact ht
  · rintro ⟨h1, h2⟩
    exact ⟨⟨u, h2⟩, fun t => by rw [induced_color_subst]; exact h1 t, rfl⟩

/-- Proposition 5.2.5 (Induced coherent subconfiguration).  "Let `X = (Ω, c)` be a `k`-ary
coherent configuration.  Let `Φ ⊆ Ω` be a union of color classes of `Ω` (in the 1-skeleton
of `X`).  Then the induced substructure `X[Φ]` is a `k`-ary coherent configuration."

Paper's proof: "From Obs. 5.1.10 it is immediate that each intersection number `γ'(i⃗ j)`
of `X[Φ]` is either equal to the corresponding intersection number `γ(i⃗ j)` for `X` or it
is zero."

In detail: fix `i⃗` and two strings of `Φ^k` of the same color, and look at their solution
sets in `Ω`.  By Obs. 5.1.10, applied to the strings `x⃗ ᵗ(z)`, all solutions (of both) have
the same vertex color; since `Φ` is a union of vertex-color classes, either all of them lie
in `Φ`, in which case both counts equal the corresponding counts for `X`, or none does, in
which case both counts are `0`.

"Union of color classes of `Ω` (in the 1-skeleton)" is `hΦ`: membership in `Φ` depends
only on the vertex color. -/
theorem induced_isCoherent [Fintype Ω] [Fintype C] (h : X.IsCoherent) (Φ : Set Ω)
    (hΦ : ∀ u v : Ω, X.vcolor u = X.vcolor v → u ∈ Φ → v ∈ Φ) :
    (X.induced Φ).IsCoherent := by
  classical
  refine isCoherent_of_count_eq (X.induced_isConfiguration h.toIsConfiguration Φ)
    fun i y y' hyy => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the conditions are vacuous, so the two sets are the same
    simp
  obtain ⟨t₀⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  set w : Str Ω k := tupleMap Subtype.val y with hw
  set w' : Str Ω k := tupleMap Subtype.val y' with hw'
  have hcol : X.color w = X.color w' := hyy
  set S : Set Ω := {z : Ω | ∀ t : Fin k, X.color (Str.subst w t z) = i t} with hS
  set S' : Set Ω := {z : Ω | ∀ t : Fin k, X.color (Str.subst w' t z) = i t} with hS'
  have hcard : S.ncard = S'.ncard := h.count_eq_of_color_eq i hcol
  -- all solutions, on either side, have the same vertex color
  have hvc : ∀ z ∈ S, ∀ z' ∈ S', X.vcolor z = X.vcolor z' := by
    intro z hz z' hz'
    have hc : X.color (Str.subst w t₀ z) = X.color (Str.subst w' t₀ z') := by
      rw [hz t₀, hz' t₀]
    have := vcolor_eq_of_color_eq X h.toIsConfiguration hc t₀
    simpa using this
  have hvcS : ∀ z ∈ S, ∀ z₁ ∈ S, X.vcolor z = X.vcolor z₁ := by
    intro z hz z₁ hz₁
    have hc : X.color (Str.subst w t₀ z) = X.color (Str.subst w t₀ z₁) := by
      rw [hz t₀, hz₁ t₀]
    have := vcolor_eq_of_color_eq X h.toIsConfiguration hc t₀
    simpa using this
  have hvcS' : ∀ z ∈ S', ∀ z₁ ∈ S', X.vcolor z = X.vcolor z₁ := by
    intro z hz z₁ hz₁
    have hc : X.color (Str.subst w' t₀ z) = X.color (Str.subst w' t₀ z₁) := by
      rw [hz t₀, hz₁ t₀]
    have := vcolor_eq_of_color_eq X h.toIsConfiguration hc t₀
    simpa using this
  rw [ncard_induced_sol X Φ i y, ncard_induced_sol X Φ i y', ← hS, ← hS']
  rcases Set.eq_empty_or_nonempty S with hSe | ⟨z₀, hz₀⟩
  · have hS'e : S' = ∅ := by
      rw [hSe, Set.ncard_empty] at hcard
      exact (Set.ncard_eq_zero (Set.toFinite _)).1 hcard.symm
    rw [hSe, hS'e]
  obtain ⟨z₀', hz₀'⟩ : S'.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), ← hcard]
    exact Set.ncard_pos (Set.toFinite _) |>.2 ⟨z₀, hz₀⟩
  by_cases hmem : z₀ ∈ Φ
  · have hsub : S ⊆ Φ := fun z hz => hΦ z₀ z (hvcS z₀ hz₀ z hz) hmem
    have hmem' : z₀' ∈ Φ := hΦ z₀ z₀' (hvc z₀ hz₀ z₀' hz₀') hmem
    have hsub' : S' ⊆ Φ := fun z hz => hΦ z₀' z (hvcS' z₀' hz₀' z hz) hmem'
    rw [Set.inter_eq_self_of_subset_left hsub, Set.inter_eq_self_of_subset_left hsub']
    exact hcard
  · have hem : S ∩ Φ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzΦ⟩
      exact hmem (hΦ z z₀ (hvcS z hz z₀ hz₀) hzΦ)
    have hem' : S' ∩ Φ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzΦ⟩
      exact hmem (hΦ z z₀ (hvc z₀ hz₀ z hz).symm hzΦ)
    rw [hem, hem']

end Induced

/-! ### §5.2.1 Restriction -/

section Restriction

/-- §5.2.1 (Restriction).  "Let `X = (Ω, c)` be a `k`-ary partition structure.  Let `ℓ < k`
and `x⃗ ∈ Ω^ℓ`.  We assign a coloring `c_x⃗` to `Ω^{k-ℓ}` as follows.  For `y⃗ ∈ Ω^{k-ℓ}` we
set `c_x⃗(y⃗) = c(x⃗ y⃗)`.  (Eq. (38).)  We denote the resulting `(k-ℓ)`-ary partition
structure `(Ω, c_x⃗)` by `X_x⃗`.  We call `X_x⃗` the *restriction* of `X` by `x⃗`."

The arity is written `l + m` instead of `k`, so that the arity of the restriction is `m`
rather than the truncated difference `k - l`; `ℓ < k` is `0 < m`. -/
def restrict (X : KAryPartStruct Ω C (l + m)) (x : Str Ω l) : KAryPartStruct Ω C m :=
  ⟨fun y => X.color (Str.concat x y)⟩

@[simp] theorem restrict_color (X : KAryPartStruct Ω C (l + m)) (x : Str Ω l)
    (y : Str Ω m) : (X.restrict x).color y = X.color (Str.concat x y) := rfl

/-- Proposition 5.2.6 (a).  "`c_x⃗` is a refinement of the `c^{(k-ℓ)}` (the coloring of the
`(k-ℓ)`-skeleton `X^{(k-ℓ)}`)."

The paper offers no proof ("*** PROVE! ***") and says only that item (a) follows from
Claim 5.2.7.  Claim 5.2.7 is about *prefixes* (the color of `x⃗z` determines the color of
`x⃗`), while item (a) is about the *suffix* `y⃗` of `x⃗y⃗`; the proof below is the direct one,
by axiom (ii) of Def. 5.1.8 applied to the index transformation
`q ↦ ℓ + min(q, (k-ℓ)-1)`, which carries `x⃗y⃗` to `pad(y⃗)`.  Claim 5.2.7 is proved
separately below.  See the corrected paper, "hole in 2.5", §5.2.1, and the entry on
Prop. 5.2.6 (a). -/
theorem restrict_refines_skeleton (X : KAryPartStruct Ω C (l + m))
    (h : X.IsConfiguration) (hm : 0 < m) (x : Str Ω l) {y y' : Str Ω m}
    (hyy : (X.restrict x).color y = (X.restrict x).color y') :
    (X.skeleton hm (Nat.le_add_left m l)).color y =
      (X.skeleton hm (Nat.le_add_left m l)).color y' := by
  have key : ∀ u : Str Ω m,
      Str.idx (fun q : Fin (l + m) => Fin.natAdd l (Str.padIdx m hm q)) (Str.concat x u)
        = Str.pad hm (l + m) u := by
    intro u
    funext q
    rw [Str.idx_apply, Str.concat_right, Str.pad_eq]
  have := h.idx _ _ (fun q : Fin (l + m) => Fin.natAdd l (Str.padIdx m hm q)) hyy
  rw [key y, key y'] at this
  exact this

/-- Proposition 5.2.6 (b).  "The assignment `X ↦ X_x⃗` is canonical relative to `x⃗`":
an isomorphism `f : X → Y` is an isomorphism `X_x⃗ → Y_{x⃗^f}` for every `x⃗ ∈ Ω^ℓ`. -/
theorem restrict_canonical (X : KAryPartStruct Ω C (l + m)) (Y : KAryPartStruct Ω' C (l + m))
    (x : Str Ω l) {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) :
    f ∈ Iso (X.restrict x) (Y.restrict (tupleMap f x)) := by
  intro y
  rw [restrict_color, restrict_color, Str.concat_tupleMap, hf]

/-- Claim 5.2.7.  "If `ℓ < k` and `x⃗, y⃗ ∈ Ω^ℓ` and `z, w ∈ Ω` and `c(x⃗z) = c(y⃗w)` then
`c(x⃗) = c(y⃗)`."  (Here `c(x⃗)` is the extended coloring of §5.1.4, i.e. `c^{(ℓ)}(x⃗)`.)

The paper states the claim without proof; it follows from axiom (ii) of Def. 5.1.8 applied
to the index transformation `q ↦ min(q, ℓ-1)`, which carries `x⃗z` to `pad(x⃗)`.  See
the corrected paper, "hole in 2.5", §5.2.1. -/
theorem color_take_eq_of_color_eq (X : KAryPartStruct Ω C (l + 1)) (h : X.IsConfiguration)
    (hl : 0 < l) (x y : Str Ω l) (z w : Ω)
    (hc : X.color (Str.concat x fun _ : Fin 1 => z)
        = X.color (Str.concat y fun _ : Fin 1 => w)) :
    X.skeletonColor hl (Nat.le_add_right l 1) x
      = X.skeletonColor hl (Nat.le_add_right l 1) y := by
  have key : ∀ (u : Str Ω l) (v : Ω),
      Str.idx (fun q : Fin (l + 1) => Fin.castAdd 1 (Str.padIdx l hl q))
          (Str.concat u fun _ : Fin 1 => v) = Str.pad hl (l + 1) u := by
    intro u v
    funext q
    rw [Str.idx_apply, Str.concat_left, Str.pad_eq]
  have := h.idx _ _ (fun q : Fin (l + 1) => Fin.castAdd 1 (Str.padIdx l hl q)) hc
  rw [key x z, key y w] at this
  exact this

/-- Claim 5.2.7 for every `ℓ < k`, as printed: *"If `ℓ < k` and `x⃗, y⃗ ∈ Ω^ℓ` and `z, w ∈ Ω`
and `c(x⃗z) = c(y⃗w)` then `c(x⃗) = c(y⃗)`,"* where `c` on strings shorter than `k` is the
extended coloring of §5.1.4 (`c(x⃗z) = c^{(ℓ+1)}(x⃗z)`, `c(x⃗) = c^{(ℓ)}(x⃗)`).  The case
`k = ℓ + 1` is `color_take_eq_of_color_eq`.  Proof: axiom (ii) of Def. 5.1.8 for the
extended coloring (`skeletonColor_comp`), with the inclusion `[ℓ] → [ℓ+1]`. -/
theorem color_take_eq_of_color_eq_of_lt (X : KAryPartStruct Ω C k) (h : X.IsConfiguration)
    (hl : 0 < l) (hlk : l < k) (x y : Str Ω l) (z w : Ω)
    (hc : X.skeletonColor (Nat.succ_pos l) hlk (Str.concat x fun _ : Fin 1 => z)
        = X.skeletonColor (Nat.succ_pos l) hlk (Str.concat y fun _ : Fin 1 => w)) :
    X.skeletonColor hl hlk.le x = X.skeletonColor hl hlk.le y := by
  have := X.skeletonColor_comp h hl hlk.le (Nat.succ_pos l) hlk (fun i => Fin.castAdd 1 i) hc
  simpa using this

/-- Proposition 5.2.6 (c), the configuration part: the restriction of a `k`-ary
configuration is a `(k-ℓ)`-ary configuration. -/
theorem restrict_isConfiguration (X : KAryPartStruct Ω C (l + m)) (h : X.IsConfiguration)
    (x : Str Ω l) : (X.restrict x).IsConfiguration where
  rho y y' hyy i j := by
    have := h.rho _ _ hyy (Fin.natAdd l i) (Fin.natAdd l j)
    simpa using this
  idx y y' τ hyy := by
    have key : ∀ u : Str Ω m,
        Str.idx (Fin.addCases (fun i : Fin l => Fin.castAdd m i)
            (fun j : Fin m => Fin.natAdd l (τ j))) (Str.concat x u)
          = Str.concat x (Str.idx τ u) := by
      intro u
      funext q
      refine Fin.addCases (fun i => ?_) (fun j => ?_) q <;>
        simp [Str.idx, Str.concat_left, Str.concat_right]
    have := h.idx _ _ (Fin.addCases (fun i : Fin l => Fin.castAdd m i)
      (fun j : Fin m => Fin.natAdd l (τ j))) hyy
    rw [key y, key y'] at this
    exact this

/-- Proposition 5.2.6 (c).  "If `X` is a `k`-ary coherent configuration then `X_x⃗` is a
`(k-ℓ)`-ary coherent configuration."

The paper gives no proof ("*** PROVE! ***").  Proof supplied: the conditions
`c_x⃗(y⃗ ᵗ(z)) = i_t` (`t ∈ [k-ℓ]`) are the conditions `c((x⃗y⃗)^{ℓ+t}(z)) = i_t` on the last
`k-ℓ` coordinates of `x⃗y⃗`, so the count is the sum, over all color vectors `i⃗'` of the
first `ℓ` coordinates, of the intersection numbers `γ(i⃗'i⃗, c(x⃗y⃗))` of `X`; each term
depends on `y⃗` only through `c(x⃗y⃗) = c_x⃗(y⃗)`.  See the corrected paper, "hole in 2.5",
§5.2.1. -/
theorem restrict_isCoherent [Fintype Ω] [Fintype C] (X : KAryPartStruct Ω C (l + m))
    (h : X.IsCoherent) (x : Str Ω l) : (X.restrict x).IsCoherent := by
  refine isCoherent_of_count_eq (X.restrict_isConfiguration h.toIsConfiguration x)
    fun i y y' hyy => ?_
  have hset : ∀ u : Str Ω m,
      {z : Ω | ∀ t : Fin m, (X.restrict x).color (Str.subst u t z) = i t}
        = {z : Ω | (fun i' : Str C (l + m) => ∀ t : Fin m, i' (Fin.natAdd l t) = i t)
            (X.colorVec (Str.concat x u) z)} := by
    intro u
    ext z
    constructor
    · intro hz t
      have := hz t
      rw [restrict_color, Str.concat_subst] at this
      exact this
    · intro hz t
      have := hz t
      rw [restrict_color, Str.concat_subst]
      exact this
  rw [hset y, hset y']
  exact h.ncard_cond_eq
    (fun i' : Str C (l + m) => ∀ t : Fin m, i' (Fin.natAdd l t) = i t) hyy

end Restriction

end KAryPartStruct

/-! ### Transport of `IsCoherent` along a change of color names -/

namespace KAryPartStruct

variable {C' : Type*}

/-- Def. 5.1.8 and Def. 5.2.2 depend on the coloring only through its kernel: two
colorings of `Ω^k` with the same color classes define the same configuration and the same
coherent configuration.  (This is the paper's silent convention that the names of the
colors do not matter; cf. §5.1.3, where `F1` renames colors.) -/
theorem isConfiguration_congr {Y : KAryPartStruct Ω C k} {Z : KAryPartStruct Ω C' k}
    (hker : ∀ x y : Str Ω k, Y.color x = Y.color y ↔ Z.color x = Z.color y)
    (h : Y.IsConfiguration) : Z.IsConfiguration where
  rho x y hxy i j := h.rho x y ((hker x y).2 hxy) i j
  idx x y τ hxy := (hker _ _).1 (h.idx x y τ ((hker x y).2 hxy))

theorem isCoherent_congr {Y : KAryPartStruct Ω C k} {Z : KAryPartStruct Ω C' k}
    (hker : ∀ x y : Str Ω k, Y.color x = Y.color y ↔ Z.color x = Z.color y)
    (h : Y.IsCoherent) : Z.IsCoherent := by
  classical
  refine isCoherent_of_count_eq (isConfiguration_congr hker h.toIsConfiguration)
    fun i x y hxy => ?_
  by_cases hall : ∀ t : Fin k, ∃ w : Str Ω k, Z.color w = i t
  · choose w hw using hall
    have hset : ∀ u : Str Ω k,
        {z : Ω | ∀ t : Fin k, Z.color (Str.subst u t z) = i t}
          = {z : Ω | ∀ t : Fin k, Y.color (Str.subst u t z) = Y.color (w t)} := by
      intro u
      ext z
      constructor
      · intro hz t
        exact (hker _ _).2 ((hz t).trans (hw t).symm)
      · intro hz t
        exact ((hker _ _).1 (hz t)).trans (hw t)
    rw [hset x, hset y]
    exact h.count_eq_of_color_eq (fun t => Y.color (w t)) ((hker x y).2 hxy)
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    have hempty : ∀ u : Str Ω k,
        {z : Ω | ∀ t : Fin k, Z.color (Str.subst u t z) = i t} = ∅ := by
      intro u
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      exact ht _ (hz t)
    rw [hempty x, hempty y]

end KAryPartStruct


namespace KAryPartStruct

variable {C' : Type*}

/-! ### Recoloring by the kernel -/

/-- The recoloring of a `k`-ary partition structure by the classes of its own coloring:
the new color of `x⃗` is the set of all strings of the same old color.  The color type is
finite as soon as `Ω` is. -/
def recolorKer (X : KAryPartStruct Ω C k) : KAryPartStruct Ω (Set (Str Ω k)) k :=
  ⟨fun x => {y | X.color y = X.color x}⟩

theorem recolorKer_color_eq_iff (X : KAryPartStruct Ω C k) (x y : Str Ω k) :
    X.recolorKer.color x = X.recolorKer.color y ↔ X.color x = X.color y := by
  constructor
  · intro h
    have : y ∈ {z : Str Ω k | X.color z = X.color x} := by
      rw [show {z : Str Ω k | X.color z = X.color x} = X.recolorKer.color x from rfl, h]
      rfl
    exact this.symm
  · intro h
    show {z : Str Ω k | X.color z = X.color x} = {z : Str Ω k | X.color z = X.color y}
    rw [h]

theorem recolorKer_isCoherent (X : KAryPartStruct Ω C k) (h : X.IsCoherent) :
    X.recolorKer.IsCoherent :=
  isCoherent_congr (fun x y => (recolorKer_color_eq_iff X x y).symm) h

/-- Proposition 5.2.6 (c) without the hypothesis that the color type is finite. -/
theorem restrict_isCoherent' [Fintype Ω] (X : KAryPartStruct Ω C (l + m))
    (h : X.IsCoherent) (x : Str Ω l) : (X.restrict x).IsCoherent := by
  classical
  haveI : Fintype (Set (Str Ω (l + m))) := Fintype.ofFinite _
  have h' := X.recolorKer.restrict_isCoherent (X.recolorKer_isCoherent h) x
  refine isCoherent_congr (fun a b => ?_) h'
  simpa [restrict] using recolorKer_color_eq_iff X (Str.concat x a) (Str.concat x b)

/-- Proposition 5.2.3 (the `ℓ`-skeleton of a `k`-ary coherent configuration is an `ℓ`-ary
coherent configuration) without the hypothesis that the color type is finite. -/
theorem skeleton_isCoherent' [Fintype Ω] (X : KAryPartStruct Ω C k)
    (h : X.IsCoherent) (hl : 0 < l) (hlk : l ≤ k) : (X.skeleton hl hlk).IsCoherent := by
  classical
  haveI : Fintype (Set (Str Ω k)) := Fintype.ofFinite _
  have h' := X.recolorKer.skeleton_isCoherent (X.recolorKer_isCoherent h) hl hlk
  refine isCoherent_congr (fun a b => ?_) h'
  simpa [skeleton, skeletonColor] using
    recolorKer_color_eq_iff X (Str.pad hl k a) (Str.pad hl k b)


end KAryPartStruct

end Babai
