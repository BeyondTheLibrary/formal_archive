/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the point stabilizer chain and its sifting table, as mathematics.
-/
import Workspace.Luks.Defs

/-!
# The point stabilizer chain, sifting, and the table

The paper never states this machinery, and never proves anything about it, but Secs. 11–15 use
it constantly: a transversal of `G` over `N` (Prop. 11.1.6, Thm. 11.1.9), constructive
membership testing (Remark 12.0.2, Def. 11.1.10), the order `|G|` (Procedure
Reduce-to-Johnson, lines 2 and 5), the pointwise stabilizer of a set (Sec. 13.1 line 08), and
the shortening of a generating list that the output size bound of `RAM.SIWorkspaceRoutine`
demands.  `Workspace/Algo/DESIGN.md`, item 2, class D lists all of them among the routines
that have to be **proved**, since the paper cites no source.  This file is the mathematics of
work package A4; the raw routines live in `Workspace/Algo/ChainRaw.lean`.

## The chain

For `G ≤ Sym(Fin n)` the chain is `G = G⁰ ≥ G¹ ≥ … ≥ Gⁿ = 1`, where `Gⁱ` is the pointwise
stabilizer of `{0, …, i−1}`; here it is `Algo.chainStab G i`, built from the paper's
`Babai.pointwiseStabilizer` (Eq. (12)).

## The table

`Algo.Table n` is a function `T : ℕ → ℕ → Option (Equiv.Perm (Fin n))`.  The intended meaning
of `T i j = some τ` is: `τ` lies in `Gⁱ` and sends `i` to `j`.  `Algo.IsTable T G` says exactly
that, and `Algo.Complete T G` says that the table misses nothing: for every level `i < n` and
every `σ ∈ Gⁱ` the position `(i, σ i)` is filled.  Row `i` is then a transversal of `Gⁱ⁺¹`
in `Gⁱ`, one entry per point of the `Gⁱ`-orbit of `i`.

`Algo.sift T σ` strips `σ` level by level: at level `i` it looks up the entry `τ` at the
position `(i, σ i)` and continues with `τ⁻¹σ`, which fixes `i` as well as `0, …, i−1`.  It
answers `none` as soon as an entry is missing, and otherwise the residue after `n` levels,
which fixes every point and is therefore the identity (`Algo.sift_eq_some_eq_one`).  So
"`σ` sifts to the identity" is `Algo.sift T σ = some 1`.

## Main results

* `Algo.mem_iff_sift_eq_one` — **membership**: for a complete table, `σ ∈ G` exactly when `σ`
  sifts to the identity;
* `Algo.card_eq_prod_row_card` — **order**: `|G|` is the product over the levels of the number
  of filled positions in each row;
* `Algo.complete_of_closed` — **the closure criterion** (Sims; Furst–Hopcroft–Luks): a table
  whose entries lie in `G`, whose diagonal holds the identity, through which every generator
  sifts to the identity and through which the product of any two entries sifts to the
  identity, is complete for `G`;
* `Algo.exists_complete_table` — every `G` has such a table, so none of the three statements
  above is vacuous, and the hypotheses of the closure criterion can be met
  (`Algo.fullTable_closed`).

## A warning about the criterion

`Algo.complete_of_closed` needs the hypothesis that the diagonal of the table holds the
identity (`∀ i < n, T i i = some 1`), and it is **false** without it: the empty table over the
empty generating set satisfies all the other hypotheses vacuously, and it is not complete for
the trivial group, since the position `(i, i)` is empty although `1 ∈ Gⁱ` sends `i` to `i`.
The diagonal is how every implementation initializes the table, so the hypothesis costs
nothing; but it has to be said.

No axiom, no `sorry`, and no running-time claim: the running time of the raw routines is in
`Workspace/Algo/ChainRaw.lean`, as `RAM.PolyFun`.
-/

namespace Algo

variable {n : ℕ}

/-! ## Reading a permutation at a level

The levels of the chain are natural numbers, because sifting walks from `i` to `i + 1`, while a
point of the domain is a `Fin n`.  `Algo.evalAt σ i` is the image of the level `i` under `σ`,
read as a natural number, and the level itself when `i` is past the domain.  That convention
makes `Algo.evalAt_mul` hold with no hypothesis. -/

/-- The image of the level `i` under `σ`, as a natural number. -/
def evalAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩ : ℕ) else i

theorem evalAt_of_lt (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    evalAt σ i = (σ ⟨i, h⟩ : ℕ) := dif_pos h

theorem evalAt_of_le (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : n ≤ i) : evalAt σ i = i :=
  dif_neg (Nat.not_lt.2 h)

@[simp] theorem evalAt_one (i : ℕ) : evalAt (1 : Equiv.Perm (Fin n)) i = i := by
  unfold evalAt; split <;> rfl

theorem evalAt_lt (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) : evalAt σ i < n := by
  rw [evalAt_of_lt σ h]; exact (σ ⟨i, h⟩).isLt

/-- The image of a level under a product.  No hypothesis is needed: past the domain both sides
are the level itself. -/
theorem evalAt_mul (σ τ : Equiv.Perm (Fin n)) (i : ℕ) :
    evalAt (σ * τ) i = evalAt σ (evalAt τ i) := by
  by_cases h : i < n
  · rw [evalAt_of_lt _ h, evalAt_of_lt τ h, evalAt_of_lt σ (τ ⟨i, h⟩).isLt]
    simp
  · rw [evalAt_of_le _ (Nat.le_of_not_lt h), evalAt_of_le τ (Nat.le_of_not_lt h),
      evalAt_of_le σ (Nat.le_of_not_lt h)]

theorem evalAt_inv_left (σ : Equiv.Perm (Fin n)) (i : ℕ) : evalAt σ⁻¹ (evalAt σ i) = i := by
  rw [← evalAt_mul]; simp

/-- `Algo.Fixes i σ`: the permutation fixes every point below the level `i`.  This is what the
`i`-th group of the chain asks of its elements. -/
def Fixes {n : ℕ} (i : ℕ) (σ : Equiv.Perm (Fin n)) : Prop := ∀ k : Fin n, (k : ℕ) < i → σ k = k

theorem Fixes.evalAt {i : ℕ} {σ : Equiv.Perm (Fin n)} (h : Fixes i σ) {k : ℕ} (hk : k < i) :
    evalAt σ k = k := by
  by_cases hkn : k < n
  · rw [evalAt_of_lt σ hkn, h ⟨k, hkn⟩ hk]
  · exact evalAt_of_le σ (Nat.le_of_not_lt hkn)

theorem fixes_of_evalAt {i : ℕ} {σ : Equiv.Perm (Fin n)} (h : ∀ k < i, evalAt σ k = k) :
    Fixes i σ := by
  intro k hk
  have hk' := h (k : ℕ) hk
  rw [evalAt_of_lt σ k.isLt] at hk'
  exact Fin.ext (by simpa using hk')

theorem Fixes.mono {i j : ℕ} {σ : Equiv.Perm (Fin n)} (h : Fixes i σ) (hle : j ≤ i) :
    Fixes j σ := fun k hk => h k (lt_of_lt_of_le hk hle)

@[simp] theorem fixes_one (i : ℕ) : Fixes i (1 : Equiv.Perm (Fin n)) := fun _ _ => rfl

theorem Fixes.mul {i : ℕ} {a b : Equiv.Perm (Fin n)} (ha : Fixes i a) (hb : Fixes i b) :
    Fixes i (a * b) := by
  intro k hk
  show a (b k) = k
  rw [hb k hk, ha k hk]

theorem Fixes.inv {i : ℕ} {a : Equiv.Perm (Fin n)} (ha : Fixes i a) : Fixes i a⁻¹ := by
  intro k hk
  conv_lhs => rw [← ha k hk]
  simp

/-- A permutation that fixes every level below the degree is the identity. -/
theorem eq_one_of_fixes {σ : Equiv.Perm (Fin n)} (h : Fixes n σ) : σ = 1 :=
  Equiv.ext fun k => h k k.isLt

/-! ## The chain -/

/-- **The `i`-th group of the point stabilizer chain**, `Gⁱ`: the elements of `G` that fix
`0, …, i−1` pointwise.  This is the paper's `G_(T)` of Eq. (12) for `T = {0, …, i−1}`. -/
def chainStab (G : Subgroup (Equiv.Perm (Fin n))) (i : ℕ) : Subgroup (Equiv.Perm (Fin n)) :=
  Babai.pointwiseStabilizer G {k : Fin n | (k : ℕ) < i}

theorem mem_chainStab {G : Subgroup (Equiv.Perm (Fin n))} {i : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ chainStab G i ↔ σ ∈ G ∧ Fixes i σ := Iff.rfl

theorem chainStab_zero (G : Subgroup (Equiv.Perm (Fin n))) : chainStab G 0 = G := by
  ext σ
  rw [mem_chainStab]
  exact ⟨fun h => h.1, fun h => ⟨h, fun k hk => absurd hk (by omega)⟩⟩

theorem chainStab_degree (G : Subgroup (Equiv.Perm (Fin n))) : chainStab G n = ⊥ := by
  ext σ
  rw [mem_chainStab, Subgroup.mem_bot]
  exact ⟨fun h => eq_one_of_fixes h.2, fun h => by subst h; exact ⟨G.one_mem, fixes_one n⟩⟩

theorem chainStab_le (G : Subgroup (Equiv.Perm (Fin n))) (i : ℕ) : chainStab G i ≤ G :=
  fun _ h => h.1

theorem chainStab_mono {G : Subgroup (Equiv.Perm (Fin n))} {i j : ℕ} (h : i ≤ j) :
    chainStab G j ≤ chainStab G i := fun _ hσ =>
  mem_chainStab.2 ⟨(mem_chainStab.1 hσ).1, (mem_chainStab.1 hσ).2.mono h⟩

/-! ## The table and sifting -/

/-- **A sifting table.**  `T i j = some τ` is meant to say: `τ` lies in the `i`-th group of the
chain and sends the level `i` to `j`.  The table is a function, so it is total; the conditions
are `Algo.IsTable`. -/
abbrev Table (n : ℕ) := ℕ → ℕ → Option (Equiv.Perm (Fin n))

/-- **Sifting through the table.**  `siftAux T k i σ` strips `σ` through the `k` levels
`i, i+1, …, i+k−1`: at level `i` it looks up the entry `τ` at the position `(i, σ i)` and
continues with `τ⁻¹σ`, which fixes `i`.  A missing entry answers `none`. -/
def siftAux (T : Table n) : ℕ → ℕ → Equiv.Perm (Fin n) → Option (Equiv.Perm (Fin n))
  | 0, _, r => some r
  | (k + 1), i, r =>
      match T i (evalAt r i) with
      | none => none
      | some τ => siftAux T k (i + 1) (τ⁻¹ * r)

/-- **Sifting**: all `n` levels, from the level `0`. -/
def sift (T : Table n) (σ : Equiv.Perm (Fin n)) : Option (Equiv.Perm (Fin n)) :=
  siftAux T n 0 σ

@[simp] theorem siftAux_zero (T : Table n) (i : ℕ) (r : Equiv.Perm (Fin n)) :
    siftAux T 0 i r = some r := rfl

theorem siftAux_succ_of_none {T : Table n} {k i : ℕ} {r : Equiv.Perm (Fin n)}
    (h : T i (evalAt r i) = none) : siftAux T (k + 1) i r = none := by
  show (match T i (evalAt r i) with
      | none => none
      | some τ => siftAux T k (i + 1) (τ⁻¹ * r)) = none
  rw [h]

theorem siftAux_succ_of_some {T : Table n} {k i : ℕ} {r τ : Equiv.Perm (Fin n)}
    (h : T i (evalAt r i) = some τ) :
    siftAux T (k + 1) i r = siftAux T k (i + 1) (τ⁻¹ * r) := by
  show (match T i (evalAt r i) with
      | none => none
      | some τ => siftAux T k (i + 1) (τ⁻¹ * r)) = _
  rw [h]

/-- **The elements that sift to the identity** through the `k` levels from `i`. -/
def Sifted (T : Table n) (k i : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | siftAux T k i σ = some 1}

theorem mem_sifted_zero {T : Table n} {i : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ Sifted T 0 i ↔ σ = 1 := by
  simp only [Sifted, Set.mem_setOf_eq, siftAux_zero, Option.some.injEq]

theorem mem_sifted_succ {T : Table n} {k i : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ Sifted T (k + 1) i ↔
      ∃ τ, T i (evalAt σ i) = some τ ∧ τ⁻¹ * σ ∈ Sifted T k (i + 1) := by
  rcases h : T i (evalAt σ i) with _ | τ
  · simp only [Sifted, Set.mem_setOf_eq, siftAux_succ_of_none h]
    simp
  · simp only [Sifted, Set.mem_setOf_eq, siftAux_succ_of_some h]
    simp

/-- The entries of one row of the table. -/
def Entries (T : Table n) (i : ℕ) : Set (Equiv.Perm (Fin n)) := {τ | ∃ j, T i j = some τ}

/-- All the entries of the table. -/
def AllEntries (T : Table n) : Set (Equiv.Perm (Fin n)) := {τ | ∃ i j, T i j = some τ}

theorem mem_allEntries {T : Table n} {i j : ℕ} {τ : Equiv.Perm (Fin n)} (h : T i j = some τ) :
    τ ∈ AllEntries T := ⟨i, j, h⟩

theorem mem_entries {T : Table n} {i j : ℕ} {τ : Equiv.Perm (Fin n)} (h : T i j = some τ) :
    τ ∈ Entries T i := ⟨j, h⟩

/-- **A table for `G`**: every entry lies in `G`, the entry at the position `(i, j)` fixes every
level below `i`, and it sends the level `i` to `j`. -/
structure IsTable (T : Table n) (G : Subgroup (Equiv.Perm (Fin n))) : Prop where
  mem : ∀ {i j : ℕ} {τ : Equiv.Perm (Fin n)}, T i j = some τ → τ ∈ G
  fixes : ∀ {i j : ℕ} {τ : Equiv.Perm (Fin n)}, T i j = some τ → Fixes i τ
  img : ∀ {i j : ℕ} {τ : Equiv.Perm (Fin n)}, T i j = some τ → evalAt τ i = j

theorem IsTable.mem_chainStab {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) {i j : ℕ} {τ : Equiv.Perm (Fin n)} (h : T i j = some τ) :
    τ ∈ chainStab G i := ⟨hT.mem h, hT.fixes h⟩

/-- **A complete table for `G`**: for every level `i` below the degree and every `σ ∈ Gⁱ`, the
position `(i, σ i)` of the table is filled.  Equivalently, row `i` has an entry for every point
of the `Gⁱ`-orbit of `i`. -/
def Complete (T : Table n) (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ i < n, ∀ σ ∈ chainStab G i, T i (evalAt σ i) ≠ none

/-! ## What sifting does in general

Three facts that need nothing but `Algo.IsTable`: the residue differs from the input by an
element of the group generated by the entries; the residue fixes every level already passed;
and an element that sifts to the identity from the level `i` fixes every level below `i`. -/

/-- **The residue is the input times an element of the group generated by the entries.** -/
theorem siftAux_residue (T : Table n) :
    ∀ (k i : ℕ) (σ r : Equiv.Perm (Fin n)), siftAux T k i σ = some r →
      ∃ p ∈ Subgroup.closure (AllEntries T), r = p * σ := by
  intro k
  induction k with
  | zero =>
      intro i σ r h
      exact ⟨1, Subgroup.one_mem _, by simpa using (Option.some.inj h).symm⟩
  | succ k ih =>
      intro i σ r h
      rcases hT : T i (evalAt σ i) with _ | τ
      · rw [siftAux_succ_of_none hT] at h; exact absurd h (by simp)
      · rw [siftAux_succ_of_some hT] at h
        obtain ⟨p, hp, hr⟩ := ih (i + 1) (τ⁻¹ * σ) r h
        refine ⟨p * τ⁻¹, Subgroup.mul_mem _ hp
          (Subgroup.inv_mem _ (Subgroup.subset_closure (mem_allEntries hT))), ?_⟩
        rw [hr, mul_assoc]

/-- An element that sifts to the identity is a product of entries. -/
theorem mem_closure_of_mem_sifted {T : Table n} {k i : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : σ ∈ Sifted T k i) : σ ∈ Subgroup.closure (AllEntries T) := by
  obtain ⟨p, hp, hr⟩ := siftAux_residue T k i σ 1 h
  have hps : p * σ = 1 := hr.symm
  have hσ : σ = p⁻¹ := by
    have := congrArg (fun x => p⁻¹ * x) hps
    simpa [← mul_assoc] using this
  rw [hσ]
  exact Subgroup.inv_mem _ hp

/-- The group generated by the entries lies in `G`. -/
theorem closure_allEntries_le {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) : Subgroup.closure (AllEntries T) ≤ G := by
  rw [Subgroup.closure_le]
  rintro τ ⟨i, j, hij⟩
  exact hT.mem hij

/-- An element that sifts to the identity lies in `G`. -/
theorem mem_of_mem_sifted {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G)
    {k i : ℕ} {σ : Equiv.Perm (Fin n)} (h : σ ∈ Sifted T k i) : σ ∈ G :=
  closure_allEntries_le hT (mem_closure_of_mem_sifted h)

/-- **The residue fixes every level already passed.** -/
theorem siftAux_fixes {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G) :
    ∀ (k i : ℕ) (σ r : Equiv.Perm (Fin n)), Fixes i σ → siftAux T k i σ = some r →
      Fixes (i + k) r := by
  intro k
  induction k with
  | zero =>
      intro i σ r hfix h
      have hrs : r = σ := (Option.some.inj h).symm
      subst hrs
      simpa using hfix
  | succ k ih =>
      intro i σ r hfix h
      rcases hT2 : T i (evalAt σ i) with _ | τ
      · rw [siftAux_succ_of_none hT2] at h; exact absurd h (by simp)
      · rw [siftAux_succ_of_some hT2] at h
        have hfix' : Fixes (i + 1) (τ⁻¹ * σ) := by
          refine fixes_of_evalAt ?_
          intro m hm
          rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm' | rfl
          · rw [evalAt_mul, hfix.evalAt hm', (hT.fixes hT2).inv.evalAt hm']
          · rw [evalAt_mul, ← hT.img hT2, evalAt_inv_left]
        have hres := ih (i + 1) (τ⁻¹ * σ) r hfix' h
        have : i + 1 + k = i + (k + 1) := by omega
        rwa [this] at hres

/-- **A complete sift ends at the identity.**  So "`σ` sifts to the identity" and "the sift of
`σ` does not get stuck" say the same thing. -/
theorem siftAux_eq_some_eq_one {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) {k i : ℕ} (hk : i + k = n) {σ r : Equiv.Perm (Fin n)} (hfix : Fixes i σ)
    (h : siftAux T k i σ = some r) : r = 1 :=
  eq_one_of_fixes (hk ▸ siftAux_fixes hT k i σ r hfix h)

theorem sift_eq_some_eq_one {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G)
    {σ r : Equiv.Perm (Fin n)} (h : sift T σ = some r) : r = 1 :=
  siftAux_eq_some_eq_one hT (by omega) (fun _ hk => absurd hk (by omega)) h

/-- **An element that sifts to the identity from the level `i` fixes every level below `i`**,
because it is a product of entries of the rows `i, i+1, …`. -/
theorem sifted_fixes {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G) :
    ∀ (k i : ℕ) (σ : Equiv.Perm (Fin n)), σ ∈ Sifted T k i → Fixes i σ := by
  intro k
  induction k with
  | zero =>
      intro i σ h
      rw [mem_sifted_zero.1 h]
      exact fixes_one i
  | succ k ih =>
      intro i σ h
      obtain ⟨τ, hτ, hρ⟩ := mem_sifted_succ.1 h
      have h1 : Fixes i (τ⁻¹ * σ) := (ih (i + 1) _ hρ).mono (by omega)
      have h2 : σ = τ * (τ⁻¹ * σ) := by rw [← mul_assoc]; simp
      rw [h2]
      exact (hT.fixes hτ).mul h1

/-! ## The factorization of a sifted element

`Sifted T (k+1) i` is exactly the set of products `τρ` with `τ` an entry of row `i` and `ρ` a
sifted element of the next level, and the two factors are determined by the product.  This one
computation is behind both the order formula and the closure criterion. -/

/-- One step of sifting, read as a factorization. -/
theorem mem_sifted_succ_iff_mul {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) {k i : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ Sifted T (k + 1) i ↔ ∃ τ ∈ Entries T i, ∃ ρ ∈ Sifted T k (i + 1), σ = τ * ρ := by
  constructor
  · intro h
    obtain ⟨τ, hτ, hρ⟩ := mem_sifted_succ.1 h
    exact ⟨τ, mem_entries hτ, τ⁻¹ * σ, hρ, by rw [← mul_assoc]; simp⟩
  · rintro ⟨τ, ⟨j, hj⟩, ρ, hρ, rfl⟩
    have hfixρ : Fixes (i + 1) ρ := sifted_fixes hT k (i + 1) ρ hρ
    have himg : evalAt (τ * ρ) i = j := by
      rw [evalAt_mul, hfixρ.evalAt (by omega), hT.img hj]
    exact mem_sifted_succ.2 ⟨τ, by rw [himg]; exact hj, by rw [← mul_assoc]; simpa using hρ⟩

/-- **The two factors are determined by the product.** -/
theorem sifted_factor_unique {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) {k i : ℕ} {τ τ' ρ ρ' : Equiv.Perm (Fin n)} (hτ : τ ∈ Entries T i)
    (hτ' : τ' ∈ Entries T i) (hρ : ρ ∈ Sifted T k (i + 1)) (hρ' : ρ' ∈ Sifted T k (i + 1))
    (h : τ * ρ = τ' * ρ') : τ = τ' ∧ ρ = ρ' := by
  obtain ⟨j, hj⟩ := hτ
  obtain ⟨j', hj'⟩ := hτ'
  have h1 : evalAt (τ * ρ) i = j := by
    rw [evalAt_mul, (sifted_fixes hT k (i + 1) ρ hρ).evalAt (by omega), hT.img hj]
  have h2 : evalAt (τ' * ρ') i = j' := by
    rw [evalAt_mul, (sifted_fixes hT k (i + 1) ρ' hρ').evalAt (by omega), hT.img hj']
  have hjj : j = j' := by rw [← h1, ← h2, h]
  subst hjj
  have hττ : τ = τ' := Option.some.inj (hj ▸ hj')
  subst hττ
  exact ⟨rfl, by simpa using congrArg (fun x => τ⁻¹ * x) h⟩

/-! ## Membership

The first of the three textbook facts.  One direction is the residue lemma above; the other is
an induction along the levels, and it is the only place where completeness is used. -/

/-- Every element of `Gⁱ` sifts to the identity through a complete table. -/
theorem siftAux_eq_one_of_mem {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) (hC : Complete T G) :
    ∀ (k i : ℕ), i + k = n → ∀ σ ∈ chainStab G i, siftAux T k i σ = some 1 := by
  intro k
  induction k with
  | zero =>
      intro i hi σ hσ
      have hin : i = n := by omega
      subst hin
      have hσ1 : σ = 1 := eq_one_of_fixes (mem_chainStab.1 hσ).2
      rw [hσ1]
      exact siftAux_zero T i 1
  | succ k ih =>
      intro i hi σ hσ
      have hin : i < n := by omega
      rcases hτ : T i (evalAt σ i) with _ | τ
      · exact absurd hτ (hC i hin σ hσ)
      · rw [siftAux_succ_of_some hτ]
        refine ih (i + 1) (by omega) _ ?_
        refine mem_chainStab.2
          ⟨G.mul_mem (G.inv_mem (hT.mem hτ)) (mem_chainStab.1 hσ).1, fixes_of_evalAt ?_⟩
        intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm' | rfl
        · rw [evalAt_mul, (mem_chainStab.1 hσ).2.evalAt hm', (hT.fixes hτ).inv.evalAt hm']
        · rw [evalAt_mul, ← hT.img hτ, evalAt_inv_left]

/-- **Membership.**  For a complete table, `σ` lies in `G` exactly when `σ` sifts to the
identity. -/
theorem mem_iff_sift_eq_one {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) (hC : Complete T G) (σ : Equiv.Perm (Fin n)) :
    σ ∈ G ↔ sift T σ = some 1 := by
  constructor
  · intro hσ
    refine siftAux_eq_one_of_mem hT hC n 0 (by omega) σ ?_
    rw [chainStab_zero]
    exact hσ
  · intro h
    exact mem_of_mem_sifted hT (k := n) (i := 0) h

/-- The elements that sift to the identity are exactly the elements of `G`. -/
theorem sifted_eq_carrier {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) : Sifted T n 0 = (G : Set (Equiv.Perm (Fin n))) := by
  ext σ
  exact (mem_iff_sift_eq_one hT hC σ).symm

/-! ## A complete table exists

Nothing above is vacuous: every `G` has a complete table, with the identity on the diagonal.
The table is built by choice, so it is noncomputable; the raw routines of
`Workspace/Algo/ChainRaw.lean` build one by sifting instead. -/

open Classical in
/-- **The full table of `G`**: the identity on the diagonal, and elsewhere any element of `Gⁱ`
that sends `i` to `j`, when there is one. -/
noncomputable def fullTable (G : Subgroup (Equiv.Perm (Fin n))) : Table n := fun i j =>
  if j = i then some 1
  else if h : ∃ τ : Equiv.Perm (Fin n), τ ∈ chainStab G i ∧ evalAt τ i = j then some h.choose
  else none

theorem fullTable_diag (G : Subgroup (Equiv.Perm (Fin n))) (i : ℕ) : fullTable G i i = some 1 := by
  rw [fullTable, if_pos rfl]

theorem isTable_fullTable (G : Subgroup (Equiv.Perm (Fin n))) : IsTable (fullTable G) G := by
  classical
  have key : ∀ (i j : ℕ) (τ : Equiv.Perm (Fin n)), fullTable G i j = some τ →
      τ ∈ chainStab G i ∧ evalAt τ i = j := by
    intro i j τ h
    rw [fullTable] at h
    by_cases hji : j = i
    · rw [if_pos hji] at h
      subst hji
      have : τ = 1 := (Option.some.inj h).symm
      subst this
      exact ⟨Subgroup.one_mem _, by simp⟩
    · rw [if_neg hji] at h
      by_cases hex : ∃ τ : Equiv.Perm (Fin n), τ ∈ chainStab G i ∧ evalAt τ i = j
      · rw [dif_pos hex] at h
        have : τ = hex.choose := (Option.some.inj h).symm
        subst this
        exact hex.choose_spec
      · rw [dif_neg hex] at h
        exact absurd h (by simp)
  exact ⟨fun h => ((key _ _ _ h).1).1, fun h => ((key _ _ _ h).1).2, fun h => (key _ _ _ h).2⟩

theorem complete_fullTable (G : Subgroup (Equiv.Perm (Fin n))) : Complete (fullTable G) G := by
  classical
  intro i _ σ hσ
  by_cases h : evalAt σ i = i
  · rw [h, fullTable_diag]; simp
  · rw [fullTable, if_neg h, dif_pos ⟨σ, hσ, rfl⟩]
    simp

/-- **A complete table exists for every group.**  So the three theorems of this file are not
vacuous. -/
theorem exists_complete_table (G : Subgroup (Equiv.Perm (Fin n))) :
    ∃ T : Table n, IsTable T G ∧ Complete T G ∧ ∀ i < n, T i i = some 1 :=
  ⟨fullTable G, isTable_fullTable G, complete_fullTable G, fun i _ => fullTable_diag G i⟩

/-! ## The order

The second textbook fact.  Row `i` has one entry per point of the `Gⁱ`-orbit of `i`, and the
factorization above turns the sifted elements of one level into pairs (entry of the row, sifted
element of the next level).  So the number of sifted elements is the product of the row
sizes. -/

open Classical in
/-- The filled positions of row `i`. -/
noncomputable def row (T : Table n) (i : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun j => T i j ≠ none)

open Classical in
/-- The elements that sift to the identity, as a finite set. -/
noncomputable def siftedFinset (T : Table n) (k i : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ ∈ Sifted T k i)

theorem mem_row {T : Table n} {i j : ℕ} : j ∈ row T i ↔ j < n ∧ T i j ≠ none := by
  classical
  rw [row]
  simp

theorem mem_siftedFinset {T : Table n} {k i : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ siftedFinset T k i ↔ σ ∈ Sifted T k i := by
  classical
  rw [siftedFinset]
  simp

/-- **One level of the order formula.** -/
theorem card_siftedFinset_succ {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) {k i : ℕ} (hi : i < n) :
    (siftedFinset T (k + 1) i).card = (row T i).card * (siftedFinset T k (i + 1)).card := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_nbij'
    (fun σ => (evalAt σ i, ((T i (evalAt σ i)).getD 1)⁻¹ * σ))
    (fun p => (T i p.1).getD 1 * p.2) ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_coe, mem_siftedFinset] at hσ
    obtain ⟨τ, hτ, hρ⟩ := mem_sifted_succ.1 hσ
    rw [Finset.mem_coe, Finset.mem_product]
    dsimp only
    refine ⟨mem_row.2 ⟨evalAt_lt σ hi, by rw [hτ]; simp⟩, ?_⟩
    rw [mem_siftedFinset, hτ]
    simpa using hρ
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_row] at hp1
    rw [mem_siftedFinset] at hp2
    rcases hτ : T i p.1 with _ | τ
    · exact absurd hτ hp1.2
    · rw [Finset.mem_coe, mem_siftedFinset]
      dsimp only
      refine (mem_sifted_succ_iff_mul hT).2 ⟨τ, mem_entries hτ, p.2, hp2, by rw [hτ]; simp⟩
  · intro σ hσ
    rw [Finset.mem_coe, mem_siftedFinset] at hσ
    obtain ⟨τ, hτ, _⟩ := mem_sifted_succ.1 hσ
    dsimp only
    simp only [hτ, Option.getD_some]
    rw [← mul_assoc]
    simp
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_row] at hp1
    rw [mem_siftedFinset] at hp2
    rcases hτ : T i p.1 with _ | τ
    · exact absurd hτ hp1.2
    · have himg : evalAt (τ * p.2) i = p.1 := by
        rw [evalAt_mul, (sifted_fixes hT k (i + 1) p.2 hp2).evalAt (by omega), hT.img hτ]
      dsimp only
      rw [hτ]
      simp only [Option.getD_some]
      rw [himg, hτ]
      simp only [Option.getD_some]
      rw [← mul_assoc]
      simp

/-- The sifted elements of the last level are just the identity. -/
theorem siftedFinset_zero (T : Table n) (i : ℕ) : siftedFinset T 0 i = {1} := by
  classical
  ext σ
  rw [mem_siftedFinset, mem_sifted_zero, Finset.mem_singleton]

/-- **The number of sifted elements is the product of the row sizes.** -/
theorem card_siftedFinset {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))} (hT : IsTable T G) :
    ∀ (k i : ℕ), i + k = n →
      (siftedFinset T k i).card = ∏ j ∈ Finset.Ico i n, (row T j).card := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have : i = n := by omega
      subst this
      rw [siftedFinset_zero, Finset.card_singleton, Finset.Ico_self, Finset.prod_empty]
  | succ k ih =>
      intro i hi
      have hin : i < n := by omega
      rw [card_siftedFinset_succ hT hin, ih (i + 1) (by omega),
        Finset.prod_eq_prod_Ico_succ_bot hin]

/-- **The order.**  For a complete table, `|G|` is the product over the levels of the number of
filled positions in each row. -/
theorem card_eq_prod_row_card {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsTable T G) (hC : Complete T G) :
    Nat.card G = ∏ i ∈ Finset.range n, (row T i).card := by
  classical
  have hset : (G : Set (Equiv.Perm (Fin n))) = ↑(siftedFinset T n 0) := by
    ext σ
    rw [Finset.mem_coe, mem_siftedFinset, sifted_eq_carrier hT hC]
  calc Nat.card G = (G : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
    _ = ((siftedFinset T n 0 : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))).ncard :=
        by rw [hset]
    _ = (siftedFinset T n 0).card := Set.ncard_coe_finset _
    _ = ∏ j ∈ Finset.Ico 0 n, (row T j).card := card_siftedFinset hT n 0 (by omega)
    _ = ∏ i ∈ Finset.range n, (row T i).card := by rw [← Finset.range_eq_Ico]

/-! ## The closure criterion

The third textbook fact, and the one that makes the construction of a table terminate: a table
that is *closed* — the generators sift to the identity, and so does the product of any two
entries — is complete.

The proof is a downward induction along the levels: the set of elements that sift to the
identity from the level `i` is closed under multiplication.  The step needs an inner induction,
which is the claim `hA` below: multiplying a sifted element of the next level by an entry of
row `i` stays sifted.  The set of elements for which that holds contains the identity, is
closed under multiplication, and contains every entry of a deeper row — for an entry, the
product with an entry of row `i` sifts to the identity by hypothesis — and every sifted element
of the next level is a product of entries of deeper rows. -/

/-- A finite group is a group already when a subset containing the identity is closed under
multiplication: the inverse of `a` is a power of `a`. -/
def subgroupOfMulClosed {H : Type*} [Group H] [Finite H] (M : Set H) (h1 : (1 : H) ∈ M)
    (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) : Subgroup H where
  carrier := M
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := by
    intro a ha
    have hpow : ∀ m : ℕ, a ^ m ∈ M := by
      intro m
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ]; exact hmul _ ih _ ha
    have hord : 0 < orderOf a := orderOf_pos a
    have hmul1 : a ^ (orderOf a - 1) * a = 1 := by
      rw [← pow_succ]
      have : orderOf a - 1 + 1 = orderOf a := by omega
      rw [this, pow_orderOf_eq_one]
    have : a ^ (orderOf a - 1) = a⁻¹ := by
      have := congrArg (fun x => x * a⁻¹) hmul1
      simpa [mul_assoc] using this
    rw [← this]
    exact hpow _

section Closed

variable {T : Table n} {G : Subgroup (Equiv.Perm (Fin n))}

/-- With the identity on the diagonal, the identity sifts to the identity. -/
theorem one_mem_sifted (hdiag : ∀ i < n, T i i = some 1) :
    ∀ (k i : ℕ), i + k ≤ n → (1 : Equiv.Perm (Fin n)) ∈ Sifted T k i := by
  intro k
  induction k with
  | zero => intro i _; exact mem_sifted_zero.2 rfl
  | succ k ih =>
      intro i hi
      refine mem_sifted_succ.2 ⟨1, ?_, ?_⟩
      · rw [evalAt_one, hdiag i (by omega)]
      · simpa using ih (i + 1) (by omega)

/-- An element sifted from the level `i + 1` is sifted from the level `i` as well: at the level
`i` it meets the identity on the diagonal. -/
theorem mem_sifted_pred (hT : IsTable T G) (hdiag : ∀ i < n, T i i = some 1) {k i : ℕ}
    (hi : i < n) {σ : Equiv.Perm (Fin n)} (h : σ ∈ Sifted T k (i + 1)) :
    σ ∈ Sifted T (k + 1) i := by
  refine mem_sifted_succ.2 ⟨1, ?_, by simpa using h⟩
  rw [(sifted_fixes hT k (i + 1) σ h).evalAt (by omega), hdiag i hi]

/-- Sifting from a level reaches down to the level `0`. -/
theorem mem_sifted_zero_of (hT : IsTable T G) (hdiag : ∀ i < n, T i i = some 1) :
    ∀ (i k : ℕ), i + k = n → ∀ σ ∈ Sifted T k i, σ ∈ Sifted T n 0 := by
  intro i
  induction i with
  | zero => intro k hk σ hσ; rwa [show k = n by omega] at hσ
  | succ i ih =>
      intro k hk σ hσ
      exact ih (k + 1) (by omega) σ (mem_sifted_pred hT hdiag (by omega) hσ)

/-- And back up, for an element that fixes the levels already passed. -/
theorem mem_sifted_of_fixes (hdiag : ∀ i < n, T i i = some 1) :
    ∀ (i k : ℕ), i + k = n → ∀ σ : Equiv.Perm (Fin n), Fixes i σ → σ ∈ Sifted T n 0 →
      σ ∈ Sifted T k i := by
  intro i
  induction i with
  | zero => intro k hk σ _ hσ; rwa [show k = n by omega]
  | succ i ih =>
      intro k hk σ hfix hσ
      have h1 : σ ∈ Sifted T (k + 1) i := ih (k + 1) (by omega) σ (hfix.mono (by omega)) hσ
      obtain ⟨τ, hτ, hρ⟩ := mem_sifted_succ.1 h1
      have h2 : T i (evalAt σ i) = some 1 := by
        rw [hfix.evalAt (by omega), hdiag i (by omega)]
      have hτ1 : τ = 1 := (Option.some.inj (h2.symm.trans hτ)).symm
      subst hτ1
      simpa using hρ

/-- **The closure step.**  The elements that sift to the identity from one level are closed
under multiplication, given that the elements of the next level are. -/
theorem sifted_mul_mem (hT : IsTable T G) (hdiag : ∀ i < n, T i i = some 1)
    (hprod : ∀ τ ∈ AllEntries T, ∀ ρ ∈ AllEntries T, sift T (τ * ρ) = some 1) :
    ∀ (k i : ℕ), i + k = n → ∀ a ∈ Sifted T k i, ∀ b ∈ Sifted T k i, a * b ∈ Sifted T k i := by
  intro k
  induction k with
  | zero =>
      intro i _ a ha b hb
      rw [mem_sifted_zero.1 ha, mem_sifted_zero.1 hb]
      exact mem_sifted_zero.2 (by simp)
  | succ k ih =>
      intro i hi a ha b hb
      have hin : i < n := by omega
      have hik : i + 1 + k = n := by omega
      -- products of two entries, when they fix the levels below `i`
      have hpair : ∀ τ ∈ AllEntries T, ∀ ρ ∈ AllEntries T, Fixes i (τ * ρ) →
          τ * ρ ∈ Sifted T (k + 1) i := by
        intro τ hτ ρ hρ hfix
        exact mem_sifted_of_fixes hdiag i (k + 1) hi _ hfix (hprod τ hτ ρ hρ)
      -- every entry of row `i` sifts to the identity from the level `i`
      have hrow : ∀ τ ∈ Entries T i, τ ∈ Sifted T (k + 1) i := by
        rintro τ ⟨j, hj⟩
        refine (mem_sifted_succ_iff_mul hT).2 ⟨τ, mem_entries hj, 1, ?_, by simp⟩
        exact one_mem_sifted hdiag k (i + 1) (by omega)
      -- the inner claim: a sifted element of the next level may be multiplied by an entry
      have hA : ∀ (k' i' : ℕ), i' + k' = n → i + 1 ≤ i' → ∀ c ∈ Sifted T k' i',
          ∀ ρ ∈ Entries T i, c * ρ ∈ Sifted T (k + 1) i := by
        intro k'
        induction k' with
        | zero =>
            intro i' _ _ c hc ρ hρ
            rw [mem_sifted_zero.1 hc, one_mul]
            exact hrow ρ hρ
        | succ k'' ih' =>
            intro i' hi' hle c hc ρ hρ
            obtain ⟨τ, hτ, d, hd, rfl⟩ := (mem_sifted_succ_iff_mul hT).1 hc
            -- `τ` is an entry of a deeper row, and `d` is handled by the inner induction
            have hd' : d * ρ ∈ Sifted T (k + 1) i := ih' (i' + 1) (by omega) (by omega) d hd ρ hρ
            obtain ⟨τ₁, hτ₁, e, he, hde⟩ := (mem_sifted_succ_iff_mul hT).1 hd'
            obtain ⟨j₁, hj₁⟩ := hτ₁
            obtain ⟨j, hj⟩ := hτ
            have hττ : τ * τ₁ ∈ Sifted T (k + 1) i := by
              refine hpair τ (mem_allEntries hj) τ₁ (mem_allEntries hj₁) ?_
              exact ((hT.fixes hj).mono (by omega)).mul (hT.fixes hj₁)
            obtain ⟨τ₂, hτ₂, f, hf, hτf⟩ := (mem_sifted_succ_iff_mul hT).1 hττ
            have hcalc : τ * d * ρ = τ₂ * (f * e) := by
              rw [mul_assoc, hde, ← mul_assoc, hτf, mul_assoc]
            rw [hcalc]
            exact (mem_sifted_succ_iff_mul hT).2
              ⟨τ₂, hτ₂, f * e, ih (i + 1) hik f hf e he, rfl⟩
      -- now the step itself
      obtain ⟨τ, hτ, c, hc, rfl⟩ := (mem_sifted_succ_iff_mul hT).1 ha
      obtain ⟨τ', hτ', c', hc', rfl⟩ := (mem_sifted_succ_iff_mul hT).1 hb
      have h1 : c * τ' ∈ Sifted T (k + 1) i := hA k (i + 1) hik (by omega) c hc τ' hτ'
      obtain ⟨τ₃, hτ₃, e, he, hce⟩ := (mem_sifted_succ_iff_mul hT).1 h1
      obtain ⟨j, hj⟩ := hτ
      obtain ⟨j₃, hj₃⟩ := hτ₃
      have h2 : τ * τ₃ ∈ Sifted T (k + 1) i :=
        hpair τ (mem_allEntries hj) τ₃ (mem_allEntries hj₃) ((hT.fixes hj).mul (hT.fixes hj₃))
      obtain ⟨τ₄, hτ₄, f, hf, hτf⟩ := (mem_sifted_succ_iff_mul hT).1 h2
      have hcalc : τ * c * (τ' * c') = τ₄ * (f * (e * c')) := by
        rw [mul_assoc τ c, ← mul_assoc c, hce, mul_assoc τ₃ e, ← mul_assoc τ, hτf,
          mul_assoc τ₄ f]
      rw [hcalc]
      exact (mem_sifted_succ_iff_mul hT).2
        ⟨τ₄, hτ₄, f * (e * c'), ih (i + 1) hik f hf _ (ih (i + 1) hik e he c' hc'), rfl⟩

/-- **The closure criterion** (Sims; Furst–Hopcroft–Luks).  A table whose entries lie in `G`,
whose diagonal holds the identity, through which every generator of `G` sifts to the identity,
and through which the product of any two entries sifts to the identity, is complete for `G`.

The diagonal hypothesis cannot be dropped: see the header of this file. -/
theorem complete_of_closed (hT : IsTable T G) (hdiag : ∀ i < n, T i i = some 1)
    {S : Set (Equiv.Perm (Fin n))} (hG : G = Subgroup.closure S)
    (hgen : ∀ g ∈ S, sift T g = some 1)
    (hprod : ∀ τ ∈ AllEntries T, ∀ ρ ∈ AllEntries T, sift T (τ * ρ) = some 1) :
    Complete T G := by
  classical
  -- the elements that sift to the identity form a subgroup
  have hone : (1 : Equiv.Perm (Fin n)) ∈ Sifted T n 0 := one_mem_sifted hdiag n 0 (by omega)
  have hmul : ∀ a ∈ Sifted T n 0, ∀ b ∈ Sifted T n 0, a * b ∈ Sifted T n 0 :=
    sifted_mul_mem hT hdiag hprod n 0 (by omega)
  set M : Subgroup (Equiv.Perm (Fin n)) := subgroupOfMulClosed (Sifted T n 0) hone hmul with hM
  have hGM : G ≤ M := by
    rw [hG, Subgroup.closure_le]
    intro g hg
    exact hgen g hg
  intro i hin σ hσ
  have hσM : σ ∈ Sifted T n 0 := hGM (mem_chainStab.1 hσ).1
  have hfix : Fixes i σ := (mem_chainStab.1 hσ).2
  have hn : i + (n - i) = n := by omega
  have hσi : σ ∈ Sifted T (n - i) i := mem_sifted_of_fixes hdiag i (n - i) hn σ hfix hσM
  have hk : n - i = (n - i - 1) + 1 := by omega
  rw [hk] at hσi
  obtain ⟨τ, hτ, _⟩ := mem_sifted_succ.1 hσi
  rw [hτ]
  simp

/-- The full table of `G` satisfies the hypotheses of the closure criterion, for any generating
set: so `Algo.complete_of_closed` is not vacuous either. -/
theorem fullTable_closed (G : Subgroup (Equiv.Perm (Fin n)))
    {S : Set (Equiv.Perm (Fin n))} (hG : G = Subgroup.closure S) :
    (∀ g ∈ S, sift (fullTable G) g = some 1) ∧
      ∀ τ ∈ AllEntries (fullTable G), ∀ ρ ∈ AllEntries (fullTable G),
        sift (fullTable G) (τ * ρ) = some 1 := by
  have hT := isTable_fullTable G
  have hC := complete_fullTable G
  refine ⟨fun g hg => (mem_iff_sift_eq_one hT hC g).1 ?_, fun τ hτ ρ hρ => ?_⟩
  · rw [hG]; exact Subgroup.subset_closure hg
  · obtain ⟨i, j, hij⟩ := hτ
    obtain ⟨i', j', hij'⟩ := hρ
    exact (mem_iff_sift_eq_one hT hC _).1 (G.mul_mem (hT.mem hij) (hT.mem hij'))

end Closed

end Algo
