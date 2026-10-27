/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: coset representatives of a kernel, indexed in binary along a
stabilizer chain (Proposition 2.2.6 (a), and the representatives Proposition 11.1.6 uses).
-/
import Workspace.Algo.Labelled
import Workspace.Machine.Div

/-!
# Coset representatives indexed in binary

Proposition 11.1.6 lets `σ` range over coset representatives of `H` in `G`.  Session 3 of
work package A7 produced them by a breadth-first search (`Algo.rawCosetReps`), whose running
time is polynomial in the *length* of the index list it is handed, so the index had to travel
in unary and a descent instance was as large as the multiplicative cost of the round.

This file replaces the search, for the only subgroup the paper ever descends to: the **kernel
of an action** (Theorem 11.1.9 descends to `N = ker(G → S(ℬ))`; Proposition 2.2.6 (a)).  Here
the action is the restriction to a window `Δ`, whose kernel is the pointwise stabilizer
`G_{(Δ)}` (`Algo.mem_ker_winRestrictHom`).

The device is the one `Workspace/Algo/Labelled.lean` already uses: conjugating by
`Algo.rawOrd (dom, Δ)` makes `Δ` the initial segment `{0, …, |Δ|−1}`, so `G_{(Δ)}` becomes the
`|Δ|`-th group `Ĝ^{(|Δ|)}` of the ordinary stabilizer chain of `Ĝ = ρ⁻¹Gρ`.  Row `i` of the
table is a transversal of `Ĝ^{(i+1)}` in `Ĝ^{(i)}` (`Algo.rowPerms_transversal`), so a
representative of `Ĝ^{(|Δ|)}` in `Ĝ` is a product of one entry per level, and the products are
indexed by the **mixed-radix digits** of a number `j`, the radices being the row lengths.  The
index `j` therefore travels in binary: the routine is polynomial in the size of the input plus
`log j`.

## Main definitions

* `Algo.chainRadix`, `Algo.chainIndex`, `Algo.chainRep`, `Algo.chainQuot` — the mixed-radix
  representative of `G^{(i+k)}` in `G^{(i)}` and the number of them;
* `Algo.ordConjGens`, `Algo.winCosetRep`, `Algo.winCosetIndex` — the same after the base
  reordering, so for the kernel `G_{(Δ)}`;
* `Algo.rawRowAt`, `Algo.rawChainStep`, `Algo.rawChainFold`, `Algo.rawWinChainRep`,
  `Algo.rawCosetRepBin` — the routines;
* `Algo.rawKerGens` — generators of the kernel.

## Main results

* `Algo.chainRep_cover` — every element of `G^{(i)}` lies in one of the `chainIndex` cosets;
* `Algo.cover_winCosetRep` — **Proposition 2.2.6 (a)**, the covering half: `G` is the union of
  the `Algo.winCosetIndex` left cosets `σ_j · G_{(Δ)}`;
* `Algo.decGroup_rawKerGens`, `Algo.length_rawKerGens_le` — **Proposition 2.2.6 (a)**, the
  kernel itself: a short generating list of `ker(G → S(Δ))`, computed by a `RAM.PolyFun`;
* `Algo.rawCosetRepBin_spec` — the routine computes `σ_j`;
* `Algo.polyFun_rawCosetRepBin`, `Algo.polyFun_rawKerGens` — the running times.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The mixed-radix representative, as mathematics -/

/-- **The radix at the level `i`**: the number of entries of row `i` of the table, that is the
length of the orbit of the level `i` under `G^{(i)}`. -/
def chainRadix (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) : ℕ := (rowPerms n gens i).length

/-- **The number of representatives of `G^{(i+k)}` in `G^{(i)}`**: the product of the radices
of the `k` levels from `i` on. -/
def chainIndex (n : ℕ) (gens : List (Perm (Fin n))) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | i, (k + 1) => chainRadix n gens i * chainIndex n gens (i + 1) k

/-- **The `j`-th representative of `G^{(i+k)}` in `G^{(i)}`**: the product of one entry per
level, the entry at the level `i` being the one selected by the `i`-th mixed-radix digit
of `j`.  Paper: "`σ` ranges over a set of coset representatives" (Prop. 11.1.6). -/
def chainRep (n : ℕ) (gens : List (Perm (Fin n))) : ℕ → ℕ → ℕ → Perm (Fin n)
  | _, 0, _ => 1
  | i, (k + 1), j =>
      (rowPerms n gens i).getD (j % chainRadix n gens i) 1
        * chainRep n gens (i + 1) k (j / chainRadix n gens i)

/-- The index left over after the `k` digits have been read off. -/
def chainQuot (n : ℕ) (gens : List (Perm (Fin n))) : ℕ → ℕ → ℕ → ℕ
  | _, 0, j => j
  | i, (k + 1), j => chainQuot n gens (i + 1) k (j / chainRadix n gens i)

@[simp] theorem chainIndex_zero (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) :
    chainIndex n gens i 0 = 1 := rfl

@[simp] theorem chainRep_zero (n : ℕ) (gens : List (Perm (Fin n))) (i j : ℕ) :
    chainRep n gens i 0 j = 1 := rfl

@[simp] theorem chainQuot_zero (n : ℕ) (gens : List (Perm (Fin n))) (i j : ℕ) :
    chainQuot n gens i 0 j = j := rfl

theorem chainIndex_succ (n : ℕ) (gens : List (Perm (Fin n))) (i k : ℕ) :
    chainIndex n gens i (k + 1) = chainRadix n gens i * chainIndex n gens (i + 1) k := rfl

theorem chainRep_succ (n : ℕ) (gens : List (Perm (Fin n))) (i k j : ℕ) :
    chainRep n gens i (k + 1) j
      = (rowPerms n gens i).getD (j % chainRadix n gens i) 1
          * chainRep n gens (i + 1) k (j / chainRadix n gens i) := rfl

theorem chainQuot_succ (n : ℕ) (gens : List (Perm (Fin n))) (i k j : ℕ) :
    chainQuot n gens i (k + 1) j
      = chainQuot n gens (i + 1) k (j / chainRadix n gens i) := rfl

theorem chainQuot_le (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ (k i j : ℕ), chainQuot n gens i k j ≤ j := by
  intro k
  induction k with
  | zero => intro i j; exact le_rfl
  | succ k ih =>
      intro i j
      exact le_trans (ih (i + 1) (j / chainRadix n gens i)) (Nat.div_le_self _ _)

/-- **A radix is at most the degree**: a row of the table has at most `n` entries, because its
keys are distinct points of the domain (the shape invariant `Algo.Shape`). -/
theorem chainRadix_le (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) : chainRadix n gens i ≤ n := by
  have hsh := shape_buildTable n gens
  set row := (buildTable n gens).getD i ([] : MRow n) with hrow
  have hlen : row.length ≤ n := by
    by_cases hi : i < (buildTable n gens).length
    · have hmem : row ∈ buildTable n gens := by
        rw [hrow, List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      have hnd := hsh.nodup row hmem
      have hlt : ∀ x ∈ row.map Prod.fst, x < n := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact hsh.keys row hmem q hq
      have := length_le_of_nodup_lt hnd hlt
      rwa [List.length_map] at this
    · rw [hrow, List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Nat.zero_le _
  rw [chainRadix, rowPerms, List.length_map]
  exact hlen

/-- **The number of representatives is at most `n^k`.** -/
theorem chainIndex_le_pow (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ (k i : ℕ), chainIndex n gens i k ≤ n ^ k := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
      intro i
      rw [chainIndex_succ, pow_succ, Nat.mul_comm (n ^ k) n]
      exact Nat.mul_le_mul (chainRadix_le n gens i) (ih (i + 1))

/-- **Row `i` lies in `G^{(i)}`.** -/
theorem rowPerms_subset_chainStab (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) {τ : Perm (Fin n)}
    (h : τ ∈ rowPerms n gens i) : τ ∈ chainStab (genGroup gens) i := by
  refine entries_subset_chainStab (isTable_buildTable n gens) i ?_
  rw [entries_eq_row (shape_buildTable n gens) i]
  exact h

/-- A `List.getD` is either an entry of the list or the default. -/
theorem getD_mem_or_eq {α : Type*} (l : List α) (m : ℕ) (d : α) :
    l.getD m d ∈ l ∨ l.getD m d = d := by
  by_cases hm : m < l.length
  · rw [List.getD_eq_getElem _ _ hm]
    exact Or.inl (List.getElem_mem hm)
  · exact Or.inr (List.getD_eq_default _ _ (Nat.le_of_not_lt hm))

/-- **The representatives lie in `G^{(i)}`.** -/
theorem chainRep_mem (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ (k i j : ℕ), chainRep n gens i k j ∈ chainStab (genGroup gens) i := by
  intro k
  induction k with
  | zero => intro i j; exact Subgroup.one_mem _
  | succ k ih =>
      intro i j
      rw [chainRep_succ]
      refine Subgroup.mul_mem _ ?_ ?_
      · rcases getD_mem_or_eq (rowPerms n gens i) (j % chainRadix n gens i) 1 with h | h
        · exact rowPerms_subset_chainStab n gens i h
        · rw [h]; exact Subgroup.one_mem _
      · exact chainStab_mono (Nat.le_succ i) (ih (i + 1) (j / chainRadix n gens i))

/-- **The mixed-radix representatives cover `G^{(i)}`.**  Every element of `G^{(i)}` lies in
the left coset `σ_j · G^{(i+k)}` of one of the `Algo.chainIndex` representatives.

*Proof.*  Row `i` is a transversal of `G^{(i+1)}` in `G^{(i)}`
(`Algo.rowPerms_transversal`), so `σ = τ ρ` with `τ` the `m`-th entry of row `i` and
`ρ ∈ G^{(i+1)}`; the induction hypothesis writes `ρ` with an index `j'`, and
`j = m + (row length) · j'` has the digits `m` and those of `j'`. -/
theorem chainRep_cover (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ (k i : ℕ), i + k ≤ n → ∀ σ ∈ chainStab (genGroup gens) i,
      ∃ j < chainIndex n gens i k,
        σ ∈ chainRep n gens i k j • (chainStab (genGroup gens) (i + k) : Set (Perm (Fin n))) := by
  intro k
  induction k with
  | zero =>
      intro i _ σ hσ
      refine ⟨0, by simp, ?_⟩
      rw [chainRep_zero, Nat.add_zero, one_smul]
      exact hσ
  | succ k ih =>
      intro i hik σ hσ
      have hin : i < n := by omega
      obtain ⟨p, ⟨hτ, hρ, hprod⟩, -⟩ :=
        rowPerms_transversal n gens (i := i) (k := n - i - 1) (by omega) hσ
      obtain ⟨m, hm, hmτ⟩ := List.getElem_of_mem hτ
      obtain ⟨j', hj', hmem⟩ := ih (i + 1) (by omega) p.2 hρ
      set r := chainRadix n gens i with hr
      have hmr : m < r := by rw [hr, chainRadix]; exact hm
      have hrpos : 0 < r := by omega
      refine ⟨m + r * j', ?_, ?_⟩
      · rw [chainIndex_succ, ← hr]
        calc m + r * j' < r + r * j' := by omega
          _ = r * (j' + 1) := by ring
          _ ≤ r * chainIndex n gens (i + 1) k := Nat.mul_le_mul_left _ (by omega)
      · have hmod : (m + r * j') % r = m := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmr]
        have hdiv : (m + r * j') / r = j' := by
          rw [Nat.add_mul_div_left _ _ hrpos, Nat.div_eq_of_lt hmr, Nat.zero_add]
        rw [chainRep_succ, ← hr, hmod, hdiv, List.getD_eq_getElem _ _ hm, hmτ]
        have hia : i + (k + 1) = (i + 1) + k := by omega
        rw [hia]
        rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem ⊢
        rw [hprod]
        have : (p.1 * chainRep n gens (i + 1) k j')⁻¹ * (p.1 * p.2)
            = (chainRep n gens (i + 1) k j')⁻¹ * p.2 := by group
        simpa [smul_eq_mul] using (by simpa [smul_eq_mul, this] using hmem :
          (p.1 * chainRep n gens (i + 1) k j')⁻¹ * (p.1 * p.2)
            ∈ (chainStab (genGroup gens) (i + 1 + k) : Set (Perm (Fin n))))

/-! ## After the base reordering: the kernel of the restriction to a window

The kernel of `Algo.winRestrictHom` is the pointwise stabilizer `G_{(Δ)}`
(`Algo.mem_ker_winRestrictHom`).  Conjugating the generators by `Algo.rawOrd (dom, Δ)` turns
`G_{(Δ)}` into the `|Δ|`-th group of the chain, so the representatives above apply. -/

variable {dom Δ : List ℕ}

/-- The generators conjugated so that the window is the initial segment `{0, …, |Δ|−1}`. -/
noncomputable def ordConjGens (n : ℕ) (dom Δ : List ℕ) (gens : List (Perm (Fin n))) :
    List (Perm (Fin n)) :=
  gens.map (fun g => (MulAut.conj (decPerm n (rawOrd (dom, Δ)))⁻¹) g)

/-- **The `j`-th coset representative of the kernel `G_{(Δ)}` in `G`.** -/
noncomputable def winCosetRep (n : ℕ) (dom Δ : List ℕ) (gens : List (Perm (Fin n))) (j : ℕ) :
    Perm (Fin n) :=
  decPerm n (rawOrd (dom, Δ)) * chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j
    * (decPerm n (rawOrd (dom, Δ)))⁻¹

/-- **The number of coset representatives of `G_{(Δ)}` in `G`**, that is `|G : G_{(Δ)}|`. -/
noncomputable def winCosetIndex (n : ℕ) (dom Δ : List ℕ) (gens : List (Perm (Fin n))) : ℕ :=
  chainIndex n (ordConjGens n dom Δ gens) 0 Δ.length

section Window

variable {gens : List (Perm (Fin n))}

/-- **The index of the kernel fits in `n²+1` bits.**  It is at most `n^n`, and `n ≤ 2^n`. -/
theorem size_winCosetIndex_le (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    Nat.size (winCosetIndex n dom Δ gens) ≤ n * n + 1 := by
  have hk : Δ.length ≤ n := length_le_of_nodup hnd hlt
  have h1 : winCosetIndex n dom Δ gens ≤ n ^ Δ.length :=
    chainIndex_le_pow n (ordConjGens n dom Δ gens) Δ.length 0
  have h2 : n ^ Δ.length ≤ n ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : Δ.length = 0 := Nat.le_zero.1 hk
      rw [this]
    · exact Nat.pow_le_pow_right hn hk
  have h3 : n ^ n ≤ 2 ^ (n * n) := by
    calc n ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) n
      _ = 2 ^ (n * n) := by rw [← pow_mul]
  refine Nat.size_le.2 ?_
  calc winCosetIndex n dom Δ gens ≤ 2 ^ (n * n) := le_trans h1 (le_trans h2 h3)
    _ < 2 ^ (n * n + 1) := by
        exact Nat.pow_lt_pow_right (by omega) (by omega)


theorem genGroup_ordConjGens (dom Δ : List ℕ) (gens : List (Perm (Fin n))) :
    genGroup (ordConjGens n dom Δ gens)
      = (genGroup gens).map (MulAut.conj (decPerm n (rawOrd (dom, Δ)))⁻¹).toMonoidHom := by
  rw [ordConjGens, genGroup_map_conj]

/-- **The `|Δ|`-th group of the chain of the conjugated group is the conjugate of the
kernel.** -/
theorem chainStab_ordConjGens (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    chainStab (genGroup (ordConjGens n dom Δ gens)) Δ.length
      = (Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ}).map
          (MulAut.conj (decPerm n (rawOrd (dom, Δ)))⁻¹).toMonoidHom := by
  set ρ := decPerm n (rawOrd (dom, Δ)) with hρ
  have himg : (ρ⁻¹ : Perm (Fin n)) '' {x : Fin n | (x : ℕ) ∈ Δ}
      = {x : Fin n | (x : ℕ) < Δ.length} := by
    rw [← image_decPerm_rawOrd hdom hnd hlt, ← hρ, ← Set.image_comp]
    simp
  rw [chainStab_eq_pointwiseStabilizer, genGroup_ordConjGens, ← himg,
    ← pointwiseStabilizer_map_conj]

/-- **Proposition 2.2.6 (a), the covering half** (§2.2.3): `G` is the union of the
`Algo.winCosetIndex` left cosets of the kernel `G_{(Δ)} = ker(G → S(Δ))`, with the explicit
representatives `Algo.winCosetRep`.  This is the decomposition `G = ⋃_σ σH` that the proof of
Proposition 11.1.6 uses. -/
theorem cover_winCosetRep (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    (genGroup gens : Set (Perm (Fin n)))
      = ⋃ j ∈ List.range (winCosetIndex n dom Δ gens),
          winCosetRep n dom Δ gens j
            • (Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ} :
                Set (Perm (Fin n))) := by
  set ρ := decPerm n (rawOrd (dom, Δ)) with hρ
  set K := Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ} with hK
  have hcs := chainStab_ordConjGens hdom hnd hlt gens
  have hlen : Δ.length ≤ n := length_le_of_nodup hnd hlt
  ext σ
  simp only [Set.mem_iUnion, exists_prop, List.mem_range, SetLike.mem_coe]
  constructor
  · intro hσ
    have hconj : ρ⁻¹ * σ * ρ ∈ genGroup (ordConjGens n dom Δ gens) := by
      rw [genGroup_ordConjGens]
      exact ⟨σ, hσ, by show ρ⁻¹ * σ * ρ⁻¹⁻¹ = _; rw [inv_inv]⟩
    have hmem : ρ⁻¹ * σ * ρ ∈ chainStab (genGroup (ordConjGens n dom Δ gens)) 0 := by
      rw [chainStab_zero]; exact hconj
    obtain ⟨j, hj, hcov⟩ :=
      chainRep_cover n (ordConjGens n dom Δ gens) Δ.length 0 (by omega) _ hmem
    rw [Nat.zero_add] at hcov
    refine ⟨j, hj, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hcov ⊢
    have hc : (chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j)⁻¹ * (ρ⁻¹ * σ * ρ)
        ∈ chainStab (genGroup (ordConjGens n dom Δ gens)) Δ.length := by
      simpa [smul_eq_mul] using hcov
    rw [hcs] at hc
    obtain ⟨u, hu, hueq⟩ := hc
    have : (winCosetRep n dom Δ gens j)⁻¹ * σ = u := by
      rw [winCosetRep, ← hρ]
      have h2 : ρ⁻¹ * u * ρ⁻¹⁻¹ = (chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j)⁻¹
          * (ρ⁻¹ * σ * ρ) := hueq
      rw [inv_inv] at h2
      have := congrArg (fun z => ρ * z * ρ⁻¹) h2
      simp only at this
      calc (ρ * chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j * ρ⁻¹)⁻¹ * σ
          = ρ * ((chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j)⁻¹
              * (ρ⁻¹ * σ * ρ)) * ρ⁻¹ := by group
        _ = u := by rw [← this]; group
    rw [show ((winCosetRep n dom Δ gens j)⁻¹ • σ : Perm (Fin n))
        = (winCosetRep n dom Δ gens j)⁻¹ * σ from rfl, this]
    exact hu
  · rintro ⟨j, -, hmem⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
    have hrep : winCosetRep n dom Δ gens j ∈ genGroup gens := by
      rw [winCosetRep, ← hρ]
      have hc : chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j
          ∈ chainStab (genGroup (ordConjGens n dom Δ gens)) 0 :=
        chainRep_mem n (ordConjGens n dom Δ gens) Δ.length 0 j
      rw [chainStab_zero, genGroup_ordConjGens] at hc
      obtain ⟨v, hv, hveq⟩ := hc
      have h2 : ρ⁻¹ * v * ρ⁻¹⁻¹ = chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j := hveq
      rw [inv_inv] at h2
      rw [← h2]
      have : ρ * (ρ⁻¹ * v * ρ) * ρ⁻¹ = v := by group
      rw [this]; exact hv
    have hu : (winCosetRep n dom Δ gens j)⁻¹ * σ ∈ genGroup gens := by
      have : (winCosetRep n dom Δ gens j)⁻¹ • σ ∈ K := hmem
      exact (Babai.mem_pointwiseStabilizer.1 this).1
    have := mul_mem hrep hu
    simpa using this

end Window

/-! ## The routines

The fold reads the digits of `j` off from the lowest, multiplying the entry selected at each
level onto the product so far.  There is one round per level of the window, and the level list
is `Algo.rawOne Δ`, so the loop is polynomial in the input; the index is a machine natural, so
it travels in binary. -/

/-- **Row `i` of a stored raw table**, as a list of raw permutations. -/
def rawRowAt (p : RawTable × ℕ) : List RawPerm := (p.1.getD p.2 ([] : RawRow)).map Prod.snd

theorem rawRow_eq_rawRowAt (p : (List ℕ × List RawPerm) × ℕ) :
    rawRow p = rawRowAt (rawBuildTable p.1, p.2) := rfl

/-- `τ` is stored in some row of the table. -/
def RowEntry (t : RawTable) (τ : RawPerm) : Prop := ∃ i, τ ∈ rawRowAt (t, i)

theorem size_le_of_rowEntry {t : RawTable} {τ : RawPerm} (h : RowEntry t τ) :
    Enc.size τ ≤ Enc.size t := by
  obtain ⟨i, hi⟩ := h
  rw [rawRowAt] at hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hi
  have hrow : t.getD i ([] : RawRow) ∈ t := by
    by_cases hlt : i < t.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at hq
      exact absurd hq (by simp)
  have h1 : Enc.size q.2 ≤ Enc.size q := Combine.size_snd_le q.1 q.2
  have h2 : Enc.size q ≤ Enc.size (t.getD i ([] : RawRow)) := size_mem_le hq
  have h3 : Enc.size (t.getD i ([] : RawRow)) ≤ Enc.size t := size_mem_le hrow
  omega

/-- **One round of the mixed-radix loop.**  `p.1.1` is the table, `p.1.2` a domain witness,
`p.2.1` the pair (product so far, index left) and `p.2.2` the level. -/
def rawChainStep (p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ)) : RawPerm × ℕ :=
  (rawMul (p.2.1.1,
      (rawRowAt (p.1.1, p.2.2)).getD (p.2.1.2 % (rawRowAt (p.1.1, p.2.2)).length)
        (rawOne p.1.2)),
    p.2.1.2 / (rawRowAt (p.1.1, p.2.2)).length)

/-- **The mixed-radix loop**: one round per level listed in `p.2.2`. -/
def rawChainFold (p : (RawTable × List ℕ) × ((RawPerm × ℕ) × List ℕ)) : RawPerm × ℕ :=
  List.foldl (fun acc i => rawChainStep (p.1, (acc, i))) p.2.1 p.2.2

/-- Mapping a list commutes with `List.getD` at a mapped default. -/
theorem getD_map {α β : Type*} (f : α → β) (l : List α) (m : ℕ) (d : α) :
    (l.map f).getD m (f d) = f (l.getD m d) := by
  by_cases hm : m < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getD_eq_getElem _ _ hm,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hm),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hm)]

section Spec

variable {t : RawTable} {gens : List (Perm (Fin n))}

/-- **The specification of the loop**: it multiplies the mixed-radix digits of `j`. -/
theorem rawChainFold_spec (hdom : dom.length = n)
    (hrow : ∀ i, rawRowAt (t, i) = (rowPerms n gens i).map (encPerm n)) :
    ∀ (k i : ℕ) (c : Perm (Fin n)) (j : ℕ),
      List.foldl (fun acc l => rawChainStep ((t, dom), (acc, l))) (encPerm n c, j)
          (List.range' i k)
        = (encPerm n (c * chainRep n gens i k j), chainQuot n gens i k j) := by
  intro k
  induction k with
  | zero => intro i c j; simp [chainRep_zero, chainQuot_zero]
  | succ k ih =>
      intro i c j
      have hlist : List.range' i (k + 1) = i :: List.range' (i + 1) k := rfl
      rw [hlist, List.foldl_cons]
      have hstep : rawChainStep ((t, dom), ((encPerm n c, j), i))
          = (encPerm n (c * (rowPerms n gens i).getD (j % chainRadix n gens i) 1),
              j / chainRadix n gens i) := by
        rw [rawChainStep]
        simp only
        rw [hrow i]
        have hlen : ((rowPerms n gens i).map (encPerm n)).length = chainRadix n gens i := by
          rw [List.length_map, chainRadix]
        rw [hlen]
        have hone : rawOne dom = encPerm n (1 : Perm (Fin n)) := by
          rw [rawOne_eq, hdom]
        rw [hone, getD_map, rawMul_encPerm]
      rw [hstep, ih (i + 1) (c * (rowPerms n gens i).getD (j % chainRadix n gens i) 1)
        (j / chainRadix n gens i), chainRep_succ, chainQuot_succ, mul_assoc]

end Spec

/-- **The `j`-th representative inside the conjugated group**, as a routine. -/
def rawWinChainRep (p : (List ℕ × List RawPerm) × (List ℕ × ℕ)) : RawPerm :=
  (rawChainFold ((rawWinTable (p.1, p.2.1), p.1.1), ((rawOne p.1.1, p.2.2), rawOne p.2.1))).1

/-- **The `j`-th coset representative of the kernel `G_{(Δ)}` in `G`, indexed in binary.**
`p.1` is a domain witness with the generator list of `G`, `p.2.1` is the window `Δ` and `p.2.2`
is the index `j`, a machine natural.  Paper: the representatives of Prop. 11.1.6, for the
kernel of Prop. 2.2.6 (a). -/
def rawCosetRepBin (p : (List ℕ × List RawPerm) × (List ℕ × ℕ)) : RawPerm :=
  rawMul (rawOrd (p.1.1, p.2.1), rawMul (rawWinChainRep p, rawInv (rawOrd (p.1.1, p.2.1))))

section RepSpec

variable {gens : List (Perm (Fin n))}

/-- The rows of the reordered table are the rows of the table of the conjugated generators. -/
theorem rawRowAt_rawWinTable (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) (i : ℕ) :
    rawRowAt (rawWinTable ((dom, gens.map (encPerm n)), Δ), i)
      = (rowPerms n (ordConjGens n dom Δ gens) i).map (encPerm n) := by
  have hwf : RawPerm.WF n (rawOrd (dom, Δ)) := wf_rawOrd hdom hnd hlt
  have hconj : rawConj (rawOrd (dom, Δ), gens.map (encPerm n))
      = (ordConjGens n dom Δ gens).map (encPerm n) := rawConj_spec hwf gens
  rw [rawWinTable]
  show rawRowAt (rawBuildTable (dom, rawConj (rawOrd (dom, Δ), gens.map (encPerm n))), i) = _
  rw [hconj]
  show rawRow ((dom, (ordConjGens n dom Δ gens).map (encPerm n)), i) = _
  exact rawRow_spec dom hdom _ i

/-- **The routine computes the representative inside the conjugated group.** -/
theorem rawWinChainRep_spec (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) (j : ℕ) :
    rawWinChainRep ((dom, gens.map (encPerm n)), (Δ, j))
      = encPerm n (chainRep n (ordConjGens n dom Δ gens) 0 Δ.length j) := by
  rw [rawWinChainRep]
  show (rawChainFold ((rawWinTable ((dom, gens.map (encPerm n)), Δ), dom),
      ((rawOne dom, j), rawOne Δ))).1 = _
  rw [rawChainFold]
  simp only
  have hone : rawOne dom = encPerm n (1 : Perm (Fin n)) := by rw [rawOne_eq, hdom]
  have hlevels : rawOne Δ = List.range' 0 Δ.length := by
    rw [rawOne, List.range_eq_range']
  rw [hone, hlevels,
    rawChainFold_spec (gens := ordConjGens n dom Δ gens) hdom
      (rawRowAt_rawWinTable hdom hnd hlt gens) Δ.length 0 1 j]
  simp

/-- **The routine computes the `j`-th coset representative.** -/
theorem rawCosetRepBin_spec (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) (j : ℕ) :
    rawCosetRepBin ((dom, gens.map (encPerm n)), (Δ, j))
      = encPerm n (winCosetRep n dom Δ gens j) := by
  have hwf : RawPerm.WF n (rawOrd (dom, Δ)) := wf_rawOrd hdom hnd hlt
  have hord : encPerm n (decPerm n (rawOrd (dom, Δ))) = rawOrd (dom, Δ) := encPerm_decPerm hwf
  rw [rawCosetRepBin]
  show rawMul (rawOrd (dom, Δ),
      rawMul (rawWinChainRep ((dom, gens.map (encPerm n)), (Δ, j)),
        rawInv (rawOrd (dom, Δ)))) = _
  rw [rawWinChainRep_spec hdom hnd hlt gens j, ← hord, rawInv_encPerm, rawMul_encPerm,
    rawMul_encPerm, winCosetRep, mul_assoc]

/-- **The `j`-th coset representative is a well-formed permutation.** -/
theorem wf_rawCosetRepBin (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) (j : ℕ) :
    RawPerm.WF n (rawCosetRepBin ((dom, gens.map (encPerm n)), (Δ, j))) := by
  rw [rawCosetRepBin_spec hdom hnd hlt gens j]
  exact wf_encPerm n _

end RepSpec

/-! ## The kernel itself: Proposition 2.2.6 (a)

The generators of the kernel are the entries of the rows past the window of the reordered
table, conjugated back — that is `Algo.rawPointStab` — shortened to at most `n²` by
`Algo.rawShorten`. -/

/-- A well-formed raw generating list is the encoding of its own decoding. -/
theorem map_encPerm_decPerm' {gs : RawGens} (h : RawGens.WF n gs) :
    (gs.map (decPerm n)).map (encPerm n) = gs := by
  rw [List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro g hg
  exact encPerm_decPerm (h g hg)

/-- **The pointwise stabilizer routine returns well-formed permutations.** -/
theorem wf_rawPointStab (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    RawGens.WF n (rawPointStab ((dom, gens.map (encPerm n)), Δ)) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
  have hord : RawPerm.WF n (rawOrd (dom, Δ)) := wf_rawOrd hdom hnd hlt
  have hhwf : RawPerm.WF n h := by
    have hs : rawStab ((dom, rawConj (rawOrd (dom, Δ), gens.map (encPerm n))), Δ.length)
        = (stabGens n (ordConjGens n dom Δ gens) Δ.length).map (encPerm n) := by
      rw [rawConj_spec hord gens]
      exact rawStab_spec dom hdom _ Δ.length
    rw [hs] at hh
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hh
    exact wf_encPerm n u
  exact wf_rawMul hord (wf_rawMul hhwf (wf_rawInv hord))

/-- **Generators of the kernel `ker(G → S(Δ)) = G_{(Δ)}`**, at most `n²` of them.
Paper: Proposition 2.2.6 (a) (§2.2.3), for the restriction to a window. -/
def rawKerGens (p : (List ℕ × List RawPerm) × List ℕ) : RawGens :=
  rawShorten (p.1.1, rawPointStab p)

/-- **Proposition 2.2.6 (a)** (§2.2.3), for the restriction to an invariant window: the routine
returns a generating list of the kernel of the action of `G` on `Δ`, which by
`Algo.mem_ker_winRestrictHom` is the pointwise stabilizer `G_{(Δ)}`. -/
theorem decGroup_rawKerGens (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    decGroup n (rawKerGens ((dom, gens.map (encPerm n)), Δ))
      = Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ} := by
  have hps := decGroup_rawPointStab dom hdom gens Δ hnd hlt
  have hmap : rawPointStab ((dom, gens.map (encPerm n)), Δ)
      = ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map (decPerm n)).map (encPerm n) :=
    (map_encPerm_decPerm' (wf_rawPointStab hdom hnd hlt gens)).symm
  rw [rawKerGens]
  rw [show rawShorten (dom, rawPointStab ((dom, gens.map (encPerm n)), Δ))
      = rawShorten (dom, ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map
        (decPerm n)).map (encPerm n)) from by rw [← hmap]]
  rw [decGroup_rawShorten dom hdom _, ← decGroup, hps]

/-- **The kernel is given by at most `n²` generators.** -/
theorem length_rawKerGens_le (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    (rawKerGens ((dom, gens.map (encPerm n)), Δ)).length ≤ n * n := by
  have hmap : rawPointStab ((dom, gens.map (encPerm n)), Δ)
      = ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map (decPerm n)).map (encPerm n) :=
    (map_encPerm_decPerm' (wf_rawPointStab hdom hnd hlt gens)).symm
  rw [rawKerGens]
  rw [show rawShorten (dom, rawPointStab ((dom, gens.map (encPerm n)), Δ))
      = rawShorten (dom, ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map
        (decPerm n)).map (encPerm n)) from by rw [← hmap]]
  exact length_rawShorten_le dom hdom _

/-- **Well-formedness of the kernel generators.** -/
theorem wf_rawKerGens (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n)
    (gens : List (Perm (Fin n))) :
    RawGens.WF n (rawKerGens ((dom, gens.map (encPerm n)), Δ)) := by
  have hmap : rawPointStab ((dom, gens.map (encPerm n)), Δ)
      = ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map (decPerm n)).map (encPerm n) :=
    (map_encPerm_decPerm' (wf_rawPointStab hdom hnd hlt gens)).symm
  rw [rawKerGens]
  rw [show rawShorten (dom, rawPointStab ((dom, gens.map (encPerm n)), Δ))
      = rawShorten (dom, ((rawPointStab ((dom, gens.map (encPerm n)), Δ)).map
        (decPerm n)).map (encPerm n)) from by rw [← hmap]]
  rw [rawShorten, rawBuildTable_spec dom hdom _, rawEntries_encMTable]
  exact wf_map_encPerm n _

theorem polyFun_rawKerGens : PolyFun rawKerGens :=
  (((polyFun_fst.comp polyFun_fst).pair polyFun_rawPointStab).comp polyFun_rawShorten).of_eq
    (fun _ => rfl)

/-! ## The running times -/

theorem polyFun_rawRowAt : PolyFun rawRowAt := by
  have hg : PolyFun (fun p : RawTable × ℕ => p.1.getD p.2 ([] : RawRow)) :=
    ((polyFun_fst.pair polyFun_snd).pair (polyFun_const ([] : RawRow))).comp polyFun_getD
  exact (hg.comp (PolyFun.map (polyFun_snd (α := ℕ) (β := RawPerm)))).of_eq (fun _ => rfl)

theorem polyFun_rawChainStep : PolyFun rawChainStep := by
  have hrow : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) =>
      rawRowAt (p.1.1, p.2.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawRowAt
  have hlen : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) =>
      (rawRowAt (p.1.1, p.2.2)).length) := hrow.comp polyFun_length
  have hj : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) => p.2.1.2) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_snd
  have hcur : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) => p.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hone : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) => rawOne p.1.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_rawOne
  have hsel : PolyFun (fun p : (RawTable × List ℕ) × ((RawPerm × ℕ) × ℕ) =>
      (rawRowAt (p.1.1, p.2.2)).getD (p.2.1.2 % (rawRowAt (p.1.1, p.2.2)).length)
        (rawOne p.1.2)) :=
    ((hrow.pair (hj.op₂ hlen polyFun_mod)).pair hone).comp polyFun_getD
  exact ((hcur.pair hsel).comp polyFun_rawMul).pair (hj.op₂ hlen polyFun_div)

/-- **The structure of the accumulator of the mixed-radix loop.**  The product is the start
multiplied by table entries and identities, so its length is the length of the last factor and
its entries are entries of the start or of a factor; the index left over only shrinks.  This is
the bound `RAM.PolyFun.foldlParam` asks for. -/
theorem rawChainFold_struct (t : RawTable) (dom : List ℕ) :
    ∀ (l : List ℕ) (r : RawPerm) (j : ℕ),
      (List.foldl (fun acc i => rawChainStep ((t, dom), (acc, i))) (r, j) l).2 ≤ j ∧
      ((List.foldl (fun acc i => rawChainStep ((t, dom), (acc, i))) (r, j) l).1.length
          ≤ r.length ∨
        ∃ τ, (RowEntry t τ ∨ τ = rawOne dom) ∧
          (List.foldl (fun acc i => rawChainStep ((t, dom), (acc, i))) (r, j) l).1.length
            ≤ τ.length) ∧
      (∀ x ∈ (List.foldl (fun acc i => rawChainStep ((t, dom), (acc, i))) (r, j) l).1,
        x ∈ r ∨ ∃ τ, (RowEntry t τ ∨ τ = rawOne dom) ∧ x ∈ τ) := by
  intro l
  induction l with
  | nil => intro r j; exact ⟨le_rfl, Or.inl le_rfl, fun x hx => Or.inl hx⟩
  | cons a s ih =>
      intro r j
      rw [List.foldl_cons]
      set w := (rawRowAt (t, a)).getD (j % (rawRowAt (t, a)).length) (rawOne dom) with hw
      have hsrc : RowEntry t w ∨ w = rawOne dom := by
        rcases getD_mem_or_eq (rawRowAt (t, a)) (j % (rawRowAt (t, a)).length)
          (rawOne dom) with h | h
        · exact Or.inl ⟨a, h⟩
        · exact Or.inr h
      have hstep : rawChainStep ((t, dom), ((r, j), a))
          = (rawMul (r, w), j / (rawRowAt (t, a)).length) := rfl
      rw [hstep]
      obtain ⟨h1, h2, h3⟩ := ih (rawMul (r, w)) (j / (rawRowAt (t, a)).length)
      refine ⟨le_trans h1 (Nat.div_le_self _ _), ?_, ?_⟩
      · rcases h2 with h | ⟨τ, hτ, hle⟩
        · exact Or.inr ⟨w, hsrc, by rwa [length_rawMul] at h⟩
        · exact Or.inr ⟨τ, hτ, hle⟩
      · intro x hx
        rcases h3 x hx with h | h
        · rcases mem_rawMul h with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨w, hsrc, h'⟩
        · exact Or.inr h

/-- The size bound of the loop's accumulator. -/
def chainAccBound (m : ℕ) : ℕ := 2 * (1 + m * (2 * (m + 2) + 1)) + 2 * m

theorem polyBound_chainAccBound : PolyBound chainAccBound :=
  ((polyBound_const 2).mul ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1))))).add ((polyBound_const 2).mul polyBound_id)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawChainFold : PolyFun rawChainFold := by
  have hacc : ∀ (cc : RawTable × List ℕ) (x : RawPerm × ℕ) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawChainStep (cc, (y, a))) x (r.take j))
        ≤ chainAccBound
            (Enc.size ((cc, (x, r)) : (RawTable × List ℕ) × ((RawPerm × ℕ) × List ℕ))) := by
    intro cc x r j
    obtain ⟨t, dm⟩ := cc
    obtain ⟨r₀, j₀⟩ := x
    set N := Enc.size (((t, dm), ((r₀, j₀), r)) :
      (RawTable × List ℕ) × ((RawPerm × ℕ) × List ℕ)) with hN
    have hcc : Enc.size ((t, dm) : RawTable × List ℕ) ≤ N :=
      Combine.size_fst_le ((t, dm) : RawTable × List ℕ) (((r₀, j₀), r) : (RawPerm × ℕ) × List ℕ)
    have ht : Enc.size t ≤ N := le_trans (Combine.size_fst_le t dm) hcc
    have hdm : Enc.size dm ≤ N := le_trans (Combine.size_snd_le t dm) hcc
    have hxr : Enc.size ((((r₀, j₀), r)) : (RawPerm × ℕ) × List ℕ) ≤ N :=
      Combine.size_snd_le ((t, dm) : RawTable × List ℕ) (((r₀, j₀), r) : (RawPerm × ℕ) × List ℕ)
    have hx : Enc.size ((r₀, j₀) : RawPerm × ℕ) ≤ N :=
      le_trans (Combine.size_fst_le ((r₀, j₀) : RawPerm × ℕ) r) hxr
    have hr₀ : Enc.size r₀ ≤ N := le_trans (Combine.size_fst_le r₀ j₀) hx
    have hj₀ : Enc.size j₀ ≤ N := le_trans (Combine.size_snd_le r₀ j₀) hx
    -- a factor is a table entry or the identity, and both are small
    have hfac : ∀ τ : RawPerm, (RowEntry t τ ∨ τ = rawOne dm) →
        τ.length ≤ N ∧ ∀ y ∈ τ, Enc.size y ≤ N + 2 := by
      intro τ hτ
      rcases hτ with hτ | rfl
      · have h1 : Enc.size τ ≤ N := le_trans (size_le_of_rowEntry hτ) ht
        exact ⟨le_trans (length_le_size τ) h1, fun y hy => by
          have := size_mem_le hy; omega⟩
      · have hlen : (rawOne dm).length = dm.length := by rw [rawOne, List.length_range]
        have hdl : dm.length ≤ N := le_trans (length_le_size dm) hdm
        refine ⟨by omega, fun y hy => ?_⟩
        have hylt : y < dm.length := by
          rw [rawOne, List.mem_range] at hy; exact hy
        have h1 : Enc.size y = Nat.size y + 2 := Small.size_nat y
        have h2 : Nat.size y ≤ y := size_le_self y
        omega
    obtain ⟨h1, h2, h3⟩ := rawChainFold_struct t dm (r.take j) r₀ j₀
    set res := List.foldl (fun acc i => rawChainStep ((t, dm), (acc, i))) (r₀, j₀) (r.take j)
      with hres
    have hjres : Enc.size res.2 ≤ N := le_trans (size_nat_le_of_le h1) hj₀
    have hlen : res.1.length ≤ N := by
      rcases h2 with h | ⟨τ, hτ, hle⟩
      · exact le_trans h (le_trans (length_le_size r₀) hr₀)
      · exact le_trans hle (hfac τ hτ).1
    have hent : ∀ y ∈ res.1, Enc.size y ≤ N + 2 := by
      intro y hy
      rcases h3 y hy with h | ⟨τ, hτ, hyτ⟩
      · have := size_mem_le h; omega
      · exact (hfac τ hτ).2 y hyτ
    have hsize := size_list_le_of_entries res.1 (N + 2) hent
    have hmul : res.1.length * (2 * (N + 2) + 1) ≤ N * (2 * (N + 2) + 1) :=
      Nat.mul_le_mul_right _ hlen
    have hpair : Enc.size res ≤ 2 * Enc.size res.1 + 2 * Enc.size res.2 := size_pair_le' res
    have hgoal : chainAccBound N = 2 * (1 + N * (2 * (N + 2) + 1)) + 2 * N := rfl
    show Enc.size res ≤ chainAccBound N
    omega
  have hfold := PolyFun.foldlParam polyFun_rawChainStep polyBound_chainAccBound hacc
  exact hfold.of_eq (fun _ => rfl)

theorem polyFun_rawWinChainRep : PolyFun rawWinChainRep := by
  have hdom : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hΔ : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) => p.2.2) :=
    polyFun_snd.comp polyFun_snd
  have htab : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) =>
      rawWinTable (p.1, p.2.1)) := (polyFun_fst.pair hΔ).comp polyFun_rawWinTable
  have hin : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) =>
      (((rawWinTable (p.1, p.2.1), p.1.1), ((rawOne p.1.1, p.2.2), rawOne p.2.1)) :
        (RawTable × List ℕ) × ((RawPerm × ℕ) × List ℕ))) :=
    (htab.pair hdom).pair (((hdom.comp polyFun_rawOne).pair hj).pair (hΔ.comp polyFun_rawOne))
  exact ((hin.comp polyFun_rawChainFold).comp polyFun_fst).of_eq (fun _ => rfl)

theorem polyFun_rawCosetRepBin : PolyFun rawCosetRepBin := by
  have hord : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × ℕ) =>
      rawOrd (p.1.1, p.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawOrd
  exact ((hord.pair ((polyFun_rawWinChainRep.pair
    (hord.comp polyFun_rawInv)).comp polyFun_rawMul)).comp polyFun_rawMul).of_eq (fun _ => rfl)

/-! ## The chain index is the index of the kernel (risk R-A7-3)

`Algo.winCosetIndex` was so far only known to **cover** `G` (`Algo.cover_winCosetRep`), so it
was at least the true number `|G : G_{(Δ)}|` of cosets.  It is in fact equal to it.  The reason
is the uniqueness half of `Algo.rowPerms_transversal`, which the covering argument does not
use: row `i` of the table is a transversal of `G^{(i+1)}` in `G^{(i)}`, and its entries are
pairwise distinct, so `Algo.chainRadix n gens i = |G^{(i)} : G^{(i+1)}|`.  Multiplying the
levels together (the orbit–stabilizer theorem along the chain) gives
`Algo.chainIndex n gens i k = |G^{(i)} : G^{(i+k)}|`.

Paper: this is `|G : N|` of Proposition 11.1.6 and Theorem 11.1.9, and with
`Babai.Theorem_11_1_9_card` it is `|Ḡ|`. -/

section Index

variable {n : ℕ}

/-- **The entries of row `i` are pairwise distinct.**  The entry stored under the key `j`
sends the level `i` to `j` (`Algo.IsTable.img`), and the keys of a stored row are pairwise
distinct (`Algo.Shape`), so distinct keys carry distinct permutations. -/
theorem nodup_rowPerms (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) :
    (rowPerms n gens i).Nodup := by
  classical
  set M := buildTable n gens with hM
  set R := M.getD i ([] : MRow n) with hR
  have hrow : rowPerms n gens i = R.map Prod.snd := rfl
  rcases getD_mem_or_nil M i with hmem | hnil
  · have hnd : (R.map Prod.fst).Nodup := (shape_buildTable n gens).nodup _ hmem
    have hkey : ∀ q ∈ R, evalAt q.2 i = q.1 := by
      intro q hq
      refine (isTable_buildTable n gens).img (i := i) (j := q.1) (τ := q.2) ?_
      show (M.getD i ([] : MRow n)).lookup q.1 = some q.2
      exact lookup_eq_some_of_mem _ hnd (by simpa using hq)
    have hmapeq : (R.map Prod.snd).map (fun τ => evalAt τ i) = R.map Prod.fst := by
      rw [List.map_map]
      exact List.map_congr_left (fun q hq => hkey q hq)
    rw [hrow]
    exact List.Nodup.of_map (fun τ => evalAt τ i) (by rw [hmapeq]; exact hnd)
  · rw [hrow, hR, hnil]
    exact List.nodup_nil

/-- **One level of the chain**, the orbit–stabilizer theorem: `|G^{(i)}| = r_i · |G^{(i+1)}|`
with `r_i = Algo.chainRadix n gens i` the length of the `i`-th basic orbit.  This is the
uniqueness half of `Algo.rowPerms_transversal`. -/
theorem card_chainStab_succ (n : ℕ) (gens : List (Perm (Fin n))) {i : ℕ} (hi : i < n) :
    Nat.card (chainStab (genGroup gens) i)
      = chainRadix n gens i * Nat.card (chainStab (genGroup gens) (i + 1)) := by
  classical
  set R := (rowPerms n gens i).toFinset with hRdef
  have hcardR : R.card = chainRadix n gens i := by
    rw [hRdef, List.toFinset_card_of_nodup (nodup_rowPerms n gens i), chainRadix]
  have hmemR : ∀ τ : Perm (Fin n), τ ∈ R ↔ τ ∈ rowPerms n gens i := by
    intro τ; rw [hRdef, List.mem_toFinset]
  have hmul : ∀ (τ : {x : Perm (Fin n) // x ∈ R})
      (u : chainStab (genGroup gens) (i + 1)),
      (τ : Perm (Fin n)) * (u : Perm (Fin n)) ∈ chainStab (genGroup gens) i := by
    intro τ u
    exact Subgroup.mul_mem _ (rowPerms_subset_chainStab n gens i ((hmemR _).1 τ.2))
      (chainStab_mono (Nat.le_succ i) u.2)
  have hbij : Function.Bijective
      (fun p : {x : Perm (Fin n) // x ∈ R} × chainStab (genGroup gens) (i + 1) =>
        (⟨(p.1 : Perm (Fin n)) * (p.2 : Perm (Fin n)), hmul p.1 p.2⟩ :
          chainStab (genGroup gens) i)) := by
    constructor
    · rintro ⟨τ, u⟩ ⟨τ', u'⟩ hp
      have heq : (τ : Perm (Fin n)) * (u : Perm (Fin n))
          = (τ' : Perm (Fin n)) * (u' : Perm (Fin n)) := congrArg Subtype.val hp
      obtain ⟨p, -, huniq⟩ := rowPerms_transversal n gens (i := i) (k := n - i - 1)
        (by omega) (hmul τ u)
      have h1 := huniq ((τ : Perm (Fin n)), (u : Perm (Fin n)))
        ⟨(hmemR _).1 τ.2, u.2, rfl⟩
      have h2 := huniq ((τ' : Perm (Fin n)), (u' : Perm (Fin n)))
        ⟨(hmemR _).1 τ'.2, u'.2, heq⟩
      have h3 : ((τ : Perm (Fin n)), (u : Perm (Fin n)))
          = ((τ' : Perm (Fin n)), (u' : Perm (Fin n))) := h1.trans h2.symm
      rw [Prod.mk.injEq] at h3
      simp only [Prod.mk.injEq]
      exact ⟨Subtype.ext h3.1, Subtype.ext h3.2⟩
    · rintro ⟨σ, hσ⟩
      obtain ⟨p, ⟨hp1, hp2, hp3⟩, -⟩ := rowPerms_transversal n gens (i := i)
        (k := n - i - 1) (by omega) hσ
      exact ⟨(⟨p.1, (hmemR _).2 hp1⟩, ⟨p.2, hp2⟩), Subtype.ext hp3.symm⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_eq_finsetCard, hcardR] at hcard
  exact hcard.symm

/-- **The orbit–stabilizer theorem along the chain**: the product of the `k` basic orbit
lengths from the level `i` on is the index `|G^{(i)} : G^{(i+k)}|`. -/
theorem chainIndex_mul_card (n : ℕ) (gens : List (Perm (Fin n))) :
    ∀ (k i : ℕ), i + k ≤ n →
      chainIndex n gens i k * Nat.card (chainStab (genGroup gens) (i + k))
        = Nat.card (chainStab (genGroup gens) i) := by
  intro k
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
      intro i hik
      have hi : i < n := by omega
      rw [chainIndex_succ, show i + (k + 1) = (i + 1) + k by omega, mul_assoc,
        ih (i + 1) (by omega), card_chainStab_succ n gens hi]

/-- Conjugating a subgroup does not change its order. -/
theorem card_map_conj {n : ℕ} (H : Subgroup (Perm (Fin n))) (c : Perm (Fin n)) :
    Nat.card (H.map (MulAut.conj c).toMonoidHom) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).toEquiv).symm

/-- **R-A7-3**: `Algo.winCosetIndex` is exactly the index `|G : G_{(Δ)}|` of the kernel of the
restriction to the window, not merely an upper bound for the number of cosets.  Written
multiplicatively, `|G : G_{(Δ)}| · |G_{(Δ)}| = |G|`. -/
theorem winCosetIndex_mul_card {n : ℕ} {dom Δ : List ℕ} (hdom : dom.length = n)
    (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n) (gens : List (Perm (Fin n))) :
    winCosetIndex n dom Δ gens
        * Nat.card (Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ})
      = Nat.card (genGroup gens) := by
  have hk : Δ.length ≤ n := length_le_of_nodup hnd hlt
  have h := chainIndex_mul_card n (ordConjGens n dom Δ gens) Δ.length 0 (by omega)
  rw [zero_add, chainStab_zero, chainStab_ordConjGens hdom hnd hlt gens,
    genGroup_ordConjGens, card_map_conj, card_map_conj] at h
  exact h

end Index

end Algo
