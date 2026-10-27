/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: transversals, pointwise stabilizers and short generating sets.
-/
import Workspace.Algo.Order

/-!
# Transversals, pointwise stabilizers, short generating sets

Three of the class-D rows of `Workspace/Algo/DESIGN.md`, item 2, all read off a complete
sifting table.

**(a) A transversal of `G^{(i+1)}` in `G^{(i)}`.**  Proposition 11.1.6 and Theorem 11.1.9 let
"`σ` range over right coset representatives"; the transversal they need is row `i` of the
table.  `Algo.entries_transversal` says exactly that: every element of `G^{(i)}` is an entry of
row `i` times an element of `G^{(i+1)}`, in exactly one way.

**(b) Generators of a pointwise stabilizer.**  §13.1 line 08 needs `G_{(Δ)}`.  For the chain's
own subsets — the initial segments `{0, …, i−1}` — the answer is the entries of the rows from
`i` on (`Algo.closure_entriesFrom`), which is the standard strong generating set.  For an
arbitrary subset `Δ` the two ways out are to reorder the base or to conjugate, and
`Algo.pointwiseStabilizer_map_conj` takes the second: conjugation by a permutation `π` carries
`G_{(Δ)}` to `(πGπ⁻¹)_{(π Δ)}`, so choosing `π` with `π Δ = {0, …, |Δ|−1}` reduces the
arbitrary case to the chain's.  Conjugation is preferred over reordering the base because it
keeps one chain routine — the base is always `0, 1, 2, …` — and because conjugating a
generating list is a `map` of `Algo.rawMul`, which is already a `RAM.PolyFun`, whereas
reordering the base would need a second copy of the whole table machinery.

**(c) Shortening a generating list.**  Every step of Luks's framework outputs a generating
list, and the lists must not grow from one round to the next (risk R8 of
`Workspace/Algo/DESIGN.md`).  The entries of a complete table generate `G`
(`Algo.closure_allEntries`) and there are at most `n²` of them
(`Algo.length_entriesList_buildTable_le`), so sifting shortens any list to `n²` generators.

No axiom and no `sorry`.  The routines themselves (and their `RAM.PolyFun`s) are left to a
later session; what is proved here is the mathematics they compute.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## What sifts through from a level is what the chain has there -/

/-- **What sifts through from the level `i` is exactly `G^{(i)}`**, as soon as the table is
complete and enough levels are left. -/
theorem sifted_eq_chainStab {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) {k i : ℕ} (h : i + k = n) :
    Sifted T k i = (chainStab G i : Set (Perm (Fin n))) := by
  ext σ
  constructor
  · intro hσ
    exact mem_chainStab.2 ⟨mem_of_mem_sifted hT hσ, sifted_fixes hT k i σ hσ⟩
  · intro hσ
    exact siftAux_eq_one_of_mem hT hC k i h σ hσ

/-! ## (a) Row `i` is a transversal of `G^{(i+1)}` in `G^{(i)}` -/

/-- **Each entry of row `i` lies in `G^{(i)}`.** -/
theorem entries_subset_chainStab {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (i : ℕ) : Entries T i ⊆ (chainStab G i : Set (Perm (Fin n))) := by
  rintro τ ⟨j, hj⟩
  exact hT.mem_chainStab hj

/-- **Row `i` of a complete table is a transversal of `G^{(i+1)}` in `G^{(i)}`**: every element
of `G^{(i)}` is an entry of row `i` times an element of `G^{(i+1)}`, and the two factors are
determined by the product.  This is the transversal that Prop. 11.1.6 and Thm. 11.1.9 use. -/
theorem entries_transversal {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) {i k : ℕ} (h : i + (k + 1) = n) {σ : Perm (Fin n)}
    (hσ : σ ∈ chainStab G i) :
    ∃! p : Perm (Fin n) × Perm (Fin n),
      p.1 ∈ Entries T i ∧ p.2 ∈ chainStab G (i + 1) ∧ σ = p.1 * p.2 := by
  have hnext : Sifted T k (i + 1) = (chainStab G (i + 1) : Set (Perm (Fin n))) :=
    sifted_eq_chainStab hT hC (by omega)
  have hhere : σ ∈ Sifted T (k + 1) i := by
    rw [sifted_eq_chainStab hT hC h]
    exact hσ
  obtain ⟨τ, hτ, ρ, hρ, hprod⟩ := (mem_sifted_succ_iff_mul hT).1 hhere
  refine ⟨(τ, ρ), ⟨hτ, by rwa [hnext] at hρ, hprod⟩, ?_⟩
  rintro ⟨τ', ρ'⟩ ⟨hτ', hρ', hprod'⟩
  have hρ'' : ρ' ∈ Sifted T k (i + 1) := by rwa [hnext]
  obtain ⟨h1, h2⟩ := sifted_factor_unique hT hτ' hτ hρ'' hρ (by rw [← hprod', ← hprod])
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-! ## (b) Generators of a pointwise stabilizer

The entries of the rows from `i` on generate `G^{(i)}`.  For `i = 0` this is the statement that
the entries of a complete table generate `G`. -/

/-- The entries of the rows from `i` on. -/
def EntriesFrom (T : Table n) (i : ℕ) : Set (Perm (Fin n)) :=
  {τ | ∃ j, i ≤ j ∧ ∃ m, T j m = some τ}

theorem entries_subset_entriesFrom {T : Table n} {i j : ℕ} (h : i ≤ j) :
    Entries T j ⊆ EntriesFrom T i := by
  rintro τ ⟨m, hm⟩
  exact ⟨j, h, m, hm⟩

theorem entriesFrom_mono {T : Table n} {i j : ℕ} (h : i ≤ j) :
    EntriesFrom T j ⊆ EntriesFrom T i := by
  rintro τ ⟨l, hl, m, hm⟩
  exact ⟨l, le_trans h hl, m, hm⟩

theorem entriesFrom_zero (T : Table n) : EntriesFrom T 0 = AllEntries T := by
  ext τ
  constructor
  · rintro ⟨j, -, m, hm⟩
    exact ⟨j, m, hm⟩
  · rintro ⟨j, m, hm⟩
    exact ⟨j, Nat.zero_le j, m, hm⟩

/-- **What sifts through from the level `i` is generated by the entries of the rows from `i`
on.**  The downward induction of the Schreier–Sims analysis. -/
theorem sifted_subset_closure_entriesFrom {T : Table n} {G : Subgroup (Perm (Fin n))}
    (hT : IsTable T G) : ∀ (k i : ℕ),
      Sifted T k i ⊆ (Subgroup.closure (EntriesFrom T i) : Set (Perm (Fin n))) := by
  intro k
  induction k with
  | zero =>
      intro i σ hσ
      rw [mem_sifted_zero.1 hσ]
      exact Subgroup.one_mem _
  | succ k ih =>
      intro i σ hσ
      obtain ⟨τ, hτ, ρ, hρ, rfl⟩ := (mem_sifted_succ_iff_mul hT).1 hσ
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.subset_closure (entries_subset_entriesFrom (le_refl i) hτ)
      · have h1 : ρ ∈ Subgroup.closure (EntriesFrom T (i + 1)) := ih (i + 1) hρ
        exact (Subgroup.closure_mono (entriesFrom_mono (Nat.le_succ i))) h1

/-- **The entries of the rows from `i` on generate the pointwise stabilizer of
`{0, …, i−1}`.**  This is the generating set §13.1 line 08 needs, for the initial segments. -/
theorem closure_entriesFrom {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) {k i : ℕ} (h : i + k = n) :
    Subgroup.closure (EntriesFrom T i) = chainStab G i := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro τ ⟨j, hj, m, hm⟩
    exact chainStab_mono hj (hT.mem_chainStab hm)
  · intro σ hσ
    have hsift : σ ∈ Sifted T k i := by
      rw [sifted_eq_chainStab hT hC h]
      exact hσ
    exact sifted_subset_closure_entriesFrom hT k i hsift

/-- **The entries of a complete table generate `G`.** -/
theorem closure_allEntries {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) : Subgroup.closure (AllEntries T) = G := by
  rw [← entriesFrom_zero, closure_entriesFrom hT hC (k := n) (i := 0) (by omega),
    chainStab_zero]

/-! ## The pointwise stabilizer of an arbitrary subset

Conjugation carries pointwise stabilizers to pointwise stabilizers, so a set `Δ` that is not an
initial segment is handled by conjugating with any `π` that maps `Δ` onto one. -/

/-- **Conjugation transports the pointwise stabilizer.**  With `π Δ = {0, …, |Δ|−1}` the right
hand side is a group of the chain of `πGπ⁻¹`, which the table of `πGπ⁻¹` computes. -/
theorem pointwiseStabilizer_map_conj {Ω : Type*} [DecidableEq Ω] (π : Perm Ω)
    (G : Subgroup (Perm Ω)) (Δ : Set Ω) :
    (Babai.pointwiseStabilizer G Δ).map (MulAut.conj π).toMonoidHom
      = Babai.pointwiseStabilizer (G.map (MulAut.conj π).toMonoidHom) (π '' Δ) := by
  ext σ
  constructor
  · rintro ⟨α, ⟨hαG, hαΔ⟩, rfl⟩
    refine ⟨⟨α, hαG, rfl⟩, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    show (π * α * π⁻¹) (π y) = π y
    simp [Equiv.Perm.mul_apply, hαΔ y hy]
  · rintro ⟨⟨α, hαG, hα⟩, hfix⟩
    refine ⟨α, ⟨hαG, ?_⟩, hα⟩
    intro y hy
    have h1 : σ (π y) = π y := hfix (π y) ⟨y, hy, rfl⟩
    have h2 : σ = π * α * π⁻¹ := hα.symm
    rw [h2] at h1
    have h3 : π (α y) = π y := by simpa [Equiv.Perm.mul_apply] using h1
    exact π.injective h3

/-! ## (c) Shortening a generating list

The entries of the table built by the closure loop generate `⟨gens⟩`, and the shape invariant
bounds their number by `n²`. -/

/-- **The entries of the table built generate the group.** -/
theorem closure_allEntries_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    Subgroup.closure (AllEntries (tableOf (buildTable n gens))) = genGroup gens :=
  closure_allEntries (isTable_buildTable n gens) (complete_buildTable n gens)

/-- **The entries of the table built are at most `n²`.**  So sifting a list of generators of any
length through the table replaces it by one of length at most `n²`. -/
theorem length_entriesList_buildTable_le (n : ℕ) (gens : List (Perm (Fin n))) :
    (entriesList (buildTable n gens)).length ≤ n * n := by
  rw [entriesList, List.length_map]
  exact length_flatten_le_of_shape (shape_buildTable n gens)

/-- The same on raw data: the routine `Algo.rawEntries` of
`Workspace/Algo/ChainBuildRaw.lean`, applied to the table the loop builds, returns at most `n²`
raw permutations. -/
theorem length_rawEntries_rawBuildTable_le {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    (rawEntries (rawBuildTable (dom, gens.map (encPerm n)))).length ≤ n * n := by
  rw [rawBuildTable_spec dom hdom gens, rawEntries_encMTable, List.length_map]
  exact length_entriesList_buildTable_le n gens

end Algo
