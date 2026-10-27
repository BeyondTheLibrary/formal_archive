/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the `j`-th coset representative of an arbitrary subgroup, indexed in
binary.
-/
import Workspace.Algo.ChainTransversal
import Workspace.Algo.Luks
import Workspace.Algo.CosetUnion

/-!
# Coset representatives of an arbitrary subgroup, indexed in binary

Proposition 11.1.6 (Descent) lets "`σ` range over a set of right coset representatives of `H`
in `G`" for an arbitrary subgroup `H ≤ G`, and Eq. (64) does the same for a normal subgroup `N`.
`Workspace/Algo/ChainTransversal.lean` gives the `j`-th representative, in time polynomial in
the input and `log j`, when the subgroup is the kernel of the restriction to a window.  This
file does the same for an **arbitrary** subgroup given by generators.  With it the descent costs
a polynomial amount of work per instance handed on, as Theorem 11.1.9 does.

## The recursion

Write `A_i = G^{(i)}` for the `i`-th group of the point stabilizer chain of `G` (the pointwise
stabilizer of `0, …, i−1`), and let `K ≤ A_i`.  Row `i` of the table of `G` is a list of
elements `τ ∈ A_i`, one for each point `τ(i)` of the `A_i`-orbit of `i`.  For `x ∈ A_i` the
left coset `xK` determines the `K`-orbit of `x⁻¹(i)`, since `(xk)⁻¹(i) = k⁻¹(x⁻¹(i))`.  Choose,
for each `K`-orbit in the `A_i`-orbit of `i`, the row entry `τ` whose image `m = τ(i)` is the
least point of that orbit.  Then

* the left cosets `xK` with `x⁻¹(i)` in the orbit of `m` are the cosets `a τ⁻¹ K` with
  `a ∈ A_{i+1}`, and `a τ⁻¹ K = b τ⁻¹ K` exactly when `b⁻¹a ∈ K' = τ⁻¹ K_m τ ≤ A_{i+1}`;
* so a left transversal of `K` in `A_i` is the union over the chosen `τ` of
  `{a τ⁻¹ : a ∈ T(A_{i+1}, K')}`, and `|A_i : K| = ∑_τ |A_{i+1} : K'_τ|`
  (`Algo.sum_trCounts`).

The `j`-th representative walks down the chain: at level `i` it finds the chosen `τ` whose block
of indices contains `j`, replaces `K` by `K'_τ` and `j` by its offset in the block, and
multiplies `τ⁻¹` onto the product.  Every level costs a polynomial number of group operations,
and there are `n` levels.

## Main results

* `Algo.sum_trCounts` — the counting identity above;
* `Algo.trFold_cover` — the representatives cover: every `x ∈ A_i` lies in `R_j K` for some
  `j < |A_i : K|`;
* `Algo.trRep_cover` — **for `H ≤ G`, `G = ⋃_{j < |G : H|} R_j H`**, the left-coset form of the
  decomposition `G = ⋃_σ Hσ` of Prop. 11.1.6 (the representatives are distinct modulo `H`,
  since `|G : H|` of them cover `G`);
* `Algo.polyFun_trRep` — the routine is a `RAM.PolyFun`; the index `j` is a machine natural.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The mathematics of one level -/

section Level

variable (gens : List (Perm (Fin n)))

/-- `q` is the least point of its `K`-orbit. -/
def MinIn (K : Subgroup (Perm (Fin n))) (q : Fin n) : Prop := ∀ g ∈ K, (q : ℕ) ≤ (g q : ℕ)

/-- The points of the `K`-orbit of `q`, as a finset. -/
noncomputable def orbFin (K : Subgroup (Perm (Fin n))) (q : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun y => ∃ g ∈ K, g q = y)

theorem mem_orbFin {K : Subgroup (Perm (Fin n))} {q y : Fin n} :
    y ∈ orbFin K q ↔ ∃ g ∈ K, g q = y := by
  classical
  unfold orbFin
  simp

/-- The pointwise stabilizer of one point. -/
abbrev ptStab (K : Subgroup (Perm (Fin n))) (q : Fin n) : Subgroup (Perm (Fin n)) :=
  Babai.pointwiseStabilizer K {q}

/-- **Orbit–stabilizer**: `|K q| · |K_q| = |K|`. -/
theorem card_orbFin_mul (K : Subgroup (Perm (Fin n))) (q : Fin n) :
    (orbFin K q).card * Nat.card (ptStab K q) = Nat.card K := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K q
  have e1 : Fintype.card (MulAction.orbit K q) = (orbFin K q).card := by
    rw [← Set.toFinset_card]
    congr 1
    ext y
    rw [Set.mem_toFinset, mem_orbFin, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  have e2 : Fintype.card (MulAction.stabilizer K q) = Nat.card (ptStab K q) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ?_
    refine
      { toFun := fun g => ⟨((g : K) : Perm (Fin n)), (g : K).2, by
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact (MulAction.mem_stabilizer_iff.1 g.2)⟩
        invFun := fun g => ⟨⟨g, (Babai.mem_pointwiseStabilizer.1 g.2).1⟩,
          MulAction.mem_stabilizer_iff.2 ((Babai.mem_pointwiseStabilizer.1 g.2).2 q rfl)⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  rw [e1] at h
  rw [← e2, Nat.card_eq_fintype_card]
  exact h

/-- The point `i` of `Fin n`. -/
abbrev pt (i : ℕ) (hi : i < n) : Fin n := ⟨i, hi⟩

/-- The child subgroup `K' = τ⁻¹ K_{τ(i)} τ`. -/
noncomputable def childGrp (K : Subgroup (Perm (Fin n))) (τ : Perm (Fin n)) (i : ℕ)
    (hi : i < n) : Subgroup (Perm (Fin n)) :=
  (ptStab K (τ (pt i hi))).map (MulAut.conj τ⁻¹).toMonoidHom

theorem card_childGrp (K : Subgroup (Perm (Fin n))) (τ : Perm (Fin n)) (i : ℕ) (hi : i < n) :
    Nat.card (childGrp K τ i hi) = Nat.card (ptStab K (τ (pt i hi))) :=
  card_map_conj _ _

theorem mem_childGrp {K : Subgroup (Perm (Fin n))} {τ : Perm (Fin n)} {i : ℕ} {hi : i < n}
    {y : Perm (Fin n)} :
    y ∈ childGrp K τ i hi ↔ τ * y * τ⁻¹ ∈ ptStab K (τ (pt i hi)) := by
  unfold childGrp
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    show τ * (τ⁻¹ * k * τ⁻¹⁻¹) * τ⁻¹ ∈ _
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨τ * y * τ⁻¹, h, ?_⟩
    show τ⁻¹ * (τ * y * τ⁻¹) * τ⁻¹⁻¹ = y
    simp [mul_assoc]

/-- An element of `A_i` fixing `i` lies in `A_{i+1}`. -/
theorem mem_chainStab_succ {G : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n) {y : Perm (Fin n)}
    (hy : y ∈ chainStab G i) (hfix : y (pt i hi) = pt i hi) : y ∈ chainStab G (i + 1) := by
  refine mem_chainStab.2 ⟨(mem_chainStab.1 hy).1, fun k hk => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
  · exact (mem_chainStab.1 hy).2 k hk
  · have : k = pt i hi := Fin.ext hk
    rw [this]; exact hfix

/-- **The child subgroup lies in `A_{i+1}`.** -/
theorem childGrp_le {G K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab G i) {τ : Perm (Fin n)} (hτ : τ ∈ chainStab G i) :
    childGrp K τ i hi ≤ chainStab G (i + 1) := by
  intro y hy
  rw [mem_childGrp, Babai.mem_pointwiseStabilizer] at hy
  obtain ⟨hk, hfix⟩ := hy
  have hfix' := hfix (τ (pt i hi)) rfl
  have hyeq : y = τ⁻¹ * (τ * y * τ⁻¹) * τ := by group
  have hA : y ∈ chainStab G i := by
    rw [hyeq]
    exact mul_mem (mul_mem (inv_mem hτ) (hK hk)) hτ
  refine mem_chainStab_succ hi hA ?_
  have : (τ * y * τ⁻¹) (τ (pt i hi)) = τ (y (pt i hi)) := by simp [Equiv.Perm.mul_apply]
  rw [hfix'] at this
  exact τ.injective this.symm

variable {gens}

/-- Row entries lie in `A_i`. -/
theorem row_mem {i : ℕ} {τ : Perm (Fin n)} (h : τ ∈ rowPerms n gens i) :
    τ ∈ chainStab (genGroup gens) i :=
  rowPerms_subset_chainStab n gens i h

/-- **Every point of the `A_i`-orbit of `i` is the image of `i` under a row entry.** -/
theorem row_surj {i : ℕ} (hi : i < n) {σ : Perm (Fin n)} (hσ : σ ∈ chainStab (genGroup gens) i) :
    ∃ τ ∈ rowPerms n gens i, τ (pt i hi) = σ (pt i hi) := by
  obtain ⟨p, ⟨hp1, hp2, hp3⟩, -⟩ := rowPerms_transversal n gens (i := i) (k := n - i - 1)
    (by omega) hσ
  refine ⟨p.1, hp1, ?_⟩
  have hfix : p.2 (pt i hi) = pt i hi := (mem_chainStab.1 hp2).2 (pt i hi) (by simp)
  rw [hp3, Equiv.Perm.mul_apply, hfix]

/-- **Row entries are determined by the image of `i`.** -/
theorem row_inj {i : ℕ} (hi : i < n) {τ τ' : Perm (Fin n)} (hτ : τ ∈ rowPerms n gens i)
    (hτ' : τ' ∈ rowPerms n gens i) (h : τ (pt i hi) = τ' (pt i hi)) : τ = τ' := by
  have hA := row_mem hτ
  have hA' := row_mem hτ'
  obtain ⟨p, -, huniq⟩ := rowPerms_transversal n gens (i := i) (k := n - i - 1) (by omega) hA
  have hu : τ'⁻¹ * τ ∈ chainStab (genGroup gens) (i + 1) := by
    refine mem_chainStab_succ hi (mul_mem (inv_mem hA') hA) ?_
    rw [Equiv.Perm.mul_apply, h]; simp
  have h1 := huniq (τ, 1) ⟨hτ, one_mem _, by simp⟩
  have h2 := huniq (τ', τ'⁻¹ * τ) ⟨hτ', hu, by simp⟩
  have := h1.trans h2.symm
  rw [Prod.mk.injEq] at this
  exact this.1

/-- The chosen row entries: those whose image of `i` is least in its `K`-orbit. -/
noncomputable def repsOf (K : Subgroup (Perm (Fin n))) (i : ℕ) (hi : i < n) :
    List (Perm (Fin n)) := by
  classical exact (rowPerms n gens i).filter (fun τ => decide (MinIn K (τ (pt i hi))))

theorem mem_repsOf {K : Subgroup (Perm (Fin n))} {i : ℕ} {hi : i < n} {τ : Perm (Fin n)} :
    τ ∈ repsOf (gens := gens) K i hi ↔ τ ∈ rowPerms n gens i ∧ MinIn K (τ (pt i hi)) := by
  classical
  unfold repsOf
  simp

theorem nodup_repsOf (K : Subgroup (Perm (Fin n))) (i : ℕ) (hi : i < n) :
    (repsOf (gens := gens) K i hi).Nodup := by
  classical
  exact (nodup_rowPerms n gens i).filter _

/-- The orbit of an image of `i` under `K ≤ A_i` stays in the `A_i`-orbit of `i`. -/
theorem orbFin_sub {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) {τ : Perm (Fin n)}
    (hτ : τ ∈ chainStab (genGroup gens) i) {y : Fin n} (hy : y ∈ orbFin K (τ (pt i hi))) :
    ∃ s ∈ rowPerms n gens i, s (pt i hi) = y := by
  obtain ⟨g, hg, rfl⟩ := mem_orbFin.1 hy
  obtain ⟨s, hs, hse⟩ := row_surj (gens := gens) hi (mul_mem (hK hg) hτ)
  exact ⟨s, hs, by rw [hse, Equiv.Perm.mul_apply]⟩

/-- **The orbits of the chosen entries partition the `A_i`-orbit of `i`**:
`∑_τ |K τ(i)| = |row i|`. -/
theorem sum_card_orbFin {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) :
    ((repsOf (gens := gens) K i hi).map (fun τ => (orbFin K (τ (pt i hi))).card)).sum
      = (rowPerms n gens i).length := by
  classical
  set R := repsOf (gens := gens) K i hi with hRdef
  set P : Finset (Fin n) := ((rowPerms n gens i).map (fun τ => τ (pt i hi))).toFinset with hP
  have hPcard : P.card = (rowPerms n gens i).length := by
    rw [hP, List.toFinset_card_of_nodup, List.length_map]
    refine (List.nodup_map_iff_inj_on (nodup_rowPerms n gens i)).2 ?_
    intro a ha b hb hab
    exact row_inj hi ha hb hab
  have hunion : P = R.toFinset.biUnion (fun τ => orbFin K (τ (pt i hi))) := by
    ext y
    rw [Finset.mem_biUnion, hP, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hne : (orbFin K (s (pt i hi))).Nonempty :=
        ⟨s (pt i hi), mem_orbFin.2 ⟨1, one_mem _, rfl⟩⟩
      set m := (orbFin K (s (pt i hi))).min' hne with hm
      have hmmem : m ∈ orbFin K (s (pt i hi)) := Finset.min'_mem _ hne
      obtain ⟨t, ht, hte⟩ := orbFin_sub (gens := gens) hi hK (row_mem hs) hmmem
      obtain ⟨k, hk, hkm⟩ := mem_orbFin.1 hmmem
      refine ⟨t, List.mem_toFinset.2 (mem_repsOf.2 ⟨ht, ?_⟩), ?_⟩
      · intro g hg
        rw [hte]
        have : g m ∈ orbFin K (s (pt i hi)) := by
          rw [← hkm]
          exact mem_orbFin.2 ⟨g * k, mul_mem hg hk, by simp [Equiv.Perm.mul_apply]⟩
        have := Finset.min'_le _ _ this
        exact this
      · rw [hte]
        refine mem_orbFin.2 ⟨k⁻¹, inv_mem hk, ?_⟩
        rw [← hkm]; simp
    · rintro ⟨t, ht, hy⟩
      have ht' := (mem_repsOf.1 (List.mem_toFinset.1 ht)).1
      exact orbFin_sub (gens := gens) hi hK (row_mem ht') hy
  have hdisj : (R.toFinset : Set (Perm (Fin n))).PairwiseDisjoint
      (fun τ => orbFin K (τ (pt i hi))) := by
    intro t ht s hs hts
    rw [Function.onFun, Finset.disjoint_left]
    intro y hyt hys
    apply hts
    have ht' := mem_repsOf.1 (List.mem_toFinset.1 ht)
    have hs' := mem_repsOf.1 (List.mem_toFinset.1 hs)
    obtain ⟨g, hg, hgy⟩ := mem_orbFin.1 hyt
    obtain ⟨h, hh, hhy⟩ := mem_orbFin.1 hys
    -- `s(i) = h⁻¹ g t(i)` and `t(i) = g⁻¹ h s(i)`
    have e1 : s (pt i hi) = (h⁻¹ * g) (t (pt i hi)) := by
      rw [Equiv.Perm.mul_apply, hgy, ← hhy]; simp
    have e2 : t (pt i hi) = (g⁻¹ * h) (s (pt i hi)) := by
      rw [Equiv.Perm.mul_apply, hhy, ← hgy]; simp
    have l1 := ht'.2 (h⁻¹ * g) (mul_mem (inv_mem hh) hg)
    have l2 := hs'.2 (g⁻¹ * h) (mul_mem (inv_mem hg) hh)
    rw [← e1] at l1
    rw [← e2] at l2
    exact row_inj hi ht'.1 hs'.1 (Fin.ext (le_antisymm l1 l2))
  rw [← hPcard, hunion, Finset.card_biUnion hdisj, List.sum_toFinset _ (nodup_repsOf K i hi)]

/-- The number of representatives below a chosen entry `τ`: `|A_{i+1} : K'_τ|`. -/
noncomputable def trCountM (gs : List (Perm (Fin n))) (K : Subgroup (Perm (Fin n))) (i : ℕ)
    (hi : i < n) (τ : Perm (Fin n)) : ℕ :=
  Nat.card (chainStab (genGroup gs) (i + 1)) / Nat.card (childGrp K τ i hi)

theorem trCountM_mul {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) {τ : Perm (Fin n)}
    (hτ : τ ∈ chainStab (genGroup gens) i) :
    trCountM gens K i hi τ * Nat.card (childGrp K τ i hi)
      = Nat.card (chainStab (genGroup gens) (i + 1)) :=
  Nat.div_mul_cancel (Subgroup.card_dvd_of_le (childGrp_le hi hK hτ))

theorem trCountM_eq_relIndex {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) {τ : Perm (Fin n)}
    (hτ : τ ∈ chainStab (genGroup gens) i) :
    trCountM gens K i hi τ = (childGrp K τ i hi).relIndex (chainStab (genGroup gens) (i + 1)) := by
  have h1 := trCountM_mul hi hK hτ
  have h2 := Babai.relIndex_mul_card_of_le (childGrp_le hi hK hτ)
  have hpos : 0 < Nat.card (childGrp K τ i hi) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

/-- **The counting identity** `∑_τ |A_{i+1} : K'_τ| = |A_i : K|`. -/
theorem sum_trCounts {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) :
    ((repsOf (gens := gens) K i hi).map (trCountM gens K i hi)).sum
      = K.relIndex (chainStab (genGroup gens) i) := by
  have hKpos : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hKpos ?_
  rw [Babai.relIndex_mul_card_of_le hK, card_chainStab_succ n gens hi, ← List.sum_map_mul_right]
  have hterm : ∀ τ ∈ repsOf (gens := gens) K i hi,
      trCountM gens K i hi τ * Nat.card K
        = Nat.card (chainStab (genGroup gens) (i + 1)) * (orbFin K (τ (pt i hi))).card := by
    intro τ hτ
    have hτA := row_mem (mem_repsOf.1 hτ).1
    rw [← card_orbFin_mul K (τ (pt i hi)), ← card_childGrp K τ i hi,
      ← trCountM_mul hi hK hτA]
    ring
  rw [List.map_congr_left hterm, List.sum_map_mul_left, sum_card_orbFin hi hK, chainRadix]
  ring

/-- **Each point of the `A_i`-orbit of `i` is `k τ(i)` for a chosen entry `τ` and `k ∈ K`.** -/
theorem exists_rep {K : Subgroup (Perm (Fin n))} {i : ℕ} (hi : i < n)
    (hK : K ≤ chainStab (genGroup gens) i) {σ : Perm (Fin n)}
    (hσ : σ ∈ chainStab (genGroup gens) i) :
    ∃ τ ∈ repsOf (gens := gens) K i hi, ∃ k ∈ K, k (τ (pt i hi)) = σ (pt i hi) := by
  classical
  obtain ⟨s, hs, hse⟩ := row_surj (gens := gens) hi hσ
  have hne : (orbFin K (s (pt i hi))).Nonempty :=
    ⟨s (pt i hi), mem_orbFin.2 ⟨1, one_mem _, rfl⟩⟩
  set m := (orbFin K (s (pt i hi))).min' hne with hm
  have hmmem : m ∈ orbFin K (s (pt i hi)) := Finset.min'_mem _ hne
  obtain ⟨t, ht, hte⟩ := orbFin_sub (gens := gens) hi hK (row_mem hs) hmmem
  obtain ⟨k, hk, hkm⟩ := mem_orbFin.1 hmmem
  refine ⟨t, mem_repsOf.2 ⟨ht, ?_⟩, k⁻¹, inv_mem hk, ?_⟩
  · intro g hg
    rw [hte]
    have : g m ∈ orbFin K (s (pt i hi)) := by
      rw [← hkm]
      exact mem_orbFin.2 ⟨g * k, mul_mem hg hk, by simp [Equiv.Perm.mul_apply]⟩
    exact Finset.min'_le _ _ this
  · rw [hte, ← hse, ← hkm]; simp

end Level

/-! ## Selecting the block of an index -/

section Select

variable {α : Type*}

/-- One step of the selection: skip the block of `a` if the index lies beyond it. -/
def selStepG (cnt : α → ℕ) (y : ℕ × Option α) (a : α) : ℕ × Option α :=
  if y.2.isSome then y else if y.1 < cnt a then (y.1, some a) else (y.1 - cnt a, none)

theorem selG_frozen (cnt : α → ℕ) : ∀ (l : List α) (j : ℕ) (a : α),
    l.foldl (selStepG cnt) (j, some a) = (j, some a) := by
  intro l
  induction l with
  | nil => intro j a; rfl
  | cons b l ih => intro j a; rw [List.foldl_cons]; exact ih j a

/-- **The selection finds the block**: the index `∑_{t < s} cnt(a_t) + j'` with `j' < cnt(a_s)`
selects `a_s` with offset `j'`. -/
theorem selG_pick (cnt : α → ℕ) : ∀ (l : List α) (s j' : ℕ) (hs : s < l.length),
    j' < cnt (l[s]) →
    l.foldl (selStepG cnt) (((l.take s).map cnt).sum + j', none) = (j', some l[s]) := by
  intro l
  induction l with
  | nil => intro s j' hs; simp at hs
  | cons b l ih =>
      intro s j' hs hj
      rw [List.foldl_cons]
      cases s with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add,
            List.getElem_cons_zero] at hj ⊢
          have : selStepG cnt (j', none) b = (j', some b) := by
            simp [selStepG, hj]
          rw [this, selG_frozen]
      | succ s =>
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
            List.getElem_cons_succ] at hj ⊢
          have : selStepG cnt (cnt b + ((l.take s).map cnt).sum + j', none) b
              = (((l.take s).map cnt).sum + j', none) := by
            simp only [selStepG, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            rw [if_neg (by omega)]
            congr 1
            omega
          rw [add_assoc, ← add_assoc (cnt b), this]
          exact ih s j' (by simp at hs; omega) hj

/-- The selection returns an entry of the list, or nothing. -/
theorem selG_mem (cnt : α → ℕ) : ∀ (l : List α) (y : ℕ × Option α),
    (l.foldl (selStepG cnt) y) = y ∨
      ((l.foldl (selStepG cnt) y).1 ≤ y.1 ∧
        ((l.foldl (selStepG cnt) y).2 = none ∨ ∃ a ∈ l, (l.foldl (selStepG cnt) y).2 = some a)) := by
  intro l
  induction l with
  | nil => intro y; left; rfl
  | cons b l ih =>
      intro y
      rw [List.foldl_cons]
      by_cases hy : y.2.isSome
      · have : selStepG cnt y b = y := by simp [selStepG, hy]
        rw [this]
        rcases ih y with h | ⟨h1, h2⟩
        · left; exact h
        · right
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨a, ha, h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, h2⟩
      · by_cases hlt : y.1 < cnt b
        · have : selStepG cnt y b = (y.1, some b) := by simp [selStepG, hy, hlt]
          rw [this, selG_frozen]
          right
          exact ⟨le_rfl, Or.inr ⟨b, List.mem_cons_self, rfl⟩⟩
        · have : selStepG cnt y b = (y.1 - cnt b, none) := by simp [selStepG, hy, hlt]
          rw [this]
          right
          rcases ih (y.1 - cnt b, none) with h | ⟨h1, h2⟩
          · rw [h]; exact ⟨Nat.sub_le _ _, Or.inl rfl⟩
          · refine ⟨le_trans h1 (Nat.sub_le _ _), ?_⟩
            rcases h2 with h2 | ⟨a, ha, h2⟩
            · exact Or.inl h2
            · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, h2⟩

end Select

/-! ## The routine -/

/-- `p.2` is the least point of its orbit under the group generated by `p.1`. -/
def trMinIn (p : RawGens × ℕ) : Bool :=
  ((rawOrbit p).filter (fun r => !decide (p.2 ≤ r))).isEmpty

/-- **The child generators** `τ⁻¹ K_{τ(i)} τ`, tidied.  `p = ((dom, K), (τ, i))`. -/
def trChild (p : (List ℕ × RawGens) × (RawPerm × ℕ)) : RawGens :=
  tidyGens (p.1.1, rawConj (p.2.1, rawPointStab (p.1, [rawApply (p.2.1, p.2.2)])))

/-- **The size of the block of `τ`**, `|A_{i+1}| / |K'_τ|`.  `p = (((dom, G), K), (τ, i))`. -/
def trCount (p : ((List ℕ × RawGens) × RawGens) × (RawPerm × ℕ)) : ℕ :=
  rawOrder (p.1.1.1, rawStab (p.1.1, p.2.2 + 1)) / rawOrder (p.1.1.1, trChild ((p.1.1.1, p.1.2), p.2))

/-- **The chosen entries of row `i`.**  `p = (((dom, G), K), i)`. -/
def trReps (p : ((List ℕ × RawGens) × RawGens) × ℕ) : List RawPerm :=
  (rawRow (p.1.1, p.2)).filter (fun τ => trMinIn (p.1.2, rawApply (τ, p.2)))

/-- One step of the selection, for the blocks of level `i`. -/
def trSelStep (p : (((List ℕ × RawGens) × RawGens) × ℕ) × ((ℕ × Option RawPerm) × RawPerm)) :
    ℕ × Option RawPerm :=
  selStepG (fun τ => trCount (p.1.1, (τ, p.1.2))) p.2.1 p.2.2

/-- **The block of the index at level `i`**: the chosen entry and the offset.
`p = ((((dom, G), K), i), j)`. -/
def trSel (p : (((List ℕ × RawGens) × RawGens) × ℕ) × ℕ) : ℕ × Option RawPerm :=
  List.foldl (fun y τ => trSelStep (p.1, (y, τ))) (p.2, none) (trReps p.1)

/-- **One level of the walk down the chain.**  `p = ((dom, G), (((K, j), acc), i))`. -/
def trStep (p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ)) :
    (RawGens × ℕ) × RawPerm :=
  ((trChild ((p.1.1, p.2.1.1.1),
      ((trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).2.getD (rawOne p.1.1), p.2.2)),
    (trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).1),
   normPerm (p.1.1, rawMul (rawInv ((trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).2.getD
      (rawOne p.1.1)), p.2.1.2)))

/-- **The walk**, one level per entry of `p.2.2`. -/
def trFold (p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ)) :
    (RawGens × ℕ) × RawPerm :=
  List.foldl (fun y l => trStep (p.1, (y, l))) p.2.1 p.2.2

/-- **The `j`-th left coset representative of `H` in `G`, indexed in binary.**
`p = (((dom, G), H), j)`.  Paper: the representatives `σ` of Prop. 11.1.6 (in the left-coset
form `G = ⋃ σ⁻¹ H`). -/
def trRep (p : ((List ℕ × RawGens) × RawGens) × ℕ) : RawPerm :=
  (trFold (p.1.1, (((p.1.2, p.2), rawOne p.1.1.1), rawOne p.1.1.1))).2

/-! ## The specification -/

section Spec

variable {dom : List ℕ} (hdom : dom.length = n)
include hdom

theorem normPerm_encPerm (c : Perm (Fin n)) : normPerm (dom, encPerm n c) = encPerm n c := by
  have h1 := wf_normPerm hdom (encPerm n c)
  rw [← encPerm_decPerm h1, decPerm_normPerm hdom, decPerm_encPerm]

omit hdom in
theorem trMinIn_eq {Kraw : RawGens} (hK : RawGens.WF n Kraw) {q : ℕ} (hq : q < n) :
    trMinIn (Kraw, q) = true ↔ MinIn (decGroup n Kraw) ⟨q, hq⟩ := by
  rw [trMinIn, List.isEmpty_iff, List.filter_eq_nil_iff]
  constructor
  · intro h g hg
    have hr : ((g ⟨q, hq⟩ : Fin n) : ℕ) ∈ rawOrbit (Kraw, q) :=
      (mem_rawOrbit_iff hK hq _).2 ⟨(g ⟨q, hq⟩).isLt, ⟨⟨g, hg⟩, rfl⟩⟩
    have := h _ hr
    simpa using this
  · intro h r hr
    obtain ⟨hrn, g, hg⟩ := (mem_rawOrbit_iff hK hq r).1 hr
    have := h g g.2
    have e : ((g : Perm (Fin n)) ⟨q, hq⟩ : ℕ) = r := by
      have := congrArg Fin.val hg
      simpa using this
    rw [e] at this
    simpa using this

omit hdom in
theorem trReps_eq (gens : List (Perm (Fin n))) (hdom : dom.length = n) {Kraw : RawGens}
    (hK : RawGens.WF n Kraw) {i : ℕ} (hi : i < n) :
    trReps (((dom, gens.map (encPerm n)), Kraw), i)
      = (repsOf (gens := gens) (decGroup n Kraw) i hi).map (encPerm n) := by
  classical
  rw [trReps, rawRow_spec dom hdom gens i, repsOf, List.filter_map]
  congr 1
  refine List.filter_congr (fun τ _ => ?_)
  simp only [Function.comp]
  rw [rawApply_encPerm n τ hi]
  by_cases h : MinIn (decGroup n Kraw) (τ (pt i hi))
  · rw [decide_eq_true h]
    exact (trMinIn_eq hK (τ (pt i hi)).isLt).2 h
  · rw [decide_eq_false h]
    cases hb : trMinIn (Kraw, ↑(τ ⟨i, hi⟩)) with
    | false => rfl
    | true => exact absurd ((trMinIn_eq hK (τ (pt i hi)).isLt).1 hb) h

theorem wf_trChild (Kraw : RawGens) (τ : RawPerm) (i : ℕ) :
    RawGens.WF n (trChild ((dom, Kraw), (τ, i))) :=
  wf_tidyGens hdom _

theorem decGroup_trChild {Kraw : RawGens} (hK : RawGens.WF n Kraw) (τ : Perm (Fin n)) {i : ℕ}
    (hi : i < n) :
    decGroup n (trChild ((dom, Kraw), (encPerm n τ, i))) = childGrp (decGroup n Kraw) τ i hi := by
  rw [trChild, decGroup_tidyGens hdom]
  set ks := Kraw.map (decPerm n) with hks
  have hKr : Kraw = ks.map (encPerm n) := (map_encPerm_decPerm hK).symm
  have hstab : rawPointStab ((dom, Kraw), [rawApply (encPerm n τ, i)])
      = rawPointStab ((dom, ks.map (encPerm n)), [rawApply (encPerm n τ, i)]) := by
    rw [← hKr]
  have hap : rawApply (encPerm n τ, i) = (τ (pt i hi) : ℕ) := rawApply_encPerm n τ hi
  have hdec := decGroup_rawPointStab dom hdom ks [rawApply (encPerm n τ, i)] (List.nodup_singleton _)
    (by intro x hx; rw [List.mem_singleton] at hx; rw [hx, hap]; exact (τ (pt i hi)).isLt)
  have hwfS : RawGens.WF n (rawPointStab ((dom, ks.map (encPerm n)), [rawApply (encPerm n τ, i)])) :=
    wf_rawPointStab hdom (List.nodup_singleton _)
      (by intro x hx; rw [List.mem_singleton] at hx; rw [hx, hap]; exact (τ (pt i hi)).isLt) ks
  set S := rawPointStab ((dom, ks.map (encPerm n)), [rawApply (encPerm n τ, i)]) with hS
  have hSr : S = (S.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hwfS).symm
  rw [hstab, hSr, rawConj_spec (wf_encPerm n τ), decGroup_map_encPerm, genGroup_map_conj,
    decPerm_encPerm, genGroup]
  have hS' : Subgroup.closure {x | x ∈ S.map (decPerm n)} = decGroup n S := rfl
  rw [hS', hdec]
  unfold childGrp ptStab
  congr 2
  · ext x
    simp only [Set.mem_setOf_eq, List.mem_singleton, Set.mem_singleton_iff, hap]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩

omit hdom in
theorem rawOrder_wf {gs : RawGens} (hgs : RawGens.WF n gs) (hdom : dom.length = n) :
    rawOrder (dom, gs) = Nat.card (decGroup n gs) := by
  have h := rawOrder_spec dom hdom (gs.map (decPerm n))
  rw [map_encPerm_decPerm hgs] at h
  exact h

theorem trCount_eq (gens : List (Perm (Fin n))) {Kraw : RawGens} (hK : RawGens.WF n Kraw)
    (τ : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    trCount (((dom, gens.map (encPerm n)), Kraw), (encPerm n τ, i))
      = trCountM gens (decGroup n Kraw) i hi τ := by
  have hS : RawGens.WF n (rawStab ((dom, gens.map (encPerm n)), i + 1)) := by
    rw [rawStab_spec dom hdom gens (i + 1)]
    intro g hg
    obtain ⟨h, -, rfl⟩ := List.mem_map.1 hg
    exact wf_encPerm n h
  rw [trCount, trCountM]
  simp only
  rw [rawOrder_wf hS hdom, decGroup_rawStab dom hdom gens (show i + 1 ≤ n by omega),
    rawOrder_wf (wf_trChild hdom Kraw _ i) hdom, decGroup_trChild hdom hK τ hi]

omit hdom in
theorem trSel_eq (p : (((List ℕ × RawGens) × RawGens) × ℕ) × ℕ) :
    trSel p = (trReps p.1).foldl (selStepG (fun τ => trCount (p.1.1, (τ, p.1.2)))) (p.2, none) :=
  rfl

/-- **The selection at one level.** -/
theorem trSel_pick (gens : List (Perm (Fin n))) {Kraw : RawGens} (hK : RawGens.WF n Kraw)
    {i : ℕ} (hi : i < n) {s j' : ℕ} (hs : s < (repsOf (gens := gens) (decGroup n Kraw) i hi).length)
    (hj' : j' < trCountM gens (decGroup n Kraw) i hi
      ((repsOf (gens := gens) (decGroup n Kraw) i hi)[s])) :
    trSel ((((dom, gens.map (encPerm n)), Kraw), i),
        (((repsOf (gens := gens) (decGroup n Kraw) i hi).take s).map
          (trCountM gens (decGroup n Kraw) i hi)).sum + j')
      = (j', some (encPerm n ((repsOf (gens := gens) (decGroup n Kraw) i hi)[s]))) := by
  rw [trSel_eq]
  simp only
  rw [trReps_eq gens hdom hK hi]
  set L := repsOf (gens := gens) (decGroup n Kraw) i hi with hL
  set cnt : RawPerm → ℕ := fun τ => trCount ((((dom, gens.map (encPerm n)), Kraw)), (τ, i))
    with hcnt
  have hce : ∀ τ : Perm (Fin n), cnt (encPerm n τ) = trCountM gens (decGroup n Kraw) i hi τ :=
    fun τ => trCount_eq hdom gens hK τ hi
  have hs' : s < (L.map (encPerm n)).length := by rw [List.length_map]; exact hs
  have hsum : ((L.take s).map (trCountM gens (decGroup n Kraw) i hi)).sum
      = (((L.map (encPerm n)).take s).map cnt).sum := by
    rw [← List.map_take, List.map_map]
    congr 1
    refine List.map_congr_left (fun τ _ => ?_)
    exact (hce τ).symm
  have hj'' : j' < cnt ((L.map (encPerm n))[s]) := by
    rw [List.getElem_map, hce]; exact hj'
  rw [hsum, selG_pick cnt (L.map (encPerm n)) s j' hs' hj'', List.getElem_map]

/-- **One level of the walk, on a chosen entry.** -/
theorem trStep_pick (gens : List (Perm (Fin n))) {Kraw : RawGens} (hK : RawGens.WF n Kraw)
    {i : ℕ} (hi : i < n) {s j' : ℕ} (hs : s < (repsOf (gens := gens) (decGroup n Kraw) i hi).length)
    (hj' : j' < trCountM gens (decGroup n Kraw) i hi
      ((repsOf (gens := gens) (decGroup n Kraw) i hi)[s])) (c : Perm (Fin n)) :
    trStep ((dom, gens.map (encPerm n)), (((Kraw,
        (((repsOf (gens := gens) (decGroup n Kraw) i hi).take s).map
          (trCountM gens (decGroup n Kraw) i hi)).sum + j'), encPerm n c), i))
      = ((trChild ((dom, Kraw),
            (encPerm n ((repsOf (gens := gens) (decGroup n Kraw) i hi)[s]), i)), j'),
          encPerm n (((repsOf (gens := gens) (decGroup n Kraw) i hi)[s])⁻¹ * c)) := by
  rw [trStep]
  simp only
  rw [trSel_pick hdom gens hK hi hs hj']
  simp only [Option.getD_some]
  rw [rawInv_encPerm, rawMul_encPerm, normPerm_encPerm hdom]

/-- **The representatives cover**: for `K ≤ A_i` given by well-formed generators, every
`x ∈ A_i` lies in `R K` for the representative `R` of some index `j < |A_i : K|`. -/
theorem trFold_cover (gens : List (Perm (Fin n))) :
    ∀ (k i : ℕ), i + k = n → ∀ (Kraw : RawGens), RawGens.WF n Kraw →
      decGroup n Kraw ≤ chainStab (genGroup gens) i →
      ∀ x ∈ chainStab (genGroup gens) i,
        ∃ j < (decGroup n Kraw).relIndex (chainStab (genGroup gens) i), ∃ R : Perm (Fin n),
          R⁻¹ * x ∈ decGroup n Kraw ∧ ∀ c : Perm (Fin n),
            (List.foldl (fun y l => trStep ((dom, gens.map (encPerm n)), (y, l)))
              ((Kraw, j), encPerm n c) (List.range' i k)).2 = encPerm n (R * c) := by
  intro k
  induction k with
  | zero =>
      intro i hik Kraw hK hle x hx
      have hi : i = n := by omega
      subst hi
      rw [chainStab_degree] at hle hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      refine ⟨0, ?_, 1, by simp, fun c => by simp⟩
      rw [chainStab_degree, Subgroup.relIndex_bot_right]
      exact Nat.one_pos
  | succ k ih =>
      intro i hik Kraw hK hle x hx
      have hi : i < n := by omega
      set K := decGroup n Kraw with hKdef
      set L := repsOf (gens := gens) K i hi with hL
      obtain ⟨t, ht, g, hg, hgt⟩ := exists_rep (gens := gens) hi hle (inv_mem hx)
      obtain ⟨s, hs, hst⟩ := List.getElem_of_mem ht
      have htA : t ∈ chainStab (genGroup gens) i := row_mem (mem_repsOf.1 ht).1
      -- the element `y = x g t` fixes `i`
      set y := x * g * t with hy
      have hyA : y ∈ chainStab (genGroup gens) (i + 1) := by
        refine mem_chainStab_succ hi (mul_mem (mul_mem hx (hle hg)) htA) ?_
        rw [hy, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgt]
        simp
      set Kraw' := trChild ((dom, Kraw), (encPerm n t, i)) with hK'
      have hK'wf : RawGens.WF n Kraw' := wf_trChild hdom Kraw _ i
      have hK'eq : decGroup n Kraw' = childGrp K t i hi := decGroup_trChild hdom hK t hi
      have hK'le : decGroup n Kraw' ≤ chainStab (genGroup gens) (i + 1) := by
        rw [hK'eq]; exact childGrp_le hi hle htA
      obtain ⟨j', hj', R', hR', hfold⟩ := ih (i + 1) (by omega) Kraw' hK'wf hK'le y hyA
      have hcnt : trCountM gens K i hi t = (decGroup n Kraw').relIndex
          (chainStab (genGroup gens) (i + 1)) := by
        rw [hK'eq]; exact trCountM_eq_relIndex hi hle htA
      have hj't : j' < trCountM gens K i hi L[s] := by rw [hst, hcnt]; exact hj'
      refine ⟨((L.take s).map (trCountM gens K i hi)).sum + j', ?_, R' * t⁻¹, ?_, ?_⟩
      · -- the index is below `|A_i : K|`
        rw [← sum_trCounts (gens := gens) hi hle, ← hL]
        have hsplit : L = L.take s ++ L[s] :: L.drop (s + 1) := by
          rw [← List.drop_eq_getElem_cons hs, List.take_append_drop]
        have e := congrArg (fun l => (l.map (trCountM gens K i hi)).sum) hsplit
        simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at e
        omega
      · -- `R⁻¹ x ∈ K`
        rw [hK'eq, mem_childGrp, Babai.mem_pointwiseStabilizer] at hR'
        have hk := hR'.1
        have : (R' * t⁻¹)⁻¹ * x = (t * (R'⁻¹ * y) * t⁻¹) * g⁻¹ := by
          rw [hy]; group
        rw [this]
        exact mul_mem hk (inv_mem hg)
      · intro c
        rw [show List.range' i (k + 1) = i :: List.range' (i + 1) k from rfl, List.foldl_cons,
          trStep_pick hdom gens hK hi hs hj't c]
        rw [hst, ← hK']
        rw [hfold (t⁻¹ * c), mul_assoc]

/-- **Every representative lies in `G`**: the walk multiplies entries of the table of `G` (or
the identity) onto the product. -/
theorem trFold_mem (gens : List (Perm (Fin n))) :
    ∀ (l : List ℕ) (st : (RawGens × ℕ) × RawPerm) (c : Perm (Fin n)), c ∈ genGroup gens →
      st.2 = encPerm n c →
      ∃ c' ∈ genGroup gens,
        (List.foldl (fun y l => trStep ((dom, gens.map (encPerm n)), (y, l))) st l).2
          = encPerm n c' := by
  intro l
  induction l with
  | nil => intro st c hc hst; exact ⟨c, hc, hst⟩
  | cons a l ih =>
      intro st c hc hst
      rw [List.foldl_cons]
      set sel := trSel ((((dom, gens.map (encPerm n)), st.1.1), a), st.1.2) with hsel
      have hτ : ∃ u ∈ genGroup gens, sel.2.getD (rawOne dom) = encPerm n u := by
        have hm := selG_mem (fun τ => trCount ((((dom, gens.map (encPerm n)), st.1.1)), (τ, a)))
          (trReps (((dom, gens.map (encPerm n)), st.1.1), a)) (st.1.2, none)
        have hse : sel = List.foldl (selStepG (fun τ => trCount ((((dom, gens.map (encPerm n)),
            st.1.1)), (τ, a)))) (st.1.2, none) (trReps (((dom, gens.map (encPerm n)), st.1.1), a)) :=
          trSel_eq _
        rw [← hse] at hm
        have hnone : sel.2 = none → sel.2.getD (rawOne dom) = encPerm n 1 := by
          intro h; rw [h, Option.getD_none, rawOne_eq, hdom]
        rcases hm with h | ⟨-, h | ⟨τ, hτmem, h⟩⟩
        · exact ⟨1, one_mem _, hnone (by rw [h])⟩
        · exact ⟨1, one_mem _, hnone h⟩
        · rw [h, Option.getD_some]
          rw [trReps] at hτmem
          have hrow := (List.mem_filter.1 hτmem).1
          rw [rawRow_spec dom hdom gens a] at hrow
          obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hrow
          exact ⟨u, chainStab_le _ a (row_mem hu), rfl⟩
      obtain ⟨u, hu, hue⟩ := hτ
      refine ih _ (u⁻¹ * c) (mul_mem (inv_mem hu) hc) ?_
      show normPerm (dom, rawMul (rawInv (sel.2.getD (rawOne dom)), st.2)) = _
      rw [hue, hst, rawInv_encPerm, rawMul_encPerm, normPerm_encPerm hdom]

/-- **The representatives of `H` in `G`**: for `H ≤ G`, the `|G : H|` representatives
`R_j = Algo.trRep (((dom, G), H), j)` satisfy `G = ⋃_{j < |G : H|} R_j H`.  Paper: Prop. 11.1.6,
"We can write `G = ⋃_σ Hσ` where `σ` ranges over a set of right coset representatives of `H` in
`G`" (the right cosets `Hσ` of the paper are the left cosets `σ⁻¹H` here). -/
theorem trRep_cover (gensG gensH : List (Perm (Fin n)))
    (hle : genGroup gensH ≤ genGroup gensG) :
    (genGroup gensG : Set (Perm (Fin n)))
      = ⋃ j ∈ List.range ((genGroup gensH).relIndex (genGroup gensG)),
          decPerm n (trRep (((dom, gensG.map (encPerm n)), gensH.map (encPerm n)), j)) •
            (genGroup gensH : Set (Perm (Fin n))) := by
  have hHwf : RawGens.WF n (gensH.map (encPerm n)) := by
    intro g hg
    obtain ⟨h, -, rfl⟩ := List.mem_map.1 hg
    exact wf_encPerm n h
  have hlev : rawOne dom = List.range' 0 n := by
    rw [rawOne, hdom, List.range_eq_range']
  have hone : rawOne dom = encPerm n 1 := by rw [rawOne_eq, hdom]
  have hunf : ∀ j, trRep (((dom, gensG.map (encPerm n)), gensH.map (encPerm n)), j)
      = (List.foldl (fun y l => trStep ((dom, gensG.map (encPerm n)), (y, l)))
          ((gensH.map (encPerm n), j), encPerm n 1) (List.range' 0 n)).2 := by
    intro j
    show (trFold ((dom, gensG.map (encPerm n)),
      (((gensH.map (encPerm n), j), rawOne dom), rawOne dom))).2 = _
    rw [trFold]
    simp only
    rw [← hone, ← hlev]
  ext x
  simp only [Set.mem_iUnion, List.mem_range, SetLike.mem_coe, exists_prop]
  constructor
  · intro hx
    have hle0 : decGroup n (gensH.map (encPerm n)) ≤ chainStab (genGroup gensG) 0 := by
      rw [chainStab_zero, decGroup_map_encPerm]; exact hle
    have hx0 : x ∈ chainStab (genGroup gensG) 0 := by rw [chainStab_zero]; exact hx
    obtain ⟨j, hj, R, hR, hfold⟩ :=
      trFold_cover hdom gensG n 0 (by omega) _ hHwf hle0 x hx0
    rw [decGroup_map_encPerm, chainStab_zero] at hj
    rw [decGroup_map_encPerm] at hR
    refine ⟨j, hj, ?_⟩
    rw [hunf, hfold 1, mul_one, decPerm_encPerm, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    exact hR
  · rintro ⟨j, -, hx⟩
    obtain ⟨c, hc, hce⟩ := trFold_mem hdom gensG (List.range' 0 n)
      ((gensH.map (encPerm n), j), encPerm n 1) 1 (one_mem _) rfl
    rw [hunf, hce, decPerm_encPerm, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact mul_mem hc (hle hx)

end Spec

/-! ## The running time -/

section Poly

theorem trPolyBound_strBound : PolyBound strBound :=
  (polyBound_const 1).add (polyBound_id.mul
    (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
      (polyBound_const 1)))

theorem trPolyBound_gensBound : PolyBound gensBound :=
  (polyBound_const 1).add ((polyBound_id.mul polyBound_id).mul
    (((polyBound_const 2).mul trPolyBound_strBound).add (polyBound_const 1)))

theorem trMono_strBound : Monotone strBound := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul hab (by omega)) 1

theorem trMono_gensBound : Monotone gensBound := by
  intro a b hab
  exact Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.mul_le_mul hab hab) (by have := trMono_strBound hab; omega)) 1

theorem polyFun_notLe : PolyFun (fun z : ℕ × ℕ => !decide (z.1 ≤ z.2)) :=
  (PolyFun.ite polyFun_le (polyFun_const false) (polyFun_const true)).of_eq
    (fun z => by by_cases h : z.1 ≤ z.2 <;> simp [h])

theorem polyFun_trIsSome {β : Type*} [Enc β] : PolyFun (fun o : Option β => o.isSome) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const false) (polyFun_const true))).of_eq
      (fun o => by cases o <;> rfl)

theorem polyFun_trMinIn : PolyFun trMinIn := by
  have hf := PolyFun.filterParam (α := ℕ) (γ := ℕ) polyFun_notLe
  exact (((polyFun_snd.pair polyFun_rawOrbit).comp hf).comp polyFun_isEmpty).of_eq
    (fun _ => rfl)

theorem polyFun_trChild : PolyFun trChild := by
  have hap : PolyFun (fun p : (List ℕ × RawGens) × (RawPerm × ℕ) => rawApply (p.2.1, p.2.2)) :=
    polyFun_snd.comp polyFun_rawApply
  have hsing : PolyFun (fun p : (List ℕ × RawGens) × (RawPerm × ℕ) => [rawApply (p.2.1, p.2.2)]) :=
    (hap.pair polyFun_nil).comp polyFun_cons
  have hst : PolyFun (fun p : (List ℕ × RawGens) × (RawPerm × ℕ) =>
      rawPointStab (p.1, [rawApply (p.2.1, p.2.2)])) := (polyFun_fst.pair hsing).comp polyFun_rawPointStab
  have hconj : PolyFun (fun p : (List ℕ × RawGens) × (RawPerm × ℕ) =>
      rawConj (p.2.1, rawPointStab (p.1, [rawApply (p.2.1, p.2.2)]))) :=
    ((polyFun_snd.comp polyFun_fst).pair hst).comp polyFun_rawConj
  exact (((polyFun_fst.comp polyFun_fst).pair hconj).comp polyFun_tidyGens).of_eq (fun _ => rfl)

theorem polyFun_trCount : PolyFun trCount := by
  have hdom : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × (RawPerm × ℕ) => p.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hA : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × (RawPerm × ℕ) =>
      rawOrder (p.1.1.1, rawStab (p.1.1, p.2.2 + 1))) :=
    (hdom.pair (((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).add (polyFun_const 1))).comp polyFun_rawStab)).comp
      polyFun_rawOrder
  have hC : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × (RawPerm × ℕ) =>
      trChild ((p.1.1.1, p.1.2), p.2)) :=
    ((hdom.pair (polyFun_fst.comp polyFun_snd)).pair polyFun_snd).comp polyFun_trChild
  exact (hA.div ((hdom.pair hC).comp polyFun_rawOrder)).of_eq (fun _ => rfl)

theorem polyFun_trReps : PolyFun trReps := by
  have hq : PolyFun (fun z : (RawGens × ℕ) × RawPerm => trMinIn (z.1.1, rawApply (z.2, z.1.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_rawApply)).comp
      polyFun_trMinIn
  have hf := PolyFun.filterParam hq
  have hrow : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × ℕ => rawRow (p.1.1, p.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawRow
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair hrow).comp hf).of_eq
    (fun _ => rfl)

theorem polyFun_trSelStep : PolyFun trSelStep := by
  have hy : PolyFun (fun p : (((List ℕ × RawGens) × RawGens) × ℕ) ×
      ((ℕ × Option RawPerm) × RawPerm) => p.2.1) := polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun p : (((List ℕ × RawGens) × RawGens) × ℕ) ×
      ((ℕ × Option RawPerm) × RawPerm) => p.2.1.1) := hy.comp polyFun_fst
  have hτ : PolyFun (fun p : (((List ℕ × RawGens) × RawGens) × ℕ) ×
      ((ℕ × Option RawPerm) × RawPerm) => p.2.2) := polyFun_snd.comp polyFun_snd
  have hc : PolyFun (fun p : (((List ℕ × RawGens) × RawGens) × ℕ) ×
      ((ℕ × Option RawPerm) × RawPerm) => trCount (p.1.1, (p.2.2, p.1.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair (hτ.pair (polyFun_fst.comp polyFun_snd))).comp
      polyFun_trCount
  have hlt : PolyFun (fun p : (((List ℕ × RawGens) × RawGens) × ℕ) ×
      ((ℕ × Option RawPerm) × RawPerm) => !decide (trCount (p.1.1, (p.2.2, p.1.2)) ≤ p.2.1.1)) :=
    (hc.pair hj).comp polyFun_notLe
  have hinner := PolyFun.ite hlt (hj.pair (hτ.comp polyFun_some))
    ((hj.sub hc).pair (polyFun_const (none : Option RawPerm)))
  refine (PolyFun.ite ((hy.comp polyFun_snd).comp polyFun_trIsSome) hy hinner).of_eq (fun p => ?_)
  simp only [trSelStep, selStepG]
  by_cases h1 : p.2.1.2.isSome
  · simp [h1]
  · by_cases h2 : p.2.1.1 < trCount (p.1.1, (p.2.2, p.1.2))
    · simp [h1, h2]
    · simp [h1, h2]

/-- The accumulator of the selection stays small: the index only shrinks, and the entry kept is
one of the list. -/
theorem size_selG_le (cnt : RawPerm → ℕ) (x : ℕ × Option RawPerm) (r : List RawPerm) :
    Enc.size (r.foldl (selStepG cnt) x) ≤ 2 * Enc.size x + 2 * (Enc.size r + 2) + 4 := by
  rcases selG_mem cnt r x with h | ⟨h1, h2⟩
  · rw [h]; omega
  · have hp := size_pair_le' (r.foldl (selStepG cnt) x)
    have e1 : Enc.size (r.foldl (selStepG cnt) x).1 ≤ Enc.size x.1 := size_nat_le_of_le h1
    have e2 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
    have e3 : Enc.size (r.foldl (selStepG cnt) x).2 ≤ Enc.size r + 2 := by
      rcases h2 with h2 | ⟨a, ha, h2⟩
      · rw [h2, size_none]; omega
      · rw [h2, size_some_eq]
        have := size_mem_le ha
        omega
    omega

theorem polyFun_trSel : PolyFun trSel := by
  have hacc : ∀ (cc : ((List ℕ × RawGens) × RawGens) × ℕ) (x : ℕ × Option RawPerm)
      (r : List RawPerm) (j : ℕ),
      Enc.size (List.foldl (fun y a => trSelStep (cc, (y, a))) x (r.take j))
        ≤ (fun m => 2 * m + 2 * (m + 2) + 4)
          (Enc.size ((cc, (x, r)) : (((List ℕ × RawGens) × RawGens) × ℕ) ×
            ((ℕ × Option RawPerm) × List RawPerm))) := by
    intro cc x r j
    have h := size_selG_le (fun τ => trCount (cc.1, (τ, cc.2))) x (r.take j)
    have e : List.foldl (fun y a => trSelStep (cc, (y, a))) x (r.take j)
        = (r.take j).foldl (selStepG (fun τ => trCount (cc.1, (τ, cc.2)))) x := rfl
    rw [e]
    have hxr : Enc.size ((x, r) : (ℕ × Option RawPerm) × List RawPerm)
        ≤ Enc.size ((cc, (x, r)) : (((List ℕ × RawGens) × RawGens) × ℕ) ×
          ((ℕ × Option RawPerm) × List RawPerm)) :=
      size_snd_le' ((cc, (x, r)) : (((List ℕ × RawGens) × RawGens) × ℕ) ×
          ((ℕ × Option RawPerm) × List RawPerm))
    have hx : Enc.size x ≤ Enc.size ((cc, (x, r)) : (((List ℕ × RawGens) × RawGens) × ℕ) ×
        ((ℕ × Option RawPerm) × List RawPerm)) :=
      le_trans (size_fst_le' (x, r)) hxr
    have hr : Enc.size (r.take j) ≤ Enc.size ((cc, (x, r)) : (((List ℕ × RawGens) × RawGens) × ℕ) ×
        ((ℕ × Option RawPerm) × List RawPerm)) :=
      le_trans (size_take_le j r) (le_trans (size_snd_le' (x, r)) hxr)
    dsimp only
    omega
  have hfold := PolyFun.foldlParam polyFun_trSelStep
    (((polyBound_const 2).mul polyBound_id).add (((polyBound_const 2).mul
      (polyBound_id.add (polyBound_const 2))).add (polyBound_const 4))) hacc
  exact ((polyFun_fst.pair ((polyFun_snd.pair (polyFun_const (none : Option RawPerm))).pair
    (polyFun_fst.comp polyFun_trReps))).comp hfold).of_eq (fun _ => rfl)

theorem polyFun_trStep : PolyFun trStep := by
  have hdom : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hK : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) => p.2.1.1.1) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hj : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) => p.2.1.1.2) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
  have hacc : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) => p.2.1.2) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_snd
  have hi : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) => p.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hsel : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) =>
      trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)) :=
    (((polyFun_fst.pair hK).pair hi).pair hj).comp polyFun_trSel
  have hτ : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) =>
      (trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).2.getD (rawOne p.1.1)) :=
    ((hsel.comp polyFun_snd).pair (hdom.comp polyFun_rawOne)).comp polyFun_optionGetD
  have hchild : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) =>
      trChild ((p.1.1, p.2.1.1.1),
        ((trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).2.getD (rawOne p.1.1), p.2.2))) :=
    ((hdom.pair hK).pair (hτ.pair hi)).comp polyFun_trChild
  have hnew : PolyFun (fun p : (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × ℕ) =>
      normPerm (p.1.1, rawMul (rawInv ((trSel (((p.1, p.2.1.1.1), p.2.2), p.2.1.1.2)).2.getD
        (rawOne p.1.1)), p.2.1.2))) :=
    (hdom.pair (((hτ.comp polyFun_rawInv).pair hacc).comp polyFun_rawMul)).comp polyFun_normPerm
  exact ((hchild.pair (hsel.comp polyFun_fst)).pair hnew).of_eq (fun _ => rfl)

/-- The index left over only shrinks along the walk, and after one level the generators and the
product are well formed and small. -/
theorem trFold_struct (dom : List ℕ) (gs : RawGens) :
    ∀ (l : List ℕ) (x : (RawGens × ℕ) × RawPerm),
      List.foldl (fun y l => trStep ((dom, gs), (y, l))) x l = x ∨
      ((List.foldl (fun y l => trStep ((dom, gs), (y, l))) x l).1.2 ≤ x.1.2 ∧
        RawGens.WF dom.length (List.foldl (fun y l => trStep ((dom, gs), (y, l))) x l).1.1 ∧
        (List.foldl (fun y l => trStep ((dom, gs), (y, l))) x l).1.1.length
          ≤ dom.length * dom.length ∧
        RawPerm.WF dom.length (List.foldl (fun y l => trStep ((dom, gs), (y, l))) x l).2) := by
  intro l
  induction l with
  | nil => intro x; left; rfl
  | cons a l ih =>
      intro x
      right
      rw [List.foldl_cons]
      set y := trStep ((dom, gs), (x, a)) with hy
      have hy1 : y.1.2 ≤ x.1.2 := by
        show (trSel ((((dom, gs), x.1.1), a), x.1.2)).1 ≤ x.1.2
        rw [trSel_eq]
        rcases selG_mem (fun τ => trCount ((((dom, gs), x.1.1)), (τ, a)))
          (trReps (((dom, gs), x.1.1), a)) (x.1.2, none) with h | ⟨h1, -⟩
        · rw [h]
        · exact h1
      have hywf : RawGens.WF dom.length y.1.1 ∧ y.1.1.length ≤ dom.length * dom.length ∧
          RawPerm.WF dom.length y.2 :=
        ⟨wf_tidyGens rfl _, length_tidyGens rfl _, wf_normPerm rfl _⟩
      rcases ih y with h | ⟨h1, h2, h3, h4⟩
      · rw [h]; exact ⟨hy1, hywf⟩
      · exact ⟨le_trans h1 hy1, h2, h3, h4⟩

/-- The size bound of the walk's state. -/
def trAccBound (m : ℕ) : ℕ := m + 2 * (2 * gensBound m + 2 * m) + 2 * strBound m

theorem polyBound_trAccBound : PolyBound trAccBound :=
  (polyBound_id.add ((polyBound_const 2).mul (((polyBound_const 2).mul trPolyBound_gensBound).add
    ((polyBound_const 2).mul polyBound_id)))).add ((polyBound_const 2).mul trPolyBound_strBound)

theorem polyFun_trFold : PolyFun trFold := by
  have hacc : ∀ (cc : List ℕ × RawGens) (x : (RawGens × ℕ) × RawPerm) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => trStep (cc, (y, a))) x (r.take j))
        ≤ trAccBound (Enc.size ((cc, (x, r)) :
          (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ))) := by
    intro cc x r j
    obtain ⟨dom, gs⟩ := cc
    set N := Enc.size (((dom, gs), (x, r)) :
      (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ)) with hN
    have hx : Enc.size x ≤ N := le_trans (size_fst_le' (x, r))
      (size_snd_le' (((dom, gs), (x, r)) :
        (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ)))
    have hdl : dom.length ≤ N :=
      le_trans (length_le_size dom) (le_trans (size_fst_le' (dom, gs))
        (size_fst_le' (((dom, gs), (x, r)) :
          (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ))))
    have hgb := trMono_gensBound hdl
    have hsb := trMono_strBound hdl
    rcases trFold_struct dom gs (r.take j) x with h | ⟨h1, h2, h3, h4⟩
    · rw [h]; unfold trAccBound; omega
    · set res := List.foldl (fun y l => trStep ((dom, gs), (y, l))) x (r.take j) with hres
      have e1 : Enc.size res.1.1 ≤ gensBound dom.length :=
        size_gens_le' (n := dom.length) le_rfl h2 h3
      have e2 : Enc.size res.2 ≤ strBound dom.length := size_perm_le' (n := dom.length) le_rfl h4
      have e3 : Enc.size res.1.2 ≤ Enc.size x.1.2 := size_nat_le_of_le h1
      have e4 : Enc.size x.1.2 ≤ N :=
        le_trans (size_snd_le' x.1) (le_trans (size_fst_le' x) hx)
      have p1 := size_pair_le' res
      have p2 := size_pair_le' res.1
      unfold trAccBound
      omega
  have hfold := PolyFun.foldlParam polyFun_trStep polyBound_trAccBound hacc
  exact hfold.of_eq (fun _ => rfl)

/-- **The `j`-th representative is a `RAM.PolyFun`**, with `j` a machine natural: the time is
polynomial in the size of the generators and the bit length of `j`. -/
theorem polyFun_trRep : PolyFun trRep := by
  have hdom : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × ℕ => p.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hin : PolyFun (fun p : ((List ℕ × RawGens) × RawGens) × ℕ =>
      ((p.1.1, (((p.1.2, p.2), rawOne p.1.1.1), rawOne p.1.1.1)) :
        (List ℕ × RawGens) × (((RawGens × ℕ) × RawPerm) × List ℕ))) :=
    (polyFun_fst.comp polyFun_fst).pair
      ((((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair (hdom.comp polyFun_rawOne)).pair
        (hdom.comp polyFun_rawOne))
  exact ((hin.comp polyFun_trFold).comp polyFun_snd).of_eq (fun _ => rfl)

end Poly

end Algo
