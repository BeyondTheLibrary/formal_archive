/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (i) — the parity condition for a
Johnson scheme, and the odd automorphism that corrects an odd `σ̄`.
-/
import Workspace.Algo.AlignJohnsonIso
import Workspace.Coherent.Classes
import Workspace.Algo.TopStab

/-!
# §14.1, Procedure Align: when does `Aut(X)` of a Johnson scheme contain an odd permutation?

Line 1 of Procedure Align asks whether `X(x)` and `X(y)` are **`G^ϕ`-isomorphic**, and `G^ϕ`
is the symmetric group `S(Γ)` *or* the alternating group `A(Γ)` (`Babai.IsGiantRep`).  The
permutation `Algo.alignJPerm` (`Workspace/Algo/AlignJohnsonIso.lean`) answers the question
for `S(Γ)`.  For `A(Γ)` an odd answer has to be corrected by an odd automorphism of `X(x)`,
and this file says exactly when one exists and computes it.

This is the Johnson analogue of `Algo.exists_odd_colPartAut_iff` (`Algo/AlignParity.lean`).

## The condition

Write `X = decJohnson m r` for well-formed raw data `r` with parameters `(m*, t*)`, carried
by the class `W ⊆ Γ = [0, m)`.  Since `X` puts no structure at all on `Γ ∖ W` and the vertex
coloring marks `W`, the automorphism group of `X` is the direct product of the automorphism
group of the Johnson scheme on `W` — which is `S(Γ*)` in its action on `t*`-subsets,
Prop. 3.2.11, `Babai.aut_johnsonGraph` — and the full symmetric group on `Γ ∖ W`.  So:

> **`Aut(X)` contains an odd permutation of `Γ` exactly when `|W| + 2 ≤ m` or
> `C(m* − 2, t* − 1)` is odd** (`Algo.exists_odd_johnsonAut_iff`).

The second disjunct is `Algo.sign_tAction_swap`, a statement about `Babai.tAction` of
independent interest: the permutation of the `t`-subsets induced by a transposition `(a b)`
of `Γ*` is the product of the `C(m* − 2, t* − 1)` transpositions `(A ∪ {a}, A ∪ {b})`, over
the `(t* − 1)`-subsets `A` of `Γ* ∖ {a, b}`, so its sign is `(−1)^{C(m*−2, t*−1)}`.

## Main definitions

* `Algo.alignJSwap01`, `Algo.alignJSwapScheme` — the same Johnson scheme with the rows
  relabelled by the transposition `(0 1)` of `Γ*`.  The choice `(0 1)` avoids re-sorting the
  rows: the point `0` is the least of `Γ*`, so a sorted row stays sorted;
* `Algo.alignJAutPerm` — the automorphism of `X` induced by that transposition of `Γ*`:
  identity outside `W`, and on `W` the matching of the rows;
* `Algo.alignJOutSwap` — the transposition of the first two points of `Γ ∖ W`;
* `Algo.alignJHasOddAut`, `Algo.alignJOddAut` — **the decision and the odd automorphism**.

## Main results

* `Algo.sign_tAction_swap` — **the sign of the induced action of a transposition**;
* `Algo.exists_odd_tAction_iff` — `S(Γ*)` has an element whose induced action is odd exactly
  when `C(m* − 2, t* − 1)` is odd;
* `Algo.exists_odd_johnsonAut_iff` — **the exact parity condition**;
* `Algo.alignJOddAut_spec` — the computed odd automorphism is one;
* `Algo.polyFun_alignJHasOddAut`, `Algo.polyFun_alignJOddAut` — the running times.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm swap)

/-! ## A fixed-point-free involution is a product of transpositions

The permutation of the `t`-subsets induced by a transposition of `Γ*` is an involution, and
the general lemma below reads its sign off the number of two-cycles.  It is stated for a
list, because the induction that proves it peels one point off the list. -/

/-- An involution `σ` is the product of the transpositions `(x, σ x)`, taken over a list `l`
that contains exactly one point of each two-cycle of `σ`. -/
theorem alignJ_prod_swaps {α : Type*} [DecidableEq α] :
    ∀ (l : List α) (σ : Perm α), (∀ y, σ (σ y) = y) → l.Nodup →
      (∀ x ∈ l, σ x ≠ x) → (∀ x ∈ l, σ x ∉ l) → (∀ y, σ y ≠ y → y ∈ l ∨ σ y ∈ l) →
      (l.map (fun x => swap x (σ x))).prod = σ := by
  intro l
  induction l with
  | nil =>
    intro σ _ _ _ _ hall
    refine Equiv.ext (fun y => ?_)
    by_cases h : σ y = y
    · simpa using h.symm
    · rcases hall y h with hy | hy <;> simp at hy
  | cons x t ih =>
    intro σ hinv hnd hne hnotmem hall
    have hxt : x ∉ t := (List.nodup_cons.1 hnd).1
    have hndt : t.Nodup := (List.nodup_cons.1 hnd).2
    have hsxnot : σ x ∉ x :: t := hnotmem x (by simp)
    have hsxne : σ x ≠ x := hne x (by simp)
    set τ : Perm α := swap x (σ x) * σ with hτ
    have hτx : τ x = x := by
      simp [hτ, Equiv.swap_apply_right]
    have hτsx : τ (σ x) = σ x := by
      simp [hτ, hinv x, Equiv.swap_apply_left]
    have hσne : ∀ y, y ≠ x → y ≠ σ x → σ y ≠ x ∧ σ y ≠ σ x := by
      intro y h1 h2
      constructor
      · intro hh
        exact h2 (by rw [← hinv y, hh])
      · intro hh
        exact h1 (by rw [← hinv y, hh, hinv x])
    have hτeq : ∀ y, y ≠ x → y ≠ σ x → τ y = σ y := by
      intro y h1 h2
      obtain ⟨k1, k2⟩ := hσne y h1 h2
      simp [hτ, Equiv.swap_apply_of_ne_of_ne k1 k2]
    have hτinv : ∀ y, τ (τ y) = y := by
      intro y
      by_cases h1 : y = x
      · subst h1; rw [hτx, hτx]
      by_cases h2 : y = σ x
      · subst h2; rw [hτsx, hτsx]
      · obtain ⟨k1, k2⟩ := hσne y h1 h2
        rw [hτeq y h1 h2, hτeq (σ y) k1 k2, hinv y]
    have hmemne : ∀ z ∈ t, z ≠ x ∧ z ≠ σ x := by
      intro z hz
      refine ⟨fun hh => hxt (hh ▸ hz), fun hh => hsxnot (by rw [← hh]; exact List.mem_cons_of_mem _ hz)⟩
    have hIH : (t.map (fun z => swap z (τ z))).prod = τ := by
      refine ih τ hτinv hndt ?_ ?_ ?_
      · intro z hz
        obtain ⟨h1, h2⟩ := hmemne z hz
        rw [hτeq z h1 h2]
        exact hne z (List.mem_cons_of_mem _ hz)
      · intro z hz
        obtain ⟨h1, h2⟩ := hmemne z hz
        rw [hτeq z h1 h2]
        exact fun hh => hnotmem z (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ hh)
      · intro y hy
        have h1 : y ≠ x := fun hh => hy (by rw [hh, hτx])
        have h2 : y ≠ σ x := fun hh => hy (by rw [hh, hτsx])
        rw [hτeq y h1 h2] at hy ⊢
        rcases hall y hy with hh | hh
        · rcases List.mem_cons.1 hh with hh' | hh'
          · exact absurd hh' h1
          · exact Or.inl hh'
        · rcases List.mem_cons.1 hh with hh' | hh'
          · exact absurd (show y = σ x by rw [← hinv y, hh']) h2
          · exact Or.inr hh'
    have hmapeq : t.map (fun z => swap z (σ z)) = t.map (fun z => swap z (τ z)) := by
      refine List.map_congr_left (fun z hz => ?_)
      obtain ⟨h1, h2⟩ := hmemne z hz
      rw [hτeq z h1 h2]
    have : ((x :: t).map (fun z => swap z (σ z))).prod
        = swap x (σ x) * (t.map (fun z => swap z (σ z))).prod := by
      simp
    rw [this, hmapeq, hIH, hτ, ← mul_assoc, Equiv.swap_mul_self, one_mul]

/-! ## The sign of the induced action of a transposition -/

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- A transposition fixes a finite set exactly when it contains both of its points or
neither. -/
theorem alignJ_image_swap_eq_iff {a b : Γ} (S : Finset Γ) :
    S.image (swap a b) = S ↔ (a ∈ S ↔ b ∈ S) := by
  constructor
  · intro h
    constructor
    · intro ha
      have : b ∈ S.image (swap a b) := by
        refine Finset.mem_image.2 ⟨a, ha, ?_⟩
        rw [Equiv.swap_apply_left]
      rwa [h] at this
    · intro hb
      have : a ∈ S.image (swap a b) := by
        refine Finset.mem_image.2 ⟨b, hb, ?_⟩
        rw [Equiv.swap_apply_right]
      rwa [h] at this
  · intro h
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases h1 : y = a
      · subst h1; rw [Equiv.swap_apply_left]; exact h.1 hy
      by_cases h2 : y = b
      · subst h2; rw [Equiv.swap_apply_right]; exact h.2 hy
      · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · intro hx
      refine ⟨swap a b x, ?_, by rw [Equiv.swap_apply_self]⟩
      by_cases h1 : x = a
      · subst h1; rw [Equiv.swap_apply_left]; exact h.1 hx
      by_cases h2 : x = b
      · subst h2; rw [Equiv.swap_apply_right]; exact h.2 hx
      · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- The `t`-subsets containing `a` and not `b`. -/
private def alignJHalf (t : ℕ) (a b : Γ) : Finset (Babai.binom Γ t) :=
  Finset.univ.filter (fun S : Babai.binom Γ t => a ∈ (S : Finset Γ) ∧ b ∉ (S : Finset Γ))

private theorem mem_alignJHalf {t : ℕ} {a b : Γ} {S : Babai.binom Γ t} :
    S ∈ alignJHalf t a b ↔ a ∈ (S : Finset Γ) ∧ b ∉ (S : Finset Γ) := by
  simp [alignJHalf]

/-- **The count**: there are `C(|Γ| − 2, t − 1)` of the `t`-subsets that contain `a` and not
`b`, one for each `(t−1)`-subset of `Γ ∖ {a, b}`. -/
private theorem card_alignJHalf {t : ℕ} (ht : 1 ≤ t) {a b : Γ} (hab : a ≠ b) :
    (alignJHalf t a b).card = (Fintype.card Γ - 2).choose (t - 1) := by
  classical
  have hcard : ((Finset.univ : Finset Γ) \ {a, b}).card = Fintype.card Γ - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_pair hab]
  rw [← hcard, ← Finset.card_powersetCard]
  refine Finset.card_bij' (fun S _ => (S : Finset Γ).erase a)
    (fun A hA => (⟨insert a A, ?_⟩ : Babai.binom Γ t)) ?_ ?_ ?_ ?_
  · have h1 := Finset.mem_powersetCard.1 hA
    have ha : a ∉ A := fun hh => by
      have := h1.1 hh
      rw [Finset.mem_sdiff] at this
      exact this.2 (by simp)
    rw [Finset.card_insert_of_notMem ha, h1.2]
    omega
  · intro S hS
    obtain ⟨haS, hbS⟩ := mem_alignJHalf.1 hS
    refine Finset.mem_powersetCard.2 ⟨fun x hx => ?_, ?_⟩
    · have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      have hxS : x ∈ (S : Finset Γ) := Finset.mem_of_mem_erase hx
      refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
      intro hh
      rcases Finset.mem_insert.1 hh with hh' | hh'
      · exact hxa hh'
      · exact hbS (by rw [← Finset.mem_singleton.1 hh']; exact hxS)
    · rw [Finset.card_erase_of_mem haS, S.2]
  · intro A hA
    have h1 := Finset.mem_powersetCard.1 hA
    have hbA : b ∉ A := fun hh => by
      have := h1.1 hh
      rw [Finset.mem_sdiff] at this
      exact this.2 (by simp)
    refine mem_alignJHalf.2 ⟨Finset.mem_insert_self _ _, ?_⟩
    intro hh
    rcases Finset.mem_insert.1 hh with hh' | hh'
    · exact hab hh'.symm
    · exact hbA hh'
  · intro S hS
    exact Subtype.ext (Finset.insert_erase (mem_alignJHalf.1 hS).1)
  · intro A hA
    have h1 := Finset.mem_powersetCard.1 hA
    have ha : a ∉ A := fun hh => by
      have := h1.1 hh
      rw [Finset.mem_sdiff] at this
      exact this.2 (by simp)
    exact Finset.erase_insert ha

/-- §14.1, line 2 (i).  **The sign of the induced action of a transposition on `t`-sets.**

The permutation of `(Γ choose t)` induced by the transposition `(a b)` of `Γ` is an
involution whose two-cycles are the pairs `{A ∪ {a}, A ∪ {b}}` with `A ⊆ Γ ∖ {a, b}` and
`|A| = t − 1`; every other `t`-subset is fixed.  There are `C(|Γ| − 2, t − 1)` such pairs.

This is a statement about `Babai.tAction` (§2.2.1) alone. -/
theorem sign_tAction_swap {t : ℕ} (ht : 1 ≤ t) {a b : Γ} (hab : a ≠ b) :
    Equiv.Perm.sign (Babai.tAction t (swap a b))
      = (-1 : ℤˣ) ^ ((Fintype.card Γ - 2).choose (t - 1)) := by
  classical
  set σ : Perm (Babai.binom Γ t) := Babai.tAction t (swap a b) with hσdef
  have hsq : σ * σ = 1 := by
    rw [hσdef, ← map_mul, Equiv.swap_mul_self, map_one]
  have hinv : ∀ y, σ (σ y) = y := by
    intro y
    show σ (σ y) = y
    rw [← Equiv.Perm.mul_apply, hsq, Equiv.Perm.one_apply]
  have hcoe : ∀ S : Babai.binom Γ t,
      ((σ S : Babai.binom Γ t) : Finset Γ) = (S : Finset Γ).image (swap a b) := by
    intro S
    rw [hσdef]
    exact Babai.tAction_apply_coe t (swap a b) S
  have hfix : ∀ S : Babai.binom Γ t,
      σ S = S ↔ (a ∈ (S : Finset Γ) ↔ b ∈ (S : Finset Γ)) := by
    intro S
    rw [Subtype.ext_iff, hcoe S]
    exact alignJ_image_swap_eq_iff _
  have hmemA : ∀ S : Babai.binom Γ t, a ∈ (S : Finset Γ) →
      b ∈ ((σ S : Babai.binom Γ t) : Finset Γ) := by
    intro S hS
    rw [hcoe S]
    exact Finset.mem_image.2 ⟨a, hS, Equiv.swap_apply_left _ _⟩
  have hmemB : ∀ S : Babai.binom Γ t, b ∈ (S : Finset Γ) →
      a ∈ ((σ S : Babai.binom Γ t) : Finset Γ) := by
    intro S hS
    rw [hcoe S]
    exact Finset.mem_image.2 ⟨b, hS, Equiv.swap_apply_right _ _⟩
  have hnotmemB : ∀ S : Babai.binom Γ t, a ∉ (S : Finset Γ) →
      b ∉ ((σ S : Babai.binom Γ t) : Finset Γ) := by
    intro S hS hh
    rw [hcoe S, Finset.mem_image] at hh
    obtain ⟨y, hy, hyb⟩ := hh
    have : y = a := by
      by_cases h1 : y = a
      · exact h1
      by_cases h2 : y = b
      · subst h2
        rw [Equiv.swap_apply_right] at hyb
        exact absurd hyb hab
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hyb
        exact absurd hyb h2
    exact hS (this ▸ hy)
  set l : List (Babai.binom Γ t) := (alignJHalf t a b).toList with hl
  have hlmem : ∀ S, S ∈ l ↔ (a ∈ (S : Finset Γ) ∧ b ∉ (S : Finset Γ)) := by
    intro S
    rw [hl, Finset.mem_toList]
    exact mem_alignJHalf
  have hprod : (l.map (fun x => swap x (σ x))).prod = σ := by
    refine alignJ_prod_swaps l σ hinv (Finset.nodup_toList _) ?_ ?_ ?_
    · intro S hS
      obtain ⟨h1, h2⟩ := (hlmem S).1 hS
      rw [Ne, hfix S]
      exact fun hh => h2 (hh.1 h1)
    · intro S hS
      obtain ⟨h1, h2⟩ := (hlmem S).1 hS
      intro hh
      exact ((hlmem _).1 hh).2 (hmemA S h1)
    · intro T hT
      rw [Ne, hfix T] at hT
      by_cases h1 : a ∈ (T : Finset Γ)
      · exact Or.inl ((hlmem T).2 ⟨h1, fun hb => hT ⟨fun _ => hb, fun _ => h1⟩⟩)
      · have hb : b ∈ (T : Finset Γ) := by
          by_contra hb
          exact hT ⟨fun hh => absurd hh h1, fun hh => absurd hh hb⟩
        exact Or.inr ((hlmem _).2 ⟨hmemB T hb, hnotmemB T h1⟩)
  have hswaps : ∀ g ∈ l.map (fun x => swap x (σ x)), Equiv.Perm.IsSwap g := by
    intro g hg
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := (hlmem S).1 hS
    refine ⟨S, σ S, ?_, rfl⟩
    intro hh
    exact h2 (by rw [hh]; exact hmemA S h1)
  have := Equiv.Perm.sign_prod_list_swap hswaps
  rw [hprod, List.length_map, hl, Finset.length_toList, card_alignJHalf ht hab] at this
  exact this

/-- §14.1, line 2 (i).  **Some permutation of `Γ*` induces an odd permutation of the
`t`-subsets exactly when `C(|Γ*| − 2, t − 1)` is odd.**  Transpositions generate `S(Γ*)` and
all have the same induced sign, so the homomorphism `π ↦ sign(π^{(t)})` is either trivial or
the sign. -/
theorem exists_odd_tAction_iff {t : ℕ} (ht : 1 ≤ t) (h2 : 2 ≤ Fintype.card Γ) :
    (∃ π : Perm Γ, Equiv.Perm.sign (Babai.tAction t π) = -1) ↔
      Odd ((Fintype.card Γ - 2).choose (t - 1)) := by
  classical
  constructor
  · intro ⟨π, hπ⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have hall : ∀ ρ : Perm Γ, Equiv.Perm.sign (Babai.tAction t ρ) = 1 := by
      intro ρ
      induction ρ using Equiv.Perm.swap_induction_on with
      | one => rw [map_one, map_one]
      | swap_mul f x y hxy ih =>
        rw [map_mul, map_mul, ih, mul_one, sign_tAction_swap ht hxy]
        exact hodd.neg_one_pow
    rw [hall π] at hπ
    exact absurd hπ (by decide)
  · intro hodd
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := Γ) (by omega)
    exact ⟨swap a b, by rw [sign_tAction_swap ht hab]; exact hodd.neg_one_pow⟩

/-! ## The transposition `(0 1)` of `Γ*`, on raw rows

The odd automorphism that corrects an odd `σ̄` is, in the second case, the image of *one*
transposition of `Γ*`.  Which transposition is free, and the choice `(0 1)` costs nothing:
a strictly increasing row stays strictly increasing after the relabelling, because `0` is
the least point of `Γ*`, so no row has to be sorted again. -/

/-- The transposition `(0 1)` of `Γ*`, on one point. -/
def alignJSwapNat (a : ℕ) : ℕ := if a = 0 then 1 else if a = 1 then 0 else a

@[simp] theorem alignJSwapNat_involutive (a : ℕ) : alignJSwapNat (alignJSwapNat a) = a := by
  unfold alignJSwapNat
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h1]
    · simp [h0, h1]

theorem alignJSwapNat_lt {a b : ℕ} (hab : a < b)
    (h : (a ≠ 1 ∧ b ≠ 1) ∨ (a ≠ 0 ∧ b ≠ 0)) :
    alignJSwapNat a < alignJSwapNat b := by
  unfold alignJSwapNat
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs <;> omega

theorem mem_map_alignJSwapNat {l : List ℕ} {a : ℕ} :
    a ∈ l.map alignJSwapNat ↔ alignJSwapNat a ∈ l := by
  constructor
  · rintro hmem
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hmem
    rwa [alignJSwapNat_involutive]
  · intro h
    exact List.mem_map.2 ⟨alignJSwapNat a, h, alignJSwapNat_involutive a⟩

/-- The transposition `(0 1)` of `Γ*`, on a row.  A row that contains both `0` and `1`, or
neither, describes a set that the transposition fixes, and is left alone. -/
def alignJSwap01 (row : List ℕ) : List ℕ :=
  if decide (0 ∈ row) = decide (1 ∈ row) then row else row.map alignJSwapNat

@[simp] theorem length_alignJSwap01 (row : List ℕ) :
    (alignJSwap01 row).length = row.length := by
  unfold alignJSwap01; split <;> simp

theorem alignJSwap01_involutive (row : List ℕ) :
    alignJSwap01 (alignJSwap01 row) = row := by
  by_cases hc : decide (0 ∈ row) = decide (1 ∈ row)
  · have hfix : alignJSwap01 row = row := by rw [alignJSwap01, if_pos hc]
    rw [hfix, hfix]
  · have hmap : alignJSwap01 row = row.map alignJSwapNat := by rw [alignJSwap01, if_neg hc]
    have h0 : (0 ∈ row.map alignJSwapNat) ↔ (1 ∈ row) := by
      rw [mem_map_alignJSwapNat]; simp [alignJSwapNat]
    have h1 : (1 ∈ row.map alignJSwapNat) ↔ (0 ∈ row) := by
      rw [mem_map_alignJSwapNat]; simp [alignJSwapNat]
    have hc' : ¬ (decide (0 ∈ row.map alignJSwapNat) = decide (1 ∈ row.map alignJSwapNat)) := by
      rw [decide_eq_decide, h0, h1]
      rw [decide_eq_decide] at hc
      exact fun hh => hc hh.symm
    have hid : (alignJSwapNat ∘ alignJSwapNat) = id :=
      funext (fun a => alignJSwapNat_involutive a)
    rw [hmap, alignJSwap01, if_neg hc', List.map_map, hid, List.map_id]

theorem alignJSwap01_injective : Function.Injective alignJSwap01 :=
  Function.LeftInverse.injective alignJSwap01_involutive

section Fin01

variable {ms : ℕ}

/-- The transposition `(0 1)` of `Γ* = [0, m*)`, as a permutation of `Fin m*`. -/
def alignJFin01 (hms : 2 ≤ ms) : Perm (Fin ms) :=
  swap ⟨0, by omega⟩ ⟨1, by omega⟩

theorem val_alignJFin01 (hms : 2 ≤ ms) (j : Fin ms) :
    ((alignJFin01 hms j : Fin ms) : ℕ) = alignJSwapNat (j : ℕ) := by
  rw [alignJFin01]
  by_cases h0 : j = (⟨0, by omega⟩ : Fin ms)
  · subst h0; rw [Equiv.swap_apply_left]; simp [alignJSwapNat]
  by_cases h1 : j = (⟨1, by omega⟩ : Fin ms)
  · subst h1; rw [Equiv.swap_apply_right]; simp [alignJSwapNat]
  · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    have k0 : (j : ℕ) ≠ 0 := fun hh => h0 (Fin.ext hh)
    have k1 : (j : ℕ) ≠ 1 := fun hh => h1 (Fin.ext hh)
    simp [alignJSwapNat, k0, k1]

theorem sign_alignJFin01 (hms : 2 ≤ ms) :
    Equiv.Perm.sign (alignJFin01 hms) = -1 := by
  rw [alignJFin01]
  exact Equiv.Perm.sign_swap (by simp [Fin.ext_iff])

/-- **The relabelled row describes the relabelled set.** -/
theorem rawJSet_alignJSwap01 (hms : 2 ≤ ms) {row : List ℕ} (hlt : ∀ a ∈ row, a < ms) :
    rawJSet ms (alignJSwap01 row) = (rawJSet ms row).image (alignJFin01 hms) := by
  classical
  unfold alignJSwap01
  split_ifs with hc
  · rw [alignJFin01, eq_comm, alignJ_image_swap_eq_iff]
    rw [decide_eq_decide] at hc
    exact ⟨fun hh => mem_rawJSet.2 (hc.1 (mem_rawJSet.1 hh)),
      fun hh => mem_rawJSet.2 (hc.2 (mem_rawJSet.1 hh))⟩
  · ext i
    simp only [mem_rawJSet, Finset.mem_image]
    constructor
    · intro hmem
      obtain ⟨a, ha, hai⟩ := List.mem_map.1 hmem
      exact ⟨⟨a, hlt a ha⟩, ha, Fin.ext (by rw [val_alignJFin01 hms]; exact hai)⟩
    · rintro ⟨j, hj, rfl⟩
      rw [val_alignJFin01 hms]
      exact List.mem_map.2 ⟨(j : ℕ), hj, rfl⟩

end Fin01

/-- The same Johnson scheme with its rows relabelled by the transposition `(0 1)` of `Γ*`. -/
def alignJSwapScheme (r : RawJohnson) : RawJohnson := (r.1, r.2.1, r.2.2.map alignJSwap01)

theorem alignJSwapScheme_wf {m ms ts : ℕ} {r : RawJohnson} (h : RawJohnson.WF m ms ts r) :
    RawJohnson.WF m ms ts (alignJSwapScheme r) := by
  have hrows : ∀ row' ∈ (alignJSwapScheme r).2.2, ∃ row ∈ r.2.2, alignJSwap01 row = row' := by
    intro row' hrow'
    obtain ⟨row, hrow, hq⟩ := List.mem_map.1 hrow'
    exact ⟨row, hrow, hq⟩
  refine ⟨h.two_le, h.params, h.hdr, h.wLt, h.wNodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (r.2.2.map alignJSwap01).length = r.1.length
    rw [List.length_map]; exact h.rowsLen
  · intro row' hrow'
    obtain ⟨row, hrow, rfl⟩ := hrows row' hrow'
    have hs := h.rowSorted row hrow
    unfold alignJSwap01
    split_ifs with hc
    · exact hs
    · rw [decide_eq_decide] at hc
      rw [List.sortedLT_iff_pairwise] at hs ⊢
      rw [List.pairwise_map]
      refine hs.imp_of_mem ?_
      intro a b ha hb hab
      by_cases h0 : (0 : ℕ) ∈ row
      · have h1 : (1 : ℕ) ∉ row := fun hh => hc ⟨fun _ => hh, fun _ => h0⟩
        exact alignJSwapNat_lt hab (Or.inl ⟨fun hh => h1 (hh ▸ ha), fun hh => h1 (hh ▸ hb)⟩)
      · have h1 : (1 : ℕ) ∈ row := by
          by_contra hh
          exact hc ⟨fun kk => absurd kk h0, fun kk => absurd kk hh⟩
        exact alignJSwapNat_lt hab (Or.inr ⟨fun hh => h0 (hh ▸ ha), fun hh => h0 (hh ▸ hb)⟩)
  · intro row' hrow'
    obtain ⟨row, hrow, rfl⟩ := hrows row' hrow'
    rw [length_alignJSwap01]; exact h.rowLen row hrow
  · intro row' hrow' a ha
    obtain ⟨row, hrow, rfl⟩ := hrows row' hrow'
    have hms : 2 ≤ ms := by have := h.two_le; have := h.params; omega
    unfold alignJSwap01 at ha
    split_ifs at ha with hc
    · exact h.rowLt row hrow a ha
    · obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 ha
      have := h.rowLt row hrow c hcmem
      unfold alignJSwapNat
      split_ifs <;> omega
  · show (r.2.2.map alignJSwap01).Nodup
    exact h.rowsNodup.map alignJSwap01_injective
  · show (r.2.2.map alignJSwap01).length = _
    rw [List.length_map]; exact h.card

@[simp] theorem alignJSwapScheme_fst (r : RawJohnson) : (alignJSwapScheme r).1 = r.1 := rfl

/-! ## Automorphisms of a decoded Johnson structure

`Algo.decJohnson` marks the carrier `W` with the vertex color `1` and puts the Johnson color
on `W × W` and `0` everywhere else.  So an automorphism is exactly a permutation that carries
`W` onto itself and preserves the Johnson color there; outside `W` it is unconstrained.  That
is the "direct product" statement the DESIGN note calls for, in the only form this file
needs. -/

private theorem alignJ_ite_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (1 : ℕ) else 0) = (if q then (1 : ℕ) else 0)) : p ↔ q := by
  split_ifs at h <;> simp_all

section Aut

variable {m ms ts : ℕ} {r : RawJohnson}

/-- §14.1, line 7 (B).  **What an automorphism of a decoded Johnson structure is**: a
permutation carrying `W` onto itself that preserves the Johnson color on `W`. -/
theorem mem_structAut_decJohnson_iff {f : Perm (Fin m)} :
    f ∈ Babai.structAut (decJohnson m r) ↔
      (∀ u : Fin m, ((f u : Fin m) : ℕ) ∈ r.1 ↔ (u : ℕ) ∈ r.1) ∧
        (∀ u v : Fin m, (u : ℕ) ∈ r.1 → (v : ℕ) ∈ r.1 →
          rawJDiff (r, (((f u : Fin m) : ℕ), ((f v : Fin m) : ℕ)))
            = rawJDiff (r, ((u : ℕ), (v : ℕ)))) := by
  rw [Babai.mem_structAut]
  constructor
  · intro hf
    have hinvself : ∀ u : Fin m, f⁻¹ (f u) = u := fun u => Equiv.symm_apply_apply f u
    have hvcol : ∀ u : Fin m, ((f u : Fin m) : ℕ) ∈ r.1 ↔ (u : ℕ) ∈ r.1 := by
      intro u
      have hx : (decJohnson m r).vcol (f⁻¹ (f u)) = (decJohnson m r).vcol (f u) :=
        congrArg (fun X : Babai.ColStruct (Fin m) ℕ => X.vcol (f u)) hf
      rw [hinvself u] at hx
      exact alignJ_ite_eq hx.symm
    refine ⟨hvcol, fun u v hu hv => ?_⟩
    have hx : (decJohnson m r).ecol (f⁻¹ (f u)) (f⁻¹ (f v))
        = (decJohnson m r).ecol (f u) (f v) :=
      congrArg (fun X : Babai.ColStruct (Fin m) ℕ => X.ecol (f u) (f v)) hf
    rw [hinvself u, hinvself v] at hx
    rw [← decJohnson_ecol_mem m r ((hvcol u).2 hu) ((hvcol v).2 hv),
      ← decJohnson_ecol_mem m r hu hv]
    exact hx.symm
  · rintro ⟨hmem, hecol⟩
    refine colStruct_smul_eq (fun u => ?_) (fun u v => ?_)
    · show (if ((f u : Fin m) : ℕ) ∈ r.1 then 1 else 0)
        = (if (u : ℕ) ∈ r.1 then 1 else 0)
      by_cases hc : (u : ℕ) ∈ r.1
      · rw [if_pos ((hmem u).2 hc), if_pos hc]
      · rw [if_neg (fun hh => hc ((hmem u).1 hh)), if_neg hc]
    · by_cases hu : (u : ℕ) ∈ r.1
      · by_cases hv : (v : ℕ) ∈ r.1
        · rw [decJohnson_ecol_mem m r ((hmem u).2 hu) ((hmem v).2 hv),
            decJohnson_ecol_mem m r hu hv]
          exact hecol u v hu hv
        · show (if _ ∈ r.1 then (if _ ∈ r.1 then _ else 0) else 0)
            = (if _ ∈ r.1 then (if _ ∈ r.1 then _ else 0) else 0)
          rw [if_pos ((hmem u).2 hu), if_pos hu,
            if_neg (fun hh => hv ((hmem v).1 hh)), if_neg hv]
      · show (if _ ∈ r.1 then _ else 0) = (if _ ∈ r.1 then _ else 0)
        rw [if_neg (fun hh => hu ((hmem u).1 hh)), if_neg hu]

/-- The identification of `W` with `(Γ* choose t*)`, as an `Equiv` of subtypes. -/
noncomputable def alignJEquiv (h : RawJohnson.WF m ms ts r) :
    {u : Fin m // (u : ℕ) ∈ r.1} ≃ Babai.binom (Fin ms) ts :=
  Equiv.ofBijective h.toBinom h.toBinom_bijective

theorem alignJEquiv_coe (h : RawJohnson.WF m ms ts r) (u : {u : Fin m // (u : ℕ) ∈ r.1}) :
    ((alignJEquiv h u : Babai.binom (Fin ms) ts) : Finset (Fin ms))
      = rawJSet ms (rawJRow (r, ((u : Fin m) : ℕ))) := rfl

/-- §14.1, line 7 (B).  **The restriction of an automorphism to `W` is induced by a
permutation of `Γ*`.**  This is Prop. 3.2.11 (`Babai.aut_johnsonGraph`) carried along the
identification of `W` with `(Γ* choose t*)`. -/
theorem alignJ_sign_restrict (h : RawJohnson.WF m ms ts r) {f : Perm (Fin m)}
    (hf : f ∈ Babai.structAut (decJohnson m r)) :
    ∃ π : Perm (Fin ms),
      Equiv.Perm.sign (Equiv.Perm.subtypePerm (p := fun u : Fin m => (u : ℕ) ∈ r.1) f
          (fun u => (mem_structAut_decJohnson_iff.1 hf).1 u))
        = Equiv.Perm.sign (Babai.tAction ts π) := by
  classical
  obtain ⟨hmem, hecol⟩ := mem_structAut_decJohnson_iff.1 hf
  set fW : Perm {u : Fin m // (u : ℕ) ∈ r.1} :=
    Equiv.Perm.subtypePerm (p := fun u : Fin m => (u : ℕ) ∈ r.1) f (fun u => hmem u)
    with hfWdef
  set e := alignJEquiv h with hedef
  set σ : Perm (Babai.binom (Fin ms) ts) := e.permCongr fW with hσdef
  have hcoe : ∀ u : {u : Fin m // (u : ℕ) ∈ r.1},
      ((σ (e u) : Babai.binom (Fin ms) ts) : Finset (Fin ms))
        = rawJSet ms (rawJRow (r, ((f (u : Fin m) : Fin m) : ℕ))) := by
    intro u
    have hstep : σ (e u) = e (fW u) := by
      rw [hσdef, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rw [hstep, alignJEquiv_coe]
    rfl
  have hpres : ∀ S T : Babai.binom (Fin ms) ts,
      (((σ S : Babai.binom (Fin ms) ts) : Finset (Fin ms)) \
        ((σ T : Babai.binom (Fin ms) ts) : Finset (Fin ms))).card
        = (((S : Babai.binom (Fin ms) ts) : Finset (Fin ms)) \
          ((T : Babai.binom (Fin ms) ts) : Finset (Fin ms))).card := by
    intro S T
    obtain ⟨u, rfl⟩ : ∃ u, e u = S := ⟨e.symm S, e.apply_symm_apply S⟩
    obtain ⟨v, rfl⟩ : ∃ v, e v = T := ⟨e.symm T, e.apply_symm_apply T⟩
    rw [hcoe u, hcoe v, alignJEquiv_coe, alignJEquiv_coe,
      ← rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem ((hmem _).2 u.2)))
        (h.rowLt _ (h.rawJRow_mem ((hmem _).2 u.2))),
      ← rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem u.2))
        (h.rowLt _ (h.rawJRow_mem u.2))]
    exact hecol (u : Fin m) (v : Fin m) u.2 v.2
  have haut : σ ∈ (Babai.johnsonGraph (Fin ms) ts).Aut := by
    refine Babai.Digraph.mem_aut.2 (fun S T => ?_)
    show ((((σ S : Babai.binom (Fin ms) ts) : Finset (Fin ms)) \
      ((σ T : Babai.binom (Fin ms) ts) : Finset (Fin ms))).card = 1) ↔ _
    rw [hpres S T]
    rfl
  have hparams : Babai.IsJohnsonGraphParams (Fin ms) ts :=
    ⟨h.two_le, by rw [Fintype.card_fin]; exact h.params⟩
  rw [Babai.aut_johnsonGraph ts hparams] at haut
  obtain ⟨π, -, hπ⟩ := Subgroup.mem_map.1 haut
  exact ⟨π, by rw [hπ, hσdef, Equiv.Perm.sign_permCongr]⟩

/-- The number of points of `Γ` outside `W`. -/
theorem alignJ_card_compl (h : RawJohnson.WF m ms ts r) :
    ((Finset.univ : Finset (Fin m)) \ rawJSet m r.1).card = m - r.1.length := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    card_rawJSet h.wNodup h.wLt]

end Aut

/-! ## The exact parity condition -/

section Parity

variable {m ms ts : ℕ} {r : RawJohnson}

/-- The transposition of two points outside `W` is an automorphism of `X`: the structure
says nothing at all about those points. -/
theorem alignJ_swap_out_mem_structAut {a b : Fin m} (ha : (a : ℕ) ∉ r.1)
    (hb : (b : ℕ) ∉ r.1) : swap a b ∈ Babai.structAut (decJohnson m r) := by
  have hfix : ∀ u : Fin m, (u : ℕ) ∈ r.1 → swap a b u = u := fun u hu =>
    Equiv.swap_apply_of_ne_of_ne (fun hh => ha (hh ▸ hu)) (fun hh => hb (hh ▸ hu))
  refine mem_structAut_decJohnson_iff.2 ⟨fun u => ?_, fun u v hu hv => ?_⟩
  · by_cases h1 : u = a
    · subst h1; rw [Equiv.swap_apply_left]
      exact ⟨fun hh => absurd hh hb, fun hh => absurd hh ha⟩
    by_cases h2 : u = b
    · subst h2; rw [Equiv.swap_apply_right]
      exact ⟨fun hh => absurd hh ha, fun hh => absurd hh hb⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rw [hfix u hu, hfix v hv]

/-- §14.1, line 7 (B).  **The automorphism of `X` that a permutation of `Γ*` induces**: it
fixes every point outside `W`, and on `W` it relabels the rows. -/
theorem alignJ_aut_of_perm (h : RawJohnson.WF m ms ts r) (π : Perm (Fin ms)) :
    ∃ f : Perm (Fin m), f ∈ Babai.structAut (decJohnson m r) ∧
      Equiv.Perm.sign f = Equiv.Perm.sign (Babai.tAction ts π) ∧
      (∀ u : Fin m, (u : ℕ) ∉ r.1 → f u = u) ∧
      (∀ u : Fin m, (u : ℕ) ∈ r.1 →
        rawJSet ms (rawJRow (r, ((f u : Fin m) : ℕ)))
          = (rawJSet ms (rawJRow (r, (u : ℕ)))).image π) := by
  classical
  set e := alignJEquiv h with hedef
  set σ : Perm (Babai.binom (Fin ms) ts) := Babai.tAction ts π with hσdef
  set fW : Perm {u : Fin m // (u : ℕ) ∈ r.1} := e.symm.permCongr σ with hfWdef
  have hfWapply : ∀ u : {u : Fin m // (u : ℕ) ∈ r.1}, e (fW u) = σ (e u) := by
    intro u
    rw [hfWdef, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hrow : ∀ u : {u : Fin m // (u : ℕ) ∈ r.1},
      rawJSet ms (rawJRow (r, (((fW u).1 : Fin m) : ℕ)))
        = (rawJSet ms (rawJRow (r, ((u : Fin m) : ℕ)))).image π := by
    intro u
    rw [← alignJEquiv_coe h (fW u), hfWapply u, hσdef, Babai.tAction_apply_coe,
      alignJEquiv_coe h u]
  refine ⟨Equiv.Perm.ofSubtype fW, ?_, ?_, ?_, ?_⟩
  · refine mem_structAut_decJohnson_iff.2 ⟨fun u => ?_, fun u v hu hv => ?_⟩
    · by_cases hu : (u : ℕ) ∈ r.1
      · rw [Equiv.Perm.ofSubtype_apply_of_mem fW hu]
        exact ⟨fun _ => hu, fun _ => (fW ⟨u, hu⟩).2⟩
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem fW hu]
    · have hfu : Equiv.Perm.ofSubtype fW u = (fW ⟨u, hu⟩).1 :=
        Equiv.Perm.ofSubtype_apply_of_mem fW hu
      have hfv : Equiv.Perm.ofSubtype fW v = (fW ⟨v, hv⟩).1 :=
        Equiv.Perm.ofSubtype_apply_of_mem fW hv
      have hu' : ((Equiv.Perm.ofSubtype fW u : Fin m) : ℕ) ∈ r.1 := by
        rw [hfu]; exact (fW ⟨u, hu⟩).2
      have hv' : ((Equiv.Perm.ofSubtype fW v : Fin m) : ℕ) ∈ r.1 := by
        rw [hfv]; exact (fW ⟨v, hv⟩).2
      rw [rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem hu'))
          (h.rowLt _ (h.rawJRow_mem hu')),
        rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem hu))
          (h.rowLt _ (h.rawJRow_mem hu)),
        hfu, hfv, hrow ⟨u, hu⟩, hrow ⟨v, hv⟩, ← Finset.image_sdiff _ _ π.injective,
        Finset.card_image_of_injective _ π.injective]
  · rw [Equiv.Perm.sign_ofSubtype, hfWdef, Equiv.Perm.sign_permCongr]
  · intro u hu
    exact Equiv.Perm.ofSubtype_apply_of_not_mem fW hu
  · intro u hu
    rw [Equiv.Perm.ofSubtype_apply_of_mem fW hu]
    exact hrow ⟨u, hu⟩

/-- §14.1, line 2 (i).  **The exact parity condition for a Johnson scheme.**

`Aut(X)` contains an odd permutation of `Γ` exactly when at least two points of `Γ` lie
outside the class `W` that carries the scheme, or `C(m* − 2, t* − 1)` is odd.  This is the
Johnson analogue of `Algo.exists_odd_colPartAut_iff`. -/
theorem exists_odd_johnsonAut_iff (h : RawJohnson.WF m ms ts r) :
    (∃ f : Perm (Fin m), f ∈ Babai.structAut (decJohnson m r) ∧
        Equiv.Perm.sign f = -1) ↔
      (r.1.length + 2 ≤ m ∨ Odd ((ms - 2).choose (ts - 1))) := by
  classical
  have hts1 : 1 ≤ ts := by have := h.two_le; omega
  have h2ms : 2 ≤ Fintype.card (Fin ms) := by
    rw [Fintype.card_fin]; have := h.two_le; have := h.params; omega
  constructor
  · rintro ⟨f, hf, hsign⟩
    by_cases hW : r.1.length + 2 ≤ m
    · exact Or.inl hW
    refine Or.inr ?_
    have hle : ((Finset.univ : Finset (Fin m)) \ rawJSet m r.1).card ≤ 1 := by
      rw [alignJ_card_compl h]; omega
    have hout : ∀ u v : Fin m, (u : ℕ) ∉ r.1 → (v : ℕ) ∉ r.1 → u = v := by
      intro u v hu hv
      refine Finset.card_le_one.1 hle u ?_ v ?_ <;>
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hh => by
          first | exact hu (mem_rawJSet.1 hh) | exact hv (mem_rawJSet.1 hh)⟩
    obtain ⟨hmem, -⟩ := mem_structAut_decJohnson_iff.1 hf
    have hfix : ∀ u : Fin m, f u ≠ u → (u : ℕ) ∈ r.1 := by
      intro u hu
      by_contra hn
      exact hu (hout (f u) u (fun hh => hn ((hmem u).1 hh)) hn)
    have hsg : Equiv.Perm.sign (Equiv.Perm.subtypePerm
        (p := fun u : Fin m => (u : ℕ) ∈ r.1) f (fun u => hmem u)) = -1 := by
      rw [Equiv.Perm.sign_subtypePerm f _ hfix]; exact hsign
    obtain ⟨π, hπ⟩ := alignJ_sign_restrict h hf
    have hodd := (exists_odd_tAction_iff (Γ := Fin ms) hts1 h2ms).1 ⟨π, by rw [← hπ]; exact hsg⟩
    rwa [Fintype.card_fin] at hodd
  · rintro (hW | hodd)
    · have hlt : 1 < ((Finset.univ : Finset (Fin m)) \ rawJSet m r.1).card := by
        rw [alignJ_card_compl h]; omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hlt
      have ha' : (a : ℕ) ∉ r.1 := fun hh =>
        (Finset.mem_sdiff.1 ha).2 (mem_rawJSet.2 hh)
      have hb' : (b : ℕ) ∉ r.1 := fun hh =>
        (Finset.mem_sdiff.1 hb).2 (mem_rawJSet.2 hh)
      exact ⟨swap a b, alignJ_swap_out_mem_structAut ha' hb', Equiv.Perm.sign_swap hab⟩
    · obtain ⟨π, hπ⟩ := (exists_odd_tAction_iff (Γ := Fin ms) hts1 h2ms).2
        (by rwa [Fintype.card_fin])
      obtain ⟨f, hf, hsign, -, -⟩ := alignJ_aut_of_perm h π
      exact ⟨f, hf, by rw [hsign, hπ]⟩

end Parity

/-! ## The odd automorphism as a routine -/

/-- §14.1, line 2 (i).  The image of one point of `Γ` under the automorphism induced by the
transposition `(0 1)` of `Γ*`: a point of `W` goes to the point of `W` whose row is the
relabelled row, and every point outside `W` stays put. -/
def alignJAutMatch (p : RawJohnson × ℕ) : ℕ :=
  if p.2 ∈ p.1.1 then
    (((p.1.2.2.map alignJSwap01).zip p.1.1).lookup (rawJRow (p.1, p.2))).getD 0
  else p.2

/-- §14.1, line 2 (i).  **The automorphism of `X` induced by the transposition `(0 1)` of
`Γ*`**, as a raw permutation. -/
def alignJAutPerm (p : List ℕ × RawJohnson) : RawPerm :=
  (List.range p.1.length).map (fun u => alignJAutMatch (p.2, u))

/-- §14.1, line 2 (i).  The transposition of the first two points of `Γ ∖ W`. -/
def alignJOutSwap (p : List ℕ × RawJohnson) : RawPerm :=
  rawTopSwap (p.1, ((alignJOutList (p.1, p.2.1)).getD 0 0,
    (alignJOutList (p.1, p.2.1)).getD 1 0))

/-- §14.1, line 2 (i).  **The decision whether `Aut(X)` contains an odd permutation**, for a
Johnson scheme: two points outside `W`, or `C(m* − 2, t* − 1)` odd. -/
def alignJHasOddAut (p : List ℕ × RawJohnson) : Bool :=
  decide (p.2.1.length + 2 ≤ p.1.length) ||
    decide (Nat.choose (rawJDeg p.2 - 2) (p.2.2.1 - 1) % 2 = 1)

/-- §14.1, line 2 (i).  **An odd automorphism of `X`**, when there is one. -/
def alignJOddAut (p : List ℕ × RawJohnson) : RawPerm :=
  if p.2.1.length + 2 ≤ p.1.length then alignJOutSwap p else alignJAutPerm p

section AutPerm

variable {m ms ts : ℕ} {dom : List ℕ} {r : RawJohnson}

theorem alignJAutMatch_eq_alignJMatch {u : ℕ} (hu : u ∈ r.1) :
    alignJAutMatch (r, u) = alignJMatch ((dom, (r, alignJSwapScheme r)), u) := by
  show (if u ∈ r.1 then _ else _) = (if u ∈ r.1 then _ else _)
  rw [if_pos hu, if_pos hu]
  rfl

theorem alignJAutMatch_of_not_mem {u : ℕ} (hu : u ∉ r.1) : alignJAutMatch (r, u) = u := by
  show (if u ∈ r.1 then _ else _) = _
  rw [if_neg hu]

theorem rawJRow_alignJSwapScheme (h : RawJohnson.WF m ms ts r) {w : ℕ} (hw : w ∈ r.1) :
    rawJRow (alignJSwapScheme r, w) = alignJSwap01 (rawJRow (r, w)) := by
  obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
  have h' := alignJSwapScheme_wf h
  have e1 : rawJRow (alignJSwapScheme r, w)
      = (r.2.2.map alignJSwap01)[i]'(by rw [List.length_map, h.rowsLen]; exact hi) := by
    rw [← hiw]
    exact h'.rawJRow_getElem (show i < (alignJSwapScheme r).1.length from hi)
  have e2 : rawJRow (r, w) = r.2.2[i]'(by rw [h.rowsLen]; exact hi) := by
    rw [← hiw]
    exact h.rawJRow_getElem hi
  rw [e1, e2]
  simp

/-- **What the routine does on `W`**: it stays in `W`, and the row of the image is the
relabelled row. -/
theorem alignJAutMatch_spec (h : RawJohnson.WF m ms ts r) {u : ℕ} (hu : u ∈ r.1) :
    alignJAutMatch (r, u) ∈ r.1 ∧
      rawJRow (r, alignJAutMatch (r, u)) = alignJSwap01 (rawJRow (r, u)) := by
  have h' := alignJSwapScheme_wf h
  have hmm := alignJMatch_mem (dom := ([] : List ℕ)) h h' hu
  rw [← alignJAutMatch_eq_alignJMatch (dom := ([] : List ℕ)) hu] at hmm
  have hmem : alignJAutMatch (r, u) ∈ r.1 := hmm.1
  refine ⟨hmem, ?_⟩
  have hk := hmm.2
  rw [rawJRow_alignJSwapScheme h hmem] at hk
  rw [← hk, alignJSwap01_involutive]

theorem alignJAutMatch_lt (h : RawJohnson.WF m ms ts r) {u : ℕ} (hu : u < m) :
    alignJAutMatch (r, u) < m := by
  by_cases hc : u ∈ r.1
  · exact h.wLt _ (alignJAutMatch_spec h hc).1
  · rw [alignJAutMatch_of_not_mem hc]; exact hu

theorem alignJAutMatch_inj (h : RawJohnson.WF m ms ts r) {u v : ℕ}
    (huv : alignJAutMatch (r, u) = alignJAutMatch (r, v)) : u = v := by
  by_cases hu : u ∈ r.1 <;> by_cases hv : v ∈ r.1
  · obtain ⟨-, hru⟩ := alignJAutMatch_spec h hu
    obtain ⟨-, hrv⟩ := alignJAutMatch_spec h hv
    rw [huv, hrv] at hru
    exact (rawJRow_inj_of_wf h hv hu (alignJSwap01_injective hru)).symm
  · exact absurd (alignJAutMatch_spec h hu).1
      (by rw [huv, alignJAutMatch_of_not_mem hv]; exact hv)
  · exact absurd (alignJAutMatch_spec h hv).1
      (by rw [← huv, alignJAutMatch_of_not_mem hu]; exact hu)
  · rw [alignJAutMatch_of_not_mem hu, alignJAutMatch_of_not_mem hv] at huv
    exact huv

theorem alignJAutPerm_wf (hd : dom.length = m) (h : RawJohnson.WF m ms ts r) :
    RawPerm.WF m (alignJAutPerm (dom, r)) := by
  refine ⟨by rw [alignJAutPerm, List.length_map, List.length_range, hd], ?_, ?_⟩
  · intro a ha
    rw [alignJAutPerm, List.mem_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    exact alignJAutMatch_lt h (hd ▸ List.mem_range.1 hu)
  · rw [alignJAutPerm]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro u _ v _ huv
    exact alignJAutMatch_inj h huv

theorem labAt_alignJAutPerm (hd : dom.length = m) {u : ℕ} (hu : u < m) :
    labAt (alignJAutPerm (dom, r)) u = alignJAutMatch (r, u) := by
  have hlt : u < ((List.range dom.length).map (fun w => alignJAutMatch (r, w))).length := by
    rw [List.length_map, List.length_range, hd]; exact hu
  show ((List.range dom.length).map (fun w => alignJAutMatch (r, w))).getD u 0 = _
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]

/-- §14.1, line 2 (i).  **The computed permutation is an automorphism of `X`, and its sign is
`(−1)^{C(m*−2, t*−1)}`** — it is the automorphism induced by the transposition `(0 1)` of
`Γ*`. -/
theorem alignJAutPerm_spec (hd : dom.length = m) (h : RawJohnson.WF m ms ts r) :
    RawPerm.WF m (alignJAutPerm (dom, r)) ∧
      decPerm m (alignJAutPerm (dom, r)) ∈ Babai.structAut (decJohnson m r) ∧
      Equiv.Perm.sign (decPerm m (alignJAutPerm (dom, r)))
        = (-1 : ℤˣ) ^ ((ms - 2).choose (ts - 1)) := by
  classical
  have hms : 2 ≤ ms := by have := h.two_le; have := h.params; omega
  obtain ⟨f, hfaut, hfsign, hfout, hfrow⟩ := alignJ_aut_of_perm h (alignJFin01 hms)
  have hwf := alignJAutPerm_wf hd h
  have himg : ∀ u : Fin m, ((decPerm m (alignJAutPerm (dom, r)) u : Fin m) : ℕ)
      = alignJAutMatch (r, (u : ℕ)) := fun u => by
    rw [← labAt_eq_decPerm hwf u.isLt, labAt_alignJAutPerm hd u.isLt]
  have heq : decPerm m (alignJAutPerm (dom, r)) = f := by
    refine Equiv.ext (fun u => ?_)
    by_cases hu : (u : ℕ) ∈ r.1
    · have h1 : ((decPerm m (alignJAutPerm (dom, r)) u : Fin m) : ℕ) ∈ r.1 := by
        rw [himg u]; exact (alignJAutMatch_spec h hu).1
      have h2 : ((f u : Fin m) : ℕ) ∈ r.1 :=
        ((mem_structAut_decJohnson_iff.1 hfaut).1 u).2 hu
      have hset : rawJSet ms
          (rawJRow (r, ((decPerm m (alignJAutPerm (dom, r)) u : Fin m) : ℕ)))
          = rawJSet ms (rawJRow (r, ((f u : Fin m) : ℕ))) := by
        rw [himg u, (alignJAutMatch_spec h hu).2, hfrow u hu,
          rawJSet_alignJSwap01 hms (h.rowLt _ (h.rawJRow_mem hu))]
      have hb := h.toBinom_bijective.1
        (a₁ := (⟨_, h1⟩ : RawJohnson.carrier m r)) (a₂ := (⟨_, h2⟩ : RawJohnson.carrier m r))
        (Subtype.ext hset)
      exact congrArg Subtype.val hb
    · rw [hfout u hu]
      exact Fin.ext (by rw [himg u, alignJAutMatch_of_not_mem hu])
  refine ⟨hwf, by rw [heq]; exact hfaut, ?_⟩
  rw [heq, hfsign, alignJFin01,
    sign_tAction_swap (Γ := Fin ms) (by have := h.two_le; omega)
      (show (⟨0, by omega⟩ : Fin ms) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff]),
    Fintype.card_fin]

/-- §14.1, line 2 (i).  **The transposition of two points outside `W` is an odd
automorphism.** -/
theorem alignJOutSwap_spec (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (hW : r.1.length + 2 ≤ m) :
    RawPerm.WF m (alignJOutSwap (dom, r)) ∧
      decPerm m (alignJOutSwap (dom, r)) ∈ Babai.structAut (decJohnson m r) ∧
      Equiv.Perm.sign (decPerm m (alignJOutSwap (dom, r))) = -1 := by
  have hlen : (alignJOutList (dom, r.1)).length = m - r.1.length :=
    length_alignJOutList hd h.wNodup h.wLt
  have h0 : 0 < (alignJOutList (dom, r.1)).length := by omega
  have h1 : 1 < (alignJOutList (dom, r.1)).length := by omega
  have hga : (alignJOutList (dom, r.1)).getD 0 0 = (alignJOutList (dom, r.1))[0]'h0 :=
    List.getD_eq_getElem _ _ h0
  have hgb : (alignJOutList (dom, r.1)).getD 1 0 = (alignJOutList (dom, r.1))[1]'h1 :=
    List.getD_eq_getElem _ _ h1
  have hamem : (alignJOutList (dom, r.1))[0]'h0 ∈ alignJOutList (dom, r.1) :=
    List.getElem_mem h0
  have hbmem : (alignJOutList (dom, r.1))[1]'h1 ∈ alignJOutList (dom, r.1) :=
    List.getElem_mem h1
  have halt : (alignJOutList (dom, r.1))[0]'h0 < m := hd ▸ alignJOutList_lt hamem
  have hblt : (alignJOutList (dom, r.1))[1]'h1 < m := hd ▸ alignJOutList_lt hbmem
  set a : Fin m := ⟨(alignJOutList (dom, r.1))[0]'h0, halt⟩ with hadef
  set b : Fin m := ⟨(alignJOutList (dom, r.1))[1]'h1, hblt⟩ with hbdef
  have hab : a ≠ b := by
    intro hh
    have := (List.Nodup.getElem_inj_iff (alignJOutList_nodup dom r.1)).1
      (congrArg Fin.val hh)
    exact absurd this (by decide)
  have hraw : alignJOutSwap (dom, r) = encPerm m (swap a b) := by
    show rawTopSwap (dom, ((alignJOutList (dom, r.1)).getD 0 0,
      (alignJOutList (dom, r.1)).getD 1 0)) = _
    rw [hga, hgb]
    exact rawTopSwap_spec hd a b
  rw [hraw, decPerm_encPerm]
  exact ⟨wf_encPerm m (swap a b),
    alignJ_swap_out_mem_structAut (alignJOutList_notMem hamem) (alignJOutList_notMem hbmem),
    Equiv.Perm.sign_swap hab⟩

/-- §14.1, line 2 (i).  **The decision is correct.** -/
theorem alignJHasOddAut_iff (hd : dom.length = m) (h : RawJohnson.WF m ms ts r) :
    alignJHasOddAut (dom, r) = true ↔
      ∃ f : Perm (Fin m), f ∈ Babai.structAut (decJohnson m r) ∧
        Equiv.Perm.sign f = -1 := by
  rw [exists_odd_johnsonAut_iff h, alignJHasOddAut, hd, h.rawJDeg_eq, h.hdr]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [← Nat.odd_iff]

/-- §14.1, line 2 (i).  **The computed odd automorphism is one.** -/
theorem alignJOddAut_spec (hd : dom.length = m) (h : RawJohnson.WF m ms ts r)
    (hodd : alignJHasOddAut (dom, r) = true) :
    RawPerm.WF m (alignJOddAut (dom, r)) ∧
      decPerm m (alignJOddAut (dom, r)) ∈ Babai.structAut (decJohnson m r) ∧
      Equiv.Perm.sign (decPerm m (alignJOddAut (dom, r))) = -1 := by
  by_cases hW : r.1.length + 2 ≤ dom.length
  · have he : alignJOddAut (dom, r) = alignJOutSwap (dom, r) := by
      show (if r.1.length + 2 ≤ dom.length then _ else _) = _
      rw [if_pos hW]
    rw [he]
    exact alignJOutSwap_spec hd h (hd ▸ hW)
  · have he : alignJOddAut (dom, r) = alignJAutPerm (dom, r) := by
      show (if r.1.length + 2 ≤ dom.length then _ else _) = _
      rw [if_neg hW]
    have hchoose : Odd ((ms - 2).choose (ts - 1)) := by
      rw [alignJHasOddAut, hd, h.rawJDeg_eq, h.hdr] at hodd
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hodd
      rcases hodd with hh | hh
      · exact absurd (hd ▸ hh) hW
      · exact Nat.odd_iff.2 hh
    obtain ⟨hwf, haut, hsign⟩ := alignJAutPerm_spec hd h
    rw [he]
    exact ⟨hwf, haut, by rw [hsign]; exact hchoose.neg_one_pow⟩

end AutPerm

/-! ## The running times -/

/-- The disjunction of two `RAM.PolyFun` tests. -/
theorem polyFun_rawJOr {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a || g a) :=
  (PolyFun.ite hf (polyFun_const true) hg).of_eq (fun a => by cases f a <;> simp)

theorem polyFun_alignJSwapNat : PolyFun alignJSwapNat := by
  refine (PolyFun.ite ((polyFun_id.pair (polyFun_const 0)).comp polyFun_natEq)
    (polyFun_const 1)
    (PolyFun.ite ((polyFun_id.pair (polyFun_const 1)).comp polyFun_natEq)
      (polyFun_const 0) polyFun_id)).of_eq (fun a => ?_)
  unfold alignJSwapNat
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1 <;> simp [h0, h1]

theorem polyFun_alignJSwap01 : PolyFun alignJSwap01 := by
  have hm0 : PolyFun (fun l : List ℕ => decide ((0 : ℕ) ∈ l)) :=
    ((polyFun_const 0).pair polyFun_id).comp polyFun_natListMem
  have hm1 : PolyFun (fun l : List ℕ => decide ((1 : ℕ) ∈ l)) :=
    ((polyFun_const 1).pair polyFun_id).comp polyFun_natListMem
  have htest : PolyFun (fun l : List ℕ =>
      decide (decide ((0 : ℕ) ∈ l) = decide ((1 : ℕ) ∈ l))) := by
    refine (PolyFun.ite hm0 hm1 (polyFun_rawJNot hm1)).of_eq (fun l => ?_)
    by_cases h0 : (0 : ℕ) ∈ l <;> by_cases h1 : (1 : ℕ) ∈ l <;> simp [h0, h1]
  have hmap : PolyFun (fun l : List ℕ => l.map alignJSwapNat) :=
    ((polyFun_id.pair polyFun_id).comp
      (PolyFun.mapParam (polyFun_snd.comp polyFun_alignJSwapNat))).of_eq (fun _ => rfl)
  refine (PolyFun.ite htest polyFun_id hmap).of_eq (fun l => ?_)
  by_cases hc : decide ((0 : ℕ) ∈ l) = decide ((1 : ℕ) ∈ l) <;> simp [alignJSwap01, hc]

theorem polyFun_alignJMapSwap01 : PolyFun (fun l : List (List ℕ) => l.map alignJSwap01) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.mapParam (polyFun_snd.comp polyFun_alignJSwap01))).of_eq (fun _ => rfl)

theorem polyFun_alignJAutMatch : PolyFun alignJAutMatch := by
  have htest : PolyFun (fun p : RawJohnson × ℕ => decide (p.2 ∈ p.1.1)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_natListMem
  have hrow : PolyFun (fun p : RawJohnson × ℕ => rawJRow (p.1, p.2)) :=
    polyFun_rawJRow.of_eq (fun _ => rfl)
  have hrows : PolyFun (fun p : RawJohnson × ℕ => p.1.2.2.map alignJSwap01) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_alignJMapSwap01
  have hyes : PolyFun (fun p : RawJohnson × ℕ =>
      (((p.1.2.2.map alignJSwap01).zip p.1.1).lookup (rawJRow (p.1, p.2))).getD 0) :=
    (((((hrows.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_zip).pair hrow).comp
      (polyFun_listLookup (β := ℕ) polyFun_listNatEq)).pair (polyFun_const 0)).comp
      polyFun_optionGetD
  refine (PolyFun.ite htest hyes polyFun_snd).of_eq (fun p => ?_)
  by_cases hc : p.2 ∈ p.1.1 <;> simp [alignJAutMatch, hc]

theorem polyFun_alignJAutPerm : PolyFun alignJAutPerm :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_alignJAutMatch)).of_eq (fun _ => rfl)

theorem polyFun_alignJOutSwap : PolyFun alignJOutSwap := by
  have hout : PolyFun (fun p : List ℕ × RawJohnson => alignJOutList (p.1, p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_alignJOutList
  have hg : ∀ k : ℕ, PolyFun (fun p : List ℕ × RawJohnson =>
      (alignJOutList (p.1, p.2.1)).getD k 0) := fun k =>
    ((hout.pair (polyFun_const k)).pair (polyFun_const 0)).comp polyFun_getD
  exact ((polyFun_fst.pair ((hg 0).pair (hg 1))).comp polyFun_rawTopSwap).of_eq (fun _ => rfl)

/-- `m*` is at most the size of the input (`Algo.rawJDeg_le_size`, at the input type of the
routines of this file).  This is the bound that makes `C(m* − 2, t* − 1)` a `RAM.PolyFun`. -/
theorem alignJ_rawJDeg_le_size (p : List ℕ × RawJohnson) : rawJDeg p.2 ≤ Enc.size p := by
  obtain ⟨dom, W, ts, rows⟩ := p
  have h1 : (dedupG (([] : List ℕ), rows.flatten)).length ≤ rows.flatten.length :=
    length_dedupG_le _
  have h2 : rows.flatten.length ≤ Enc.size rows := length_flatten_le_size _
  have h3 : Enc.size rows ≤ Enc.size ((ts, rows) : ℕ × List (List ℕ)) :=
    Combine.size_snd_le _ _
  have h4 : Enc.size ((ts, rows) : ℕ × List (List ℕ))
      ≤ Enc.size ((W, (ts, rows)) : RawJohnson) := Combine.size_snd_le _ _
  have h5 : Enc.size ((W, (ts, rows)) : RawJohnson)
      ≤ Enc.size ((dom, (W, (ts, rows))) : List ℕ × RawJohnson) := Combine.size_snd_le _ _
  show (dedupG (([] : List ℕ), rows.flatten)).length
      ≤ Enc.size ((dom, (W, (ts, rows))) : List ℕ × RawJohnson)
  exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 h5)))

theorem polyFun_alignJOutTest :
    PolyFun (fun p : List ℕ × RawJohnson => decide (p.2.1.length + 2 ≤ p.1.length)) :=
  ((((((polyFun_snd.comp polyFun_fst).comp polyFun_length).pair (polyFun_const 2)).comp
    polyFun_add).pair (polyFun_fst.comp polyFun_length))).comp polyFun_le

/-- §14.1, line 2 (i).  **The decision runs in polynomial time.** -/
theorem polyFun_alignJHasOddAut : PolyFun alignJHasOddAut := by
  have hms : PolyFun (fun p : List ℕ × RawJohnson => rawJDeg p.2) :=
    polyFun_snd.comp polyFun_rawJDeg
  have hms2 : PolyFun (fun p : List ℕ × RawJohnson => rawJDeg p.2 - 2) :=
    (hms.pair (polyFun_const 2)).comp polyFun_sub
  have hts : PolyFun (fun p : List ℕ × RawJohnson => p.2.2.1 - 1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair (polyFun_const 1)).comp polyFun_sub
  have hchoose : PolyFun (fun p : List ℕ × RawJohnson =>
      Nat.choose (rawJDeg p.2 - 2) (p.2.2.1 - 1)) :=
    PolyFun.choose hms2 hts
      (fun p => le_trans (Nat.sub_le _ _) (alignJ_rawJDeg_le_size p)) polyBound_id
  have h2 : PolyFun (fun p : List ℕ × RawJohnson =>
      decide (Nat.choose (rawJDeg p.2 - 2) (p.2.2.1 - 1) % 2 = 1)) :=
    (((hchoose.pair (polyFun_const 2)).comp polyFun_mod).pair (polyFun_const 1)).comp
      polyFun_natEq
  exact polyFun_rawJOr polyFun_alignJOutTest h2

/-- §14.1, line 2 (i).  **The odd automorphism is computed in polynomial time.** -/
theorem polyFun_alignJOddAut : PolyFun alignJOddAut := by
  refine (PolyFun.ite polyFun_alignJOutTest polyFun_alignJOutSwap
    polyFun_alignJAutPerm).of_eq (fun p => ?_)
  by_cases hc : p.2.1.length + 2 ≤ p.1.length <;> simp [alignJOddAut, hc]

end Algo
