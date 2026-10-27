/-
Auxiliary machinery for the formalization of §4 (and §5.3) of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The refinement processes of §4.1 and §4.3 are iterations of a refinement round, stopped
"when we reach a stable configuration".  The paper asserts termination ("The naive
refinement process clearly terminates in `k ≤ n-1` rounds", §4.1.1) without proof.  This
file supplies the termination argument in the form used by all of them: a decreasing
sequence of partitions of a finite set is constant from some index on, and one may take
that index uniformly, which is what makes the stable refinement canonical (the same number
of rounds is used on every input).
-/
import Workspace.Higher.PrelimExtra
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.EquivFin

namespace Babai

/-- The kernel of a coloring, as a set of pairs: the partition it defines. -/
def kernelSet {α : Type*} {C : Type*} (d : α → C) : Set (α × α) := {p | d p.1 = d p.2}

@[simp] theorem mem_kernelSet {α C : Type*} {d : α → C} {p : α × α} :
    p ∈ kernelSet d ↔ d p.1 = d p.2 := Iff.rfl

/-- A decreasing sequence of subsets of a finite type is constant from some index on, and
the index can be taken to be `|α|`: if `S (n+1) = S n` propagates, then
`S (M+1) = S M` for `M = |α|`.

This is the termination of the refinement processes of §4.1, §4.3 and §5.3. -/
theorem eq_of_antitone_sets {α : Type*} [Fintype α] (S : ℕ → Set α)
    (hmono : ∀ n, S (n + 1) ⊆ S n) (hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1)) :
    S (Fintype.card α + 1) = S (Fintype.card α) := by
  classical
  set M := Fintype.card α with hM
  -- first, a repeat occurs within the first `M+1` steps
  have hex : ∃ N ≤ M, S (N + 1) = S N := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ N ≤ M, (S (N + 1)).ncard < (S N).ncard := by
      intro N hN
      exact Set.ncard_lt_ncard ⟨hmono N, fun hsub =>
        hcon N hN (Set.Subset.antisymm (hmono N) hsub)⟩ (Set.toFinite _)
    have hdec : ∀ n ≤ M + 1, (S n).ncard + n ≤ (S 0).ncard := by
      intro n
      induction n with
      | zero => intro _; omega
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hlt m (by omega)
        omega
    have h1 := hdec (M + 1) le_rfl
    have h2 : (S 0).ncard ≤ M := by
      have := Set.ncard_le_ncard (Set.subset_univ (S 0)) (Set.toFinite _)
      simpa [hM] using this
    omega
  obtain ⟨N, hNM, hN⟩ := hex
  -- and once it occurs it persists
  have hall : ∀ m, N ≤ m → S (m + 1) = S m := by
    intro m hm
    induction m with
    | zero =>
      have hN0 : N = 0 := Nat.le_zero.1 hm
      subst hN0
      exact hN
    | succ p ih =>
      rcases Nat.lt_or_ge N (p + 1) with h | h
      · exact hstep p (ih (by omega))
      · have : N = p + 1 := by omega
        exact this ▸ hN
  exact hall M (by omega)


/-- The same, with the index taken at any `M ≥ |α|` rather than at `|α|` itself.  This is
what makes a refinement process canonical across **different** vertex sets: one and the
same number of rounds, fixed in advance, is run on every input, so the color type after the
process does not depend on the input.  (§9.4, step 3: `Babai.wlRounds`.) -/
theorem eq_of_antitone_sets_le {α : Type*} [Finite α] (S : ℕ → Set α)
    (hmono : ∀ n, S (n + 1) ⊆ S n) (hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1))
    {M : ℕ} (hM : Nat.card α ≤ M) : S (M + 1) = S M := by
  classical
  -- first, a repeat occurs within the first `M+1` steps
  have hex : ∃ N ≤ M, S (N + 1) = S N := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ N ≤ M, (S (N + 1)).ncard < (S N).ncard := by
      intro N hN
      exact Set.ncard_lt_ncard ⟨hmono N, fun hsub =>
        hcon N hN (Set.Subset.antisymm (hmono N) hsub)⟩ (Set.toFinite _)
    have hdec : ∀ n ≤ M + 1, (S n).ncard + n ≤ (S 0).ncard := by
      intro n
      induction n with
      | zero => intro _; omega
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hlt m (by omega)
        omega
    have h1 := hdec (M + 1) le_rfl
    have h2 : (S 0).ncard ≤ M := by
      have hle := Set.ncard_le_ncard (Set.subset_univ (S 0)) (Set.toFinite _)
      rw [Set.ncard_univ] at hle
      omega
    omega
  obtain ⟨N, hNM, hN⟩ := hex
  -- and once it occurs it persists
  have hall : ∀ m, N ≤ m → S (m + 1) = S m := by
    intro m hm
    induction m with
    | zero =>
      have hN0 : N = 0 := Nat.le_zero.1 hm
      subst hN0
      exact hN
    | succ p ih =>
      rcases Nat.lt_or_ge N (p + 1) with h | h
      · exact hstep p (ih (by omega))
      · have : N = p + 1 := by omega
        exact this ▸ hN
  exact hall M hNM

/-- A strict refinement has strictly more color classes: if the partition of `g` is strictly
finer than that of `f`, then `g` takes strictly more values than `f`. -/
theorem card_range_lt_of_kernelSet_ssubset {α β γ : Type*} [Finite α] (f : α → β)
    (g : α → γ) (hsub : kernelSet g ⊆ kernelSet f) (hne : kernelSet g ≠ kernelSet f) :
    Nat.card (Set.range f) < Nat.card (Set.range g) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  let φ : Set.range g → Set.range f := fun c => ⟨f c.2.choose, c.2.choose, rfl⟩
  have hφ : ∀ a, φ ⟨g a, a, rfl⟩ = ⟨f a, a, rfl⟩ := by
    intro a
    apply Subtype.ext
    have hc : g (Exists.choose (⟨a, rfl⟩ : ∃ y, g y = g a)) = g a :=
      Exists.choose_spec (⟨a, rfl⟩ : ∃ y, g y = g a)
    exact hsub (show (_, a) ∈ kernelSet g from hc)
  have hsurj : Function.Surjective φ := by
    rintro ⟨_, a, rfl⟩
    exact ⟨⟨g a, a, rfl⟩, hφ a⟩
  have hninj : ¬ Function.Injective φ := by
    intro hinj
    obtain ⟨p, hpf, hpg⟩ : ∃ p, p ∈ kernelSet f ∧ p ∉ kernelSet g := by
      by_contra hcon
      push_neg at hcon
      exact hne (Set.Subset.antisymm hsub hcon)
    have hpf' : f p.1 = f p.2 := hpf
    have heq : φ ⟨g p.1, p.1, rfl⟩ = φ ⟨g p.2, p.2, rfl⟩ := by
      rw [hφ, hφ]
      exact Subtype.ext hpf'
    exact hpg (congrArg Subtype.val (hinj heq))
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  haveI : Finite (Set.range g) := (Set.finite_range g).to_subtype
  haveI : Fintype (Set.range f) := Fintype.ofFinite _
  haveI : Fintype (Set.range g) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective φ hsurj hninj

/-- §4.1.1, *"The naive refinement process clearly terminates in `k ≤ n-1` rounds."*  For a
sequence of colorings `d n` of a set of `n` elements whose partitions get finer, and which
stays put once it has stopped changing, the partition does not change after round `n - 1`:
each round that changes the partition adds a color class, and there are at least `1` and at
most `n` classes. -/
theorem kernelSet_eq_of_card_sub_one_le {α : Type*} [Fintype α] {β : ℕ → Type*}
    (d : ∀ n, α → β n) (hmono : ∀ n, kernelSet (d (n + 1)) ⊆ kernelSet (d n))
    (hstep : ∀ n, kernelSet (d (n + 1)) = kernelSet (d n) →
      kernelSet (d (n + 2)) = kernelSet (d (n + 1)))
    {m : ℕ} (hm : Fintype.card α - 1 ≤ m) :
    kernelSet (d (m + 1)) = kernelSet (d m) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · ext p
    exact (hα.false p.1).elim
  set M := Fintype.card α - 1 with hM
  have hcard : 1 ≤ Fintype.card α := Fintype.card_pos
  -- a repeat occurs within the first `M` rounds
  have hex : ∃ N ≤ M, kernelSet (d (N + 1)) = kernelSet (d N) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ N ≤ M, Nat.card (Set.range (d N)) < Nat.card (Set.range (d (N + 1))) :=
      fun N hN => card_range_lt_of_kernelSet_ssubset _ _ (hmono N) (hcon N hN)
    have hinc : ∀ n ≤ M + 1, Nat.card (Set.range (d 0)) + n ≤ Nat.card (Set.range (d n)) := by
      intro n
      induction n with
      | zero => intro _; omega
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have h2 := hlt j (by omega)
        omega
    have h0 : 1 ≤ Nat.card (Set.range (d 0)) := by
      obtain ⟨a⟩ := hα
      haveI : Nonempty (Set.range (d 0)) := ⟨⟨d 0 a, a, rfl⟩⟩
      haveI : Finite (Set.range (d 0)) := (Set.finite_range (d 0)).to_subtype
      exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
    have hle : Nat.card (Set.range (d (M + 1))) ≤ Fintype.card α := by
      rw [← Nat.card_eq_fintype_card]
      exact Finite.card_range_le _
    have := hinc (M + 1) le_rfl
    omega
  obtain ⟨N, hNM, hN⟩ := hex
  -- and once it occurs it persists
  have hall : ∀ m, N ≤ m → kernelSet (d (m + 1)) = kernelSet (d m) := by
    intro m hm
    induction m with
    | zero =>
      have hN0 : N = 0 := Nat.le_zero.1 hm
      subst hN0
      exact hN
    | succ p ih =>
      rcases Nat.lt_or_ge N (p + 1) with h | h
      · exact hstep p (ih (by omega))
      · have : N = p + 1 := by omega
        exact this ▸ hN
  exact hall m (by omega)

end Babai
