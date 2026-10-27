/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: explicit permutations of `Fin n`.
-/
import Workspace.AltQuotients.DM52.SylowTools

/-!
# Explicit permutations of `Fin n`

Explicit permutations, given by their value tables, used as models in the small-degree cases
of [DiM, Thm. 5.2A,B]; and the transport of a normalizing element from a model cycle to any
permutation of the same cycle type.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

/-- The permutation of `Fin n` with value table `f` and inverse table `g`. -/
def ofVec {n : ℕ} (f g : Fin n → Fin n) (h : ∀ i, g (f i) = i ∧ f (g i) = i) :
    Perm (Fin n) :=
  ⟨f, g, fun i => (h i).1, fun i => (h i).2⟩

@[simp] theorem ofVec_apply {n : ℕ} (f g : Fin n → Fin n) (h) (i : Fin n) :
    ofVec f g h i = f i := rfl

/-- In a finite group, an element conjugating `c` to a power of `c` normalizes `⟨c⟩`. -/
theorem mem_normalizer_zpowers_of_conj_eq_zpow {H : Type*} [Group H] [Finite H] {c m : H}
    {k : ℤ} (h : m * c * m⁻¹ = c ^ k) :
    m ∈ normalizer ((zpowers c : Subgroup H) : Set H) := by
  -- conjugation by `m` maps `⟨c⟩` into itself, hence onto itself
  have hmaps : ∀ z ∈ zpowers c, m * z * m⁻¹ ∈ zpowers c := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, h, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers c _
  let f : zpowers c → zpowers c := fun z => ⟨m * z * m⁻¹, hmaps z z.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa [f] using this
  have hsurj := Finite.injective_iff_surjective.mp hf
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => hmaps z hz, fun hz => ?_⟩
  obtain ⟨w, hw⟩ := hsurj ⟨_, hz⟩
  have := congrArg Subtype.val hw
  simp only [f] at this
  have hzw : z = w := by
    have := congrArg (fun t => m⁻¹ * t * m) this
    simpa [mul_assoc] using this.symm
  rw [hzw]; exact w.2

/-- An odd permutation normalizing `⟨c₀⟩` for a model `c₀` gives one for every permutation of
the same cycle type (all are conjugate to `c₀`). -/
theorem exists_odd_normalizer_of_model {n : ℕ} {c₀ m₀ : Perm (Fin n)} {k : ℤ}
    (hm : m₀ * c₀ * m₀⁻¹ = c₀ ^ k) (hs : sign m₀ = -1) {x : Perm (Fin n)}
    (hx : x.cycleType = c₀.cycleType) :
    ∃ y ∈ normalizer ((zpowers x : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))),
      sign y = -1 := by
  obtain ⟨τ, hτ'⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hx.symm)
  refine ⟨τ * m₀ * τ⁻¹, mem_normalizer_zpowers_of_conj_eq_zpow (k := k) ?_, ?_⟩
  · rw [← hτ', conj_zpow, ← hm]; group
  · simp [hs]

/-- An element of prime order `p` of `Sym(Fin n)` with `n < 2p` is a `p`-cycle, so its cycle
type is `{p}`. -/
theorem cycleType_eq_of_orderOf_prime {n p : ℕ} {x : Perm (Fin n)} (hp : p.Prime)
    (hx : orderOf x = p) (hn : n < 2 * p) : x.cycleType = {p} := by
  have hc : x.IsCycle := isCycle_of_prime_order' (hx ▸ hp) (by simpa [hx] using hn)
  rw [hc.cycleType, ← hc.orderOf, hx]

/-- The six values of `Fin 6`; used to split a check over the permutations of `Fin 6` by the
images of `0` and `1`, so that each part is a small kernel computation. -/
theorem fin6_cases (x : Fin 6) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  fin_cases x <;> simp

theorem fin7_cases (x : Fin 7) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
  fin_cases x <;> simp

end Babai.DM52
