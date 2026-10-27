/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background used by the proof of Lemma 10.2.5, Case 1 (the affine case): an internal direct
product of `s` isomorphic abelian simple groups is elementary abelian of order `p ^ s`.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.NoncommPiCoprod
import Workspace.Prelim.PrimitiveSocleGL

/-!
# Elementary abelian direct products

The proof of Lemma 10.2.5, Case 1, says: "`N` is abelian … In this case `N ≅ ℤ_p^s`".  By
Fact 10.2.2 (ii) the socle `N` is an internal direct product of `s` pairwise isomorphic
simple subgroups; if `N` is abelian, each factor is abelian simple, hence cyclic of prime
order `p`, and `N ≅ ℤ_p^s`.  That is `Babai.exists_prime_mulEquiv_of_abelian_directProduct`
below.  The hypotheses are spelled out rather than bundled as
`Babai.IsInternalDirectProduct`, so that this file can live under `Prelim/`.
-/

namespace Babai

variable {G : Type*} [Group G] {s : ℕ} {N : Subgroup G} {R : Fin s → Subgroup G}

/-- An internal direct product of `s` pairwise isomorphic *abelian* simple subgroups is
elementary abelian: it is isomorphic to `ℤ_p^s` for a prime `p`, and has order `p ^ s`.

This is the step "`N ≅ ℤ_p^s`, so `n = p^s`" in the proof of Lemma 10.2.5, Case 1
(Dixon–Mortimer, *Permutation Groups*, GTM 163, Theorem 4.3B (i), p. 114). -/
theorem exists_prime_mulEquiv_of_abelian_directProduct
    (hle : ∀ i, R i ≤ N) (hind : iSupIndep R) (hsup : ⨆ i, R i = N)
    (hsimple : ∀ i, IsSimpleGroup ↥(R i))
    (habel : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (i₀ : Fin s) (hiso : ∀ i, Nonempty (↥(R i) ≃* ↥(R i₀))) :
    ∃ p : ℕ, p.Prime ∧ Nonempty (↥N ≃* Multiplicative (Fin s → ZMod p)) ∧
      Nat.card ↥N = p ^ s := by
  classical
  haveI := hsimple
  -- each factor is an abelian simple group
  letI comm : ∀ i, CommGroup ↥(R i) := fun i =>
    { (inferInstance : Group ↥(R i)) with
      mul_comm := fun a b => Subtype.ext (habel a (hle i a.2) b (hle i b.2)) }
  set p : ℕ := Nat.card ↥(R i₀) with hp
  have hpprime : p.Prime := IsSimpleGroup.prime_card (α := ↥(R i₀))
  have hcard : ∀ i, Nat.card ↥(R i) = p := by
    intro i
    obtain ⟨e⟩ := hiso i
    exact Nat.card_congr e.toEquiv
  -- each factor is isomorphic to `Multiplicative (ZMod p)`
  have he : ∀ i, Nonempty (Multiplicative (ZMod p) ≃* ↥(R i)) := by
    intro i
    have hc : IsCyclic ↥(R i) := IsSimpleGroup.isCyclic
    exact ⟨(hcard i) ▸ zmodCyclicMulEquiv hc⟩
  have e : ∀ i, Multiplicative (ZMod p) ≃* ↥(R i) := fun i => (he i).some
  -- `N` is the internal direct product of the factors
  have hcomm : Pairwise fun i j : Fin s => ∀ x y : G, x ∈ R i → y ∈ R j → Commute x y := by
    intro i j _ x y hx hy
    exact habel x (hle i hx) y (hle j hy)
  set φ := Subgroup.noncommPiCoprod hcomm with hφ
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hφrange : φ.range = N := by rw [hφ, Subgroup.noncommPiCoprod_range, hsup]
  have hNiso : Nonempty ((∀ i, ↥(R i)) ≃* ↥N) :=
    ⟨(MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)⟩
  obtain ⟨eN⟩ := hNiso
  refine ⟨p, hpprime, ⟨?_⟩, ?_⟩
  · exact eN.symm.trans
      ((MulEquiv.piCongrRight fun i => (e i).symm).trans
        (MulEquiv.piMultiplicative fun _ : Fin s => ZMod p))
  · haveI : NeZero p := ⟨hpprime.ne_zero⟩
    have h1 : Nat.card ↥N = Nat.card (∀ i, ↥(R i)) := Nat.card_congr eN.symm.toEquiv
    have h2 : Nat.card (∀ i : Fin s, ↥(R i)) = p ^ s := by
      rw [Nat.card_pi]
      simp [hcard]
    rw [h1, h2]

end Babai
