/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: Sylow arguments for permutation groups.
-/
import Workspace.AltQuotients.DM52.JordanPrime
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Sylow tools for the small-degree cases of [DiM, Thm. 5.2A,B]

[DiM, Exercises 5.2.3–5.2.6] leave the primitive groups of degree `≤ 12` and `14` to the
reader; the hint of Exercise 5.2.5 uses Jordan's theorem 3.3E and Sylow's theorems.  This file
collects the general facts used there.

* `exists_isCycle_mem_of_not_dvd_index`: if `p ≤ n` is a prime not dividing `|Sym(n) : G|`,
  then `G` contains a `p`-cycle (a Sylow `p`-subgroup of `G` is one of `Sym(n)`).
* `alternatingGroup_le_of_not_dvd_index`: with Theorem 3.3E, a primitive `G` with
  `p + 3 ≤ n` and `p ∤ |Sym(n) : G|` contains `Alt(n)`.
* `card_normalizer_zpowers_dvd`: `|N_S(⟨x⟩)|` divides `|C_S(x)| · φ(o(x))`.
* Sylow counting, Burnside's transfer theorem in the form used, and the transitivity of
  nontrivial normal subgroups of primitive groups.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `Sym(α)` contains a `p`-cycle whenever `2 ≤ p ≤ |α|`. -/
theorem exists_isCycle_card_support {p : ℕ} (hp : 2 ≤ p) (hpn : p ≤ Fintype.card α) :
    ∃ c : Perm α, c.IsCycle ∧ c.support.card = p := by
  obtain ⟨c, hc⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := α) (m := {p})).mpr
    ⟨by simpa using hpn, by simpa using hp⟩
  refine ⟨c, ?_, ?_⟩
  · rw [← card_cycleType_eq_one, hc]; rfl
  · rw [← sum_cycleType, hc]; simp

/-- A subgroup `G ≤ Sym(α)` whose index is prime to `p` contains a `p`-cycle, for every prime
`p ≤ |α|`: a Sylow `p`-subgroup of `G` is a Sylow `p`-subgroup of `Sym(α)`, and every Sylow
`p`-subgroup of `Sym(α)` contains a conjugate of a given `p`-cycle. -/
theorem exists_isCycle_mem_of_not_dvd_index {G : Subgroup (Perm α)} {p : ℕ} (hp : p.Prime)
    (hpn : p ≤ Fintype.card α) (hdvd : ¬ p ∣ G.index) :
    ∃ c ∈ G, c.IsCycle ∧ c.support.card = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c₀, hc₀, hc₀p⟩ := exists_isCycle_card_support hp.two_le hpn
  -- a Sylow `p`-subgroup of `G`, as a subgroup of `Sym(α)`
  let P : Sylow p G := default
  have hPcard : Nat.card (P.map G.subtype) =
      p ^ (Nat.card (Perm α)).factorization p := by
    rw [Subgroup.card_map_of_injective G.subtype_injective, P.card_eq_multiplicity,
      ← G.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' G.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hdvd, add_zero]
  let P' : Sylow p (Perm α) := Sylow.ofCard _ hPcard
  -- a Sylow `p`-subgroup of `Sym(α)` containing `c₀`
  have hc₀ord : orderOf c₀ = p := by rw [hc₀.orderOf, hc₀p]
  have hpg : IsPGroup p (zpowers c₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc₀ord, pow_one])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm α) Q P'
  have hmem : g * c₀ * g⁻¹ ∈ (P' : Subgroup (Perm α)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hQ (Subgroup.mem_zpowers c₀)
  obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hmem
  refine ⟨g * c₀ * g⁻¹, ?_, hc₀.conj, ?_⟩
  · rw [← hyc]; exact y.2
  · rw [card_support_conj, hc₀p]

/-- **[DiM, Theorem 3.3E] applied through Sylow's theorem**: a primitive `G ≤ Sym(α)` whose
index is prime to a prime `p` with `p + 3 ≤ |α|` contains `Alt(α)`. -/
theorem alternatingGroup_le_of_not_dvd_index {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    {p : ℕ} (hp : p.Prime) (hpn : p + 3 ≤ Fintype.card α) (hdvd : ¬ p ∣ G.index) :
    alternatingGroup α ≤ G := by
  obtain ⟨c, hcG, hc, hcp⟩ := exists_isCycle_mem_of_not_dvd_index hp (by omega) hdvd
  exact alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hG hp
    (by rw [Nat.card_eq_fintype_card]; exact hpn) hc hcp hcG

/-- `|H ∩ K| = |H.subgroupOf K|`. -/
theorem card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

omit [Fintype α] [DecidableEq α] in
/-- The centralizer of the cyclic group `⟨x⟩` is the centralizer of `x`. -/
theorem centralizer_zpowers_eq (x : Perm α) :
    centralizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) =
      centralizer ({x} : Set (Perm α)) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by simp)
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hy x rfl) k)).eq

omit [DecidableEq α] in
/-- `|N_S(⟨x⟩)|` divides `|C_S(x)| · φ(o(x))`: the normalizer acts on the cyclic group
`⟨x⟩` by conjugation, with kernel the centralizer, and `|Aut ⟨x⟩| = φ(o(x))`. -/
theorem card_normalizer_zpowers_dvd (x : Perm α) :
    Nat.card (normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α))) ∣
      Nat.card (centralizer ({x} : Set (Perm α))) * φ (orderOf x) := by
  set H : Subgroup (Perm α) := zpowers x
  set f := H.normalizerMonoidHom
  have hker : Nat.card f.ker = Nat.card (centralizer ({x} : Set (Perm α))) := by
    rw [Subgroup.normalizerMonoidHom_ker, card_subgroupOf, inf_of_le_left
      (Subgroup.centralizer_le_normalizer _), centralizer_zpowers_eq]
  have hrange : Nat.card f.range ∣ φ (orderOf x) := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [IsCyclic.card_mulAut, Nat.card_zpowers] at this
  rw [← f.ker.card_mul_index, hker, Subgroup.index_ker]
  exact Nat.mul_dvd_mul_left _ hrange

/-- A subgroup `K ≤ Sym(α)` containing an odd permutation has `|K| = 2·|K ∩ Alt(α)|`. -/
theorem card_eq_two_mul_card_inf_alternatingGroup (K : Subgroup (Perm α))
    {y : Perm α} (hy : y ∈ K) (hyodd : sign y = -1) :
    Nat.card K = 2 * Nat.card (alternatingGroup α ⊓ K : Subgroup _) := by
  let f : K →* ℤˣ := (sign).comp K.subtype
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨⟨y, hy⟩, by simpa [f] using hyodd⟩
  have hker : f.ker = (alternatingGroup α).subgroupOf K := by
    ext z; simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_alternatingGroup]
  rw [← f.ker.card_mul_index, Subgroup.index_ker, hker, card_subgroupOf,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, mul_comm,
    show Nat.card ℤˣ = 2 by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]]

/-- **Burnside's transfer theorem** in the form used in [DiM, Exercises 5.2.3–5.2.6]: if a
Sylow `p`-subgroup `P` of prime order is its own normalizer, then `P` has a normal
complement `K`, so `|K| · p = |G|`. -/
theorem exists_normal_card_mul_eq_of_normalizer_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) (hP : Nat.card P = p)
    (hN : normalizer ((P : Subgroup G) : Set G) = P) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card K * p = Nat.card G := by
  haveI : IsCyclic P := isCyclic_of_prime_card hP
  have hle : normalizer ((P : Subgroup G) : Set G) ≤ centralizer ((P : Subgroup G) : Set G) := by
    rw [hN]
    intro a ha b hb
    have := IsCyclic.commGroup.mul_comm (⟨a, ha⟩ : P) ⟨b, hb⟩
    exact congrArg Subtype.val this.symm
  refine ⟨(MonoidHom.transferSylow P hle).ker, MonoidHom.normal_ker _, ?_⟩
  have := (MonoidHom.ker_transferSylow_isComplement' P hle).card_mul
  rwa [hP] at this

/-- **Sylow counting in `Alt(α)`** ([DiM, Exercises 5.2.3–5.2.6]).  Let `G ≤ Alt(α)`, let
`p` be a prime with `p ∣ |G|` and `p² ∤ |G|`, and suppose that the normalizer in `Sym(α)` of
every subgroup `⟨x⟩ ≤ G` of order `p` contains an odd permutation.  Then some `x ∈ G` of
order `p` generates a Sylow `p`-subgroup; with `N := N_S(⟨x⟩)`,
`2·|A ∩ N|` divides `|C_S(x)|·(p-1)`, `|G ∩ N|` divides `|A ∩ N|` and `|G|`, the number
`|G|/|G ∩ N|` of Sylow `p`-subgroups is `≡ 1 (mod p)`, and if `|G ∩ N| = p` then `G` has a
normal subgroup of order `|G|/p` (Burnside). -/
theorem sylow_normalizer_facts {G : Subgroup (Perm α)}
    (hGA : G ≤ alternatingGroup α) {p : ℕ} (hp : p.Prime) (hpG : p ∣ Nat.card G)
    (hp2 : ¬ p ^ 2 ∣ Nat.card G)
    (hodd : ∀ x ∈ G, orderOf x = p →
      ∃ y ∈ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)), sign y = -1) :
    ∃ x ∈ G, orderOf x = p ∧
      2 * Nat.card (alternatingGroup α ⊓
          normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) : Subgroup _) ∣
        Nat.card (centralizer ({x} : Set (Perm α))) * (p - 1) ∧
      Nat.card (G ⊓ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) : Subgroup _) ∣
        Nat.card (alternatingGroup α ⊓
          normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) : Subgroup _) ∧
      Nat.card (G ⊓ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) : Subgroup _) ∣
        Nat.card G ∧
      Nat.card G / Nat.card (G ⊓ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) :
        Subgroup _) % p = 1 ∧
      (Nat.card (G ⊓ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)) :
          Subgroup _) = p →
        ∃ K : Subgroup (Perm α), K ≤ G ∧ (K.subgroupOf G).Normal ∧
          Nat.card K * p = Nat.card G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := default
  have hfact : (Nat.card G).factorization p = 1 := by
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    apply le_antisymm
    · by_contra h
      exact hp2 ((hp.pow_dvd_iff_le_factorization h0).mpr (by omega))
    · exact (hp.dvd_iff_one_le_factorization h0).mp hpG
  have hPcard : Nat.card P = p := by rw [P.card_eq_multiplicity, hfact, pow_one]
  set P' : Subgroup (Perm α) := P.map G.subtype with hP'
  have hP'card : Nat.card P' = p := by
    rw [hP', Subgroup.card_map_of_injective G.subtype_injective, hPcard]
  have hP'G : P' ≤ G := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  -- a generator `x` of `P'`
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P', x ≠ 1 := by
    by_contra h
    push Not at h
    have : P' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hP'card
    exact hp.one_lt.ne hP'card
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      rw [← hP'card, ← Subgroup.orderOf_mk x hxP]; exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzP : (zpowers x : Subgroup (Perm α)) = P' := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr hxP
    · rw [hP'card, Nat.card_zpowers, hxord]
  -- `N_G(P) ≅ G ∩ N_S(P')`
  have hsub : (P : Subgroup G) = P'.subgroupOf G := by
    rw [hP']; exact (Subgroup.comap_map_eq_self_of_injective G.subtype_injective _).symm
  have hNG : Nat.card (normalizer ((P : Subgroup G) : Set G)) =
      Nat.card (G ⊓ normalizer (P' : Set (Perm α)) : Subgroup _) := by
    rw [hsub, ← Subgroup.subgroupOf_normalizer_eq hP'G, card_subgroupOf, inf_comm]
  refine ⟨x, hP'G hxP, hxord, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hzP]
  · obtain ⟨y, hy, hyodd⟩ := hodd x (hP'G hxP) hxord
    have h2 := card_eq_two_mul_card_inf_alternatingGroup
      (normalizer (P' : Set (Perm α))) (hzP ▸ hy) hyodd
    have h3 := card_normalizer_zpowers_dvd x
    rw [hzP, hxord, Nat.totient_prime hp, h2] at h3
    exact h3
  · apply Subgroup.card_dvd_of_le
    intro z hz
    exact ⟨hGA hz.1, hz.2⟩
  · rw [← hNG]; exact Subgroup.card_subgroup_dvd_card _
  · rw [← hNG]
    have h1 := card_sylow_modEq_one (p := p) (G := G)
    rw [Sylow.card_eq_index_normalizer P] at h1
    have h2 := (normalizer ((P : Subgroup G) : Set G)).card_mul_index
    have hpos : 0 < Nat.card (normalizer ((P : Subgroup G) : Set G)) := Nat.card_pos
    rw [← h2, Nat.mul_div_cancel_left _ hpos]
    rw [Nat.ModEq] at h1
    have h1' : (normalizer ((P : Subgroup G) : Set G)).index % p = 1 % p := h1
    rw [h1', Nat.one_mod_eq_one.mpr hp.one_lt.ne']
  · intro hd
    rw [← hNG] at hd
    have hN : normalizer ((P : Subgroup G) : Set G) = P := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.le_normalizer)
      rw [hd, hPcard]
    obtain ⟨K₀, hK₀, hK₀card⟩ := exists_normal_card_mul_eq_of_normalizer_eq P hPcard hN
    refine ⟨K₀.map G.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩; exact y.2
    · have : (K₀.map G.subtype).subgroupOf G = K₀ :=
        Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
      rw [this]; exact hK₀
    · rw [Subgroup.card_map_of_injective G.subtype_injective, hK₀card]

/-- The numerical form of `sylow_normalizer_facts`: with `d := |N_G(P)|`,
`2d ∣ |C_S(x)|·(p-1)`, `d ∣ |G|`, `|G|/d ≡ 1 (mod p)`, and Burnside when `d = p`. -/
theorem sylow_count_of_le_alternatingGroup {G : Subgroup (Perm α)}
    (hGA : G ≤ alternatingGroup α) {p : ℕ} (hp : p.Prime) (hpG : p ∣ Nat.card G)
    (hp2 : ¬ p ^ 2 ∣ Nat.card G)
    (hodd : ∀ x ∈ G, orderOf x = p →
      ∃ y ∈ normalizer ((zpowers x : Subgroup (Perm α)) : Set (Perm α)), sign y = -1) :
    ∃ x ∈ G, orderOf x = p ∧ ∃ d : ℕ,
      2 * d ∣ Nat.card (centralizer ({x} : Set (Perm α))) * (p - 1) ∧ d ∣ Nat.card G ∧
      Nat.card G / d % p = 1 ∧
      (d = p → ∃ K : Subgroup (Perm α), K ≤ G ∧ (K.subgroupOf G).Normal ∧
        Nat.card K * p = Nat.card G) := by
  obtain ⟨x, hx, hxo, h1, h2, h3, h4, h5⟩ := sylow_normalizer_facts hGA hp hpG hp2 hodd
  exact ⟨x, hx, hxo, _, (Nat.mul_dvd_mul_left 2 h2).trans h1, h3, h4, h5⟩

/-- A nontrivial normal subgroup `K` of a primitive group `G ≤ Sym(α)` is transitive
([DiM, Theorem 1.6A (i)]; Wielandt, Thm. 7.1), so `|α|` divides `|K|`. -/
theorem card_dvd_card_of_normal {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    {K : Subgroup (Perm α)} (hKG : K ≤ G) (hKn : (K.subgroupOf G).Normal) (hK : K ≠ ⊥) :
    Fintype.card α ∣ Nat.card K := by
  obtain ⟨k, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK
  obtain ⟨a, ha⟩ : ∃ a, (k : Perm α) a ≠ a := by
    by_contra h
    push Not at h
    exact hk1 (Subtype.ext (Equiv.ext h))
  set N := K.subgroupOf G
  have hfix : MulAction.fixedPoints N α ≠ Set.univ := by
    intro h
    have : (⟨⟨k, hKG k.2⟩, by simp [N, Subgroup.mem_subgroupOf]⟩ : N) • a = a :=
      (Set.ext_iff.mp h a).mpr trivial _
    exact ha this
  haveI := hG
  haveI : IsPretransitive N α :=
    IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfix
  have h1 := MulAction.index_stabilizer N a
  rw [MulAction.orbit_eq_univ, Set.ncard_univ] at h1
  have h2 := (MulAction.stabilizer N a).index_dvd_card
  rw [h1, card_subgroupOf, inf_of_le_left hKG, Nat.card_eq_fintype_card] at h2
  exact h2

omit [Fintype α] [DecidableEq α] in
/-- A transitive abelian group `A ≤ Sym(α)` is its own centralizer: if `y` commutes with
every element of `A`, then `y ∈ A` ([DiM, Theorem 4.2A]). -/
theorem mem_of_commute_of_isPretransitive {A : Subgroup (Perm α)} (hA : IsPretransitive A α)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {y : Perm α}
    (hy : ∀ a ∈ A, a * y = y * a) : y ∈ A := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · have : y = 1 := Equiv.ext (fun z => isEmptyElim z)
    rw [this]; exact A.one_mem
  obtain ⟨a, ha⟩ := hA.exists_smul_eq x₀ (y x₀)
  have hay : (a : Perm α) = y := by
    ext z
    obtain ⟨b, hb⟩ := hA.exists_smul_eq x₀ z
    rw [← hb]
    simp only [Subgroup.smul_def, Perm.smul_def] at ha hb ⊢
    rw [← Perm.mul_apply, hcomm _ a.2 _ b.2, Perm.mul_apply, ha, ← Perm.mul_apply,
      hy _ b.2, Perm.mul_apply]
  rw [← hay]; exact a.2

end Babai.DM52
