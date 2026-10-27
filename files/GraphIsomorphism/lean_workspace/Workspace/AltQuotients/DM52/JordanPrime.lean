/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: Jordan's theorem on prime cycles.
-/
import Workspace.AltQuotients.DM52.Bochert
import Workspace.Prelim.PermGroups
import Mathlib.GroupTheory.Sylow

/-!
# Jordan's theorem on prime cycles ([DiM, Thm. 3.3E])

[DiM, Theorem 3.3E] (Dixon–Mortimer, *Permutation Groups*, GTM 163, p. 84): *Let
`G ≤ Sym(n)` be a primitive group which contains a cycle `x` of prime length `p`.  Then
either `G ≥ Alt(n)` or `n ≤ p + 2`.*  The exercises of [DiM, §5.2] (5.2.4–5.2.6) use it to
exclude the small primitive groups of degree `10, 11, 12, 14`.

We follow the structure of the proof in [DiM, p. 84]: `G` is multiply transitive
(the first step of [DiM]; here we use Jordan's criterion `IsPreprimitive.isMultiplyPreprimitive`
of Mathlib, which is [DiM, Exercise 3.3.16] iterated, cf. Wielandt, Thm. 13.1),
then the Frattini argument makes the normalizer `N` of `P := ⟨x⟩` induce the full symmetric
group on three fixed points of `x`, `N' ≤ C_G(P)` since `Aut(P)` is abelian, the centralizer
of the cycle `x` induces `⟨x⟩` on its support ([DiM, Exercise 3.3.17]), and a suitable element
of `N'` corrected by a power of `x` is a short cycle, so `G ≥ Alt(n)` by [DiM, Thm. 3.3A]
(Mathlib's `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`).  The only change
from [DiM] is that we produce a 3-cycle from `N'` directly (the commutator of a transposition
and a transposition of `Sym(E)` sharing one point), which is valid for every prime `p`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- Multiple transitivity in the form used below: a `|F|`-transitive group contains, for
every permutation `τ`, an element agreeing with `τ` on `F`. -/
theorem exists_mem_agree_of_isMultiplyPretransitive (G : Subgroup (Perm α)) (F : Finset α)
    [IsMultiplyPretransitive G α F.card] (τ : Perm α) :
    ∃ h ∈ G, ∀ z ∈ F, h z = τ z := by
  let e : Fin F.card ↪ α := F.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨h, hh⟩ := exists_smul_eq G e (e.trans τ.toEmbedding)
  refine ⟨h, h.2, fun z hz => ?_⟩
  have := congrArg (fun f : Fin F.card ↪ α => f (F.equivFin ⟨z, hz⟩)) hh
  simpa [e] using this

omit [Fintype α] [DecidableEq α] in
/-- [DiM, Exercise 3.3.17]: an element commuting with a cycle `g` acts on the support of `g`
as a power of `g`. -/
theorem exists_zpow_eqOn_support_of_commute {g w : Perm α} (hgc : g.IsCycle)
    (hw : Commute w g) : ∃ j : ℤ, ∀ z, g z ≠ z → w z = (g ^ j) z := by
  obtain ⟨a, ha, hcyc⟩ := hgc
  have hwa : g (w a) ≠ w a := by
    intro h
    apply ha
    have : w (g a) = w a := by
      rw [← Perm.mul_apply, hw.eq, Perm.mul_apply, h]
    exact w.injective this
  obtain ⟨j, hj⟩ := hcyc hwa
  refine ⟨j, fun z hz => ?_⟩
  obtain ⟨m, rfl⟩ := hcyc hz
  rw [← Perm.mul_apply, ((Commute.zpow_right hw m)).eq, Perm.mul_apply, ← hj,
    ← Perm.mul_apply, ← Perm.mul_apply, ← zpow_add, ← zpow_add, add_comm]

/-- The derived subgroup of the normalizer of a cyclic group centralizes it (`Aut(P)` is
abelian, [DiM, Exercise 2.2.2]), in the form used below. -/
theorem commute_commutator_of_normalizes {H : Type*} [Group H] {g u v : H}
    (hu : u * g * u⁻¹ ∈ Subgroup.zpowers g) (hu' : u⁻¹ * g * u ∈ Subgroup.zpowers g)
    (hv : v * g * v⁻¹ ∈ Subgroup.zpowers g) (hv' : v⁻¹ * g * v ∈ Subgroup.zpowers g) :
    Commute (u⁻¹ * v⁻¹ * u * v) g := by
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨d, hd⟩ := Subgroup.mem_zpowers_iff.mp hu'
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hv'
  have key : ∀ (y : H) (e : ℤ) (x : H), y * x ^ e * y⁻¹ = (y * x * y⁻¹) ^ e :=
    fun y e x => conj_zpow.symm
  have keyi : ∀ (y : H) (e : ℤ) (x : H), y⁻¹ * x ^ e * y = (y⁻¹ * x * y) ^ e := by
    intro y e x; simpa using key y⁻¹ e x
  have hca : (g ^ c) ^ a = g := by
    rw [hc, ← keyi, ha]; group
  have hdb : (g ^ d) ^ b = g := by
    rw [hd, ← keyi, hb]; group
  have h1 : (u⁻¹ * v⁻¹ * u * v) * g * (u⁻¹ * v⁻¹ * u * v)⁻¹ = g := by
    calc (u⁻¹ * v⁻¹ * u * v) * g * (u⁻¹ * v⁻¹ * u * v)⁻¹
        = u⁻¹ * (v⁻¹ * (u * (v * g * v⁻¹) * u⁻¹) * v) * u := by group
      _ = u⁻¹ * (v⁻¹ * g ^ (b * a) * v) * u := by
        rw [← ha, key, ← hb, ← zpow_mul]
      _ = u⁻¹ * g ^ (c * (b * a)) * u := by
        rw [keyi, ← hc, ← zpow_mul]
      _ = g ^ (d * (c * (b * a))) := by
        rw [keyi, ← hd, ← zpow_mul]
      _ = ((g ^ c) ^ a) ^ (d * b) := by rw [← zpow_mul, ← zpow_mul]; ring_nf
      _ = g := by rw [hca, zpow_mul, hdb]
  rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul, h1]

/-- The pointwise stabilizer in `G` of the fixed points of `g`. -/
abbrev fixSubgroup (G : Subgroup (Perm α)) (g : Perm α) : Subgroup (Perm α) :=
  G ⊓ (ofSubtype (p := (· ∈ g.support))).range

theorem mem_fixSubgroup {G : Subgroup (Perm α)} {g y : Perm α} :
    y ∈ fixSubgroup G g ↔ y ∈ G ∧ ∀ z, g z = z → y z = z := by
  rw [Subgroup.mem_inf, mem_range_ofSubtype_iff]
  refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h z hz => ?_⟩
  · by_contra hyz
    exact (Equiv.Perm.mem_support.mp (h (Equiv.Perm.mem_support.mpr hyz))) hz
  · simp only [Finset.mem_coe, Equiv.Perm.mem_support] at hz ⊢
    exact fun hgz => hz (h z hgz)

theorem card_fixSubgroup_dvd (G : Subgroup (Perm α)) (g : Perm α) :
    Nat.card (fixSubgroup G g) ∣ (g.support.card)! := by
  refine (Subgroup.card_dvd_of_le inf_le_right).trans ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective (ofSubtype_injective
    (p := (· ∈ g.support)))).toEquiv, Nat.card_perm, Nat.card_eq_finsetCard]

/-- `p² ∤ p!`. -/
theorem not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p ! := by
  intro h
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hp.one_le
  rw [Nat.factorial_succ, pow_two] at h
  have := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  rw [hp.dvd_factorial] at this
  omega

/-- The Frattini step of [DiM, proof of Thm. 3.3E]: if `u ∈ G` preserves the set of fixed
points of the `p`-cycle `g`, then some `u' ∈ u·K`, `K` the pointwise stabilizer of these
fixed points, normalizes `⟨g⟩` (a Sylow `p`-subgroup of `K`); `u'` agrees with `u` on the
fixed points of `g`. -/
theorem exists_normalizer_agree {G : Subgroup (Perm α)} {p : ℕ} (hp : p.Prime) {g : Perm α}
    (hgc : g.IsCycle) (hgp : g.support.card = p) (hg : g ∈ G)
    {u : Perm α} (hu : u ∈ G) (huF : ∀ z, g z = z → g (u z) = u z)
    (huF' : ∀ z, g z = z → g (u⁻¹ z) = u⁻¹ z) :
    ∃ u' ∈ G, (∀ z, g z = z → u' z = u z) ∧
      u' * g * u'⁻¹ ∈ Subgroup.zpowers g ∧ u'⁻¹ * g * u' ∈ Subgroup.zpowers g := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K := fixSubgroup G g
  have hgK : g ∈ K := mem_fixSubgroup.mpr ⟨hg, fun z hz => hz⟩
  have hxK : u * g * u⁻¹ ∈ K := by
    refine mem_fixSubgroup.mpr ⟨G.mul_mem (G.mul_mem hu hg) (G.inv_mem hu), fun z hz => ?_⟩
    simp only [Perm.mul_apply, huF' z hz, perm_apply_inv_self]
  have hord : orderOf g = p := by rw [hgc.orderOf, hgp]
  have hordx : orderOf (u * g * u⁻¹) = p := by
    rw [← hord, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hfact : (Nat.card K).factorization p = 1 := by
    have hdvd : p ∣ Nat.card K := by
      rw [← hord, ← Subgroup.orderOf_mk g hgK]; exact orderOf_dvd_natCard _
    have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    apply le_antisymm
    · by_contra hlt
      have : p ^ 2 ∣ Nat.card K :=
        (hp.pow_dvd_iff_le_factorization hK0).mpr (by omega)
      exact not_sq_dvd_factorial hp
        (this.trans (hgp ▸ card_fixSubgroup_dvd G g))
    · exact (hp.dvd_iff_one_le_factorization hK0).mp hdvd
  let gK : K := ⟨g, hgK⟩
  let xK : K := ⟨u * g * u⁻¹, hxK⟩
  let PS : Sylow p K := Sylow.ofCard (Subgroup.zpowers gK) (by
    rw [Nat.card_zpowers, hfact, pow_one, Subgroup.orderOf_mk, hord])
  let QS : Sylow p K := Sylow.ofCard (Subgroup.zpowers xK) (by
    rw [Nat.card_zpowers, hfact, pow_one, Subgroup.orderOf_mk, hordx])
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K QS PS
  have hmem : ∀ y : K, y ∈ Subgroup.zpowers xK ↔ k * y * k⁻¹ ∈ Subgroup.zpowers gK := by
    intro y
    have : (MulAut.conj k • (QS : Subgroup K)) = (PS : Subgroup K) := by
      rw [← Sylow.coe_subgroup_smul, hk]
    change y ∈ (QS : Subgroup K) ↔ k * y * k⁻¹ ∈ (PS : Subgroup K)
    rw [← this, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  refine ⟨(k : Perm α) * u, G.mul_mem (Subgroup.mem_inf.mp k.2).1 hu, fun z hz => ?_, ?_, ?_⟩
  · rw [Perm.mul_apply]
    exact (mem_fixSubgroup.mp k.2).2 _ (huF z hz)
  · have h1 := (hmem xK).mp (Subgroup.mem_zpowers xK)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, gK, xK] at this
    rw [this]; group
  · have h1 := (hmem (k⁻¹ * gK * k)).mpr (by
      simp [mul_assoc])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, gK, xK] at this
    rw [conj_zpow] at this
    rw [mul_inv_rev, show u⁻¹ * (k : Perm α)⁻¹ * g * (k * u) =
      u⁻¹ * ((k : Perm α)⁻¹ * g * k) * u by group, ← this]
    group

omit [Fintype α] [DecidableEq α] in
theorem agree_inv {F : Finset α} {u σ : Perm α} (hσ' : ∀ z ∈ F, σ⁻¹ z ∈ F)
    (h : ∀ z ∈ F, u z = σ z) : ∀ z ∈ F, u⁻¹ z = σ⁻¹ z := by
  intro z hz
  rw [Perm.inv_eq_iff_eq, h _ (hσ' z hz), perm_apply_inv_self]

omit [Fintype α] in
theorem swap_mem {F : Finset α} {x y z : α} (hx : x ∈ F) (hy : y ∈ F) (hz : z ∈ F) :
    swap x y z ∈ F := by
  rw [swap_apply_def]; split_ifs <;> assumption

/-- **[DiM, Theorem 3.3E]** (finite case, in Mathlib's language): a primitive group of degree
`n` containing a cycle of prime length `p ≤ n - 3` contains `Alt(n)`.  This is the
`proof_wanted` `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` of Mathlib. -/
theorem alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α)
    {g : Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p)
    (hg : g ∈ G) : alternatingGroup α ≤ G := by
  classical
  have hp2 := hp.two_le
  set F : Finset α := g.supportᶜ with hF
  have hmemF : ∀ z, z ∈ F ↔ g z = z := by simp [F]
  have hn : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have hFcard : F.card = Nat.card α - p := by
    rw [Finset.card_compl, hgp, hn]
  -- Step 1 ([DiM]): `G` is `(n - p + 1)`-fold primitive (Jordan's criterion).
  have hmp : IsMultiplyPreprimitive G α (Nat.card α - p - 1 + 2) := by
    apply hG.isMultiplyPreprimitive (s := ((g.support : Set α)ᶜ))
    · rw [← Finset.coe_compl, Set.ncard_coe_finset, ← hF, hFcard]; omega
    · have := hp.two_le; omega
    · have := isPretransitive_of_isCycle_mem hgc hg
      apply IsPreprimitive.of_prime_card
      convert hp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hgp]
      congr 1; ext x; simp [SubMulAction.mem_ofFixingSubgroup_iff]
  haveI : IsMultiplyPretransitive G α F.card := by
    haveI := hmp.isMultiplyPretransitive
    exact isMultiplyPretransitive_of_le (n := Nat.card α - p - 1 + 2) (by omega) (by omega)
  -- three fixed points `a, b, c` of `g`
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < F.card)
  -- Step 2 (Frattini): elements of `N_G(⟨g⟩)` inducing `(a b)` and `(b c)` on `fix(g)`.
  have hnorm : ∀ x y, x ∈ F → y ∈ F → ∃ u' ∈ G, (∀ z ∈ F, u' z = swap x y z) ∧
      u' * g * u'⁻¹ ∈ Subgroup.zpowers g ∧ u'⁻¹ * g * u' ∈ Subgroup.zpowers g := by
    intro x y hx hy
    obtain ⟨u, hu, hus⟩ := exists_mem_agree_of_isMultiplyPretransitive G F (swap x y)
    have hus' := agree_inv (fun z hz => by rw [swap_inv]; exact swap_mem hx hy hz) hus
    obtain ⟨u', hu', hagree, h1, h2⟩ := exists_normalizer_agree hp hgc hgp hg hu
      (fun z hz => (hmemF _).mp (by
        rw [hus z ((hmemF z).mpr hz)]; exact swap_mem hx hy ((hmemF z).mpr hz)))
      (fun z hz => (hmemF _).mp (by
        rw [hus' z ((hmemF z).mpr hz), swap_inv]; exact swap_mem hx hy ((hmemF z).mpr hz)))
    exact ⟨u', hu', fun z hz => (hagree z ((hmemF z).mp hz)).trans (hus z hz), h1, h2⟩
  obtain ⟨u, hu, hus, hu1, hu2⟩ := hnorm a b ha hb
  obtain ⟨v, hv, hvt, hv1, hv2⟩ := hnorm b c hb hc
  -- Step 3: the commutator `w` centralizes `g`, so on `supp(g)` it is a power of `g`.
  set w := u⁻¹ * v⁻¹ * u * v with hw
  have hwg : Commute w g := commute_commutator_of_normalizes hu1 hu2 hv1 hv2
  obtain ⟨j, hj⟩ := exists_zpow_eqOn_support_of_commute hgc hwg
  -- Step 4: `(g^j)⁻¹ w` is the 3-cycle `[(a b), (b c)]`.
  set T : Perm α := (swap a b)⁻¹ * (swap b c)⁻¹ * swap a b * swap b c with hT
  have hT3 : IsThreeCycle T := by
    apply isThreeCycle_commutator (a := b)
    · rw [swap_apply_right]; exact hab
    · rw [swap_apply_left]; exact hbc.symm
    · intro z h1 h2
      by_contra hzb
      have hza : z = a := by
        by_contra hza; exact h1 (swap_apply_of_ne_of_ne hza hzb)
      have hzc : z = c := by
        by_contra hzc; exact h2 (swap_apply_of_ne_of_ne hzb hzc)
      exact hac (hza.symm.trans hzc)
  have hus' := agree_inv (fun z hz => by rw [swap_inv]; exact swap_mem ha hb hz) hus
  have hvt' := agree_inv (fun z hz => by rw [swap_inv]; exact swap_mem hb hc hz) hvt
  have hTe : (g ^ j)⁻¹ * w = T := by
    ext z
    by_cases hz : g z = z
    · have hzF := (hmemF z).mpr hz
      have e1 := swap_mem hb hc hzF
      have e2 := swap_mem ha hb e1
      have e3 : (swap b c)⁻¹ (swap a b (swap b c z)) ∈ F := by
        rw [swap_inv]; exact swap_mem hb hc e2
      have e4 : (swap a b)⁻¹ ((swap b c)⁻¹ (swap a b (swap b c z))) ∈ F := by
        rw [swap_inv]; exact swap_mem ha hb e3
      simp only [hw, hT, Perm.mul_apply]
      rw [hvt z hzF, hus _ e1, hvt' _ e2, hus' _ e3]
      rw [Perm.inv_eq_iff_eq]
      exact (zpow_apply_eq_self_of_apply_eq_self ((hmemF _).mp e4) j).symm
    · have hza : z ≠ a := fun h => hz ((hmemF z).mp (h ▸ ha))
      have hzb : z ≠ b := fun h => hz ((hmemF z).mp (h ▸ hb))
      have hzc : z ≠ c := fun h => hz ((hmemF z).mp (h ▸ hc))
      rw [Perm.mul_apply, hj z hz, perm_inv_apply_self]
      simp only [hT, Perm.mul_apply, swap_inv, swap_apply_of_ne_of_ne hzb hzc,
        swap_apply_of_ne_of_ne hza hzb]
  have hTG : T ∈ G := by
    rw [← hTe]
    exact G.mul_mem (G.inv_mem (G.zpow_mem hg j))
      (G.mul_mem (G.mul_mem (G.mul_mem (G.inv_mem hu) (G.inv_mem hv)) hu) hv)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG hT3 hTG

/-- **[DiM, Theorem 3.3E]** (Dixon–Mortimer, p. 84), finite degree: "Let `G ≤ Sym(n)` be a
primitive group which contains a cycle `x` of prime length `p`.  Then either `G ≥ Alt(n)` or
`|Ω| ≤ p + 2`."  Primitivity is the paper's `Babai.IsPrimitive`. -/
theorem theorem_3_3E {G : Subgroup (Perm α)} (hG : Babai.IsPrimitive G)
    {p : ℕ} (hp : p.Prime) {x : Perm α} (hxc : x.IsCycle) (hxp : x.support.card = p)
    (hx : x ∈ G) : alternatingGroup α ≤ G ∨ Nat.card α ≤ p + 2 := by
  by_cases hn : p + 3 ≤ Nat.card α
  · left
    haveI : Nontrivial α := by
      rw [← Finite.one_lt_card_iff_nontrivial]; omega
    exact alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
      ((Babai.isPrimitive_iff_isPreprimitive G).mp hG) hp hn hxc hxp hx
  · right; omega

end Babai.DM52
