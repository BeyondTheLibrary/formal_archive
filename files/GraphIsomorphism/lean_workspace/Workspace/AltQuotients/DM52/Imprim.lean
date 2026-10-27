/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: the transitive imprimitive case.
-/
import Workspace.AltQuotients.DM52.Combin
import Workspace.AltQuotients.DM52.OrbitTools
import Workspace.AltQuotients.DM52.SetStab

/-!
# Transitive imprimitive subgroups of small index in `A_n`

The second paragraph of the proof of [DiM, Thm. 5.2A] (p. 148):

> Now suppose that `G` is not primitive (and (ii) does not hold).  Then we claim that either
> `n ≤ 6`, or `G` is intransitive.  Indeed, suppose that `G` is transitive, and that `G` has
> `t` blocks of imprimitivity of size `n/t` with `2 ≤ t ≤ n/2`.  Then `G` is isomorphic to a
> subgroup of even permutations in a wreath product of order `{(n/t)!}^t t!` (see Exercise
> 2.6.2).  Thus `C(n,m) > h ≥ (n!/2) / ({(n/t)!}^t t!/2)`.  If `t = 2` (and so `n` is even),
> this inequality implies that `h = ½ C(n,m)` which is the case listed in (ii) of the
> theorem.  On the other hand, if `t ≥ 3`, then Lemma 5.2A (i) shows that `n ≤ 6`, and an
> examination of Table 2.1 gives the imprimitive exception listed in (iii).

Here `t` is the number of blocks, and `n/t ≥ 2` is their size.

* The wreath product is the stabilizer `partStab ℬ` of the block system `ℬ`; its order is at
  most `{(n/t)!}^t t!` (`card_partStab_le`: the kernel of the action on the blocks embeds in
  `∏_{B ∈ ℬ} Sym(B)`), and it contains a transposition, so its even part has at most half
  that order.
* For `t = 2`, `|A : G| = ½ C(n,m)` follows from `|A : G| < C(n,m)` because the index of the
  setwise stabilizer of a block is `C(n,m)` (`two_mul_relIndex_eq_of_halving`).
* For `t ≥ 3` and `n ≤ 6` the only case is `n = 6` with three blocks of size `2`; then
  `|G| ≤ 24` and `6 ∣ |G|`, so `|A : G| = 15`, which is less than `C(6, r)` only for `r = 3`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise

section Index

/-- `|H| · |K : H| = |K|` for `H ≤ K`. -/
theorem card_mul_relIndex {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have := (H.subgroupOf K).card_mul_index
  rwa [card_subgroupOf, inf_of_le_left h] at this

/-- A proper subgroup has at most half the order. -/
theorem two_mul_card_le_of_not_mem {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : H ≤ K) {x : G} (hxK : x ∈ K) (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  have e := card_mul_relIndex h
  have h1 : H.relIndex K ≠ 1 := fun h1 => hxH (Subgroup.relIndex_eq_one.mp h1 hxK)
  have h0 : H.relIndex K ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  calc 2 * Nat.card H ≤ Nat.card H * H.relIndex K := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    _ = Nat.card K := e

end Index

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `2 |A| = n!`. -/
theorem two_mul_card_alternatingGroup [Nontrivial Ω] :
    2 * Nat.card (alternatingGroup Ω) = (Nat.card Ω)! := by
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]

/-! ### The stabilizer of a partition -/

/-- The stabilizer in `Sym(Ω)` of a set `ℬ` of subsets of `Ω` (for a block system, the
wreath product of [DiM, Exercise 2.6.2]). -/
def partStab (ℬ : Set (Set Ω)) : Subgroup (Perm Ω) where
  carrier := {σ | ∀ C : Set Ω, C ∈ ℬ ↔ (σ : Perm Ω) '' C ∈ ℬ}
  mul_mem' := by
    intro a b ha hb C
    rw [hb C, ha (b '' C), Perm.coe_mul, Set.image_comp]
  one_mem' := by intro C; simp
  inv_mem' := by
    intro a ha C
    rw [ha ((a⁻¹ : Perm Ω) '' C), Set.image_image]
    simp

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_partStab {ℬ : Set (Set Ω)} {σ : Perm Ω} :
    σ ∈ partStab ℬ ↔ ∀ C : Set Ω, C ∈ ℬ ↔ σ '' C ∈ ℬ := Iff.rfl

omit [Fintype Ω] in
/-- A transposition of two points that lie in the same part, or in no part, of a partition
fixes every part. -/
theorem image_swap_eq {x y : Ω} {C : Set Ω} (h : x ∈ C ↔ y ∈ C) : (swap x y) '' C = C := by
  ext z
  rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, Equiv.symm_swap]
  by_cases hzx : z = x
  · subst hzx; rw [swap_apply_left]; exact h.symm
  by_cases hzy : z = y
  · subst hzy; rw [swap_apply_right]; exact h
  rw [swap_apply_of_ne_of_ne hzx hzy]

omit [Fintype Ω] in
/-- A transposition inside a part of a partition stabilizes the partition. -/
theorem swap_mem_partStab {ℬ : Set (Set Ω)}
    (hdisj : ∀ C ∈ ℬ, ∀ D ∈ ℬ, C ≠ D → Disjoint C D) {C₀ : Set Ω} (hC₀ : C₀ ∈ ℬ) {x y : Ω}
    (hx : x ∈ C₀) (hy : y ∈ C₀) : swap x y ∈ partStab ℬ := by
  have key : ∀ C ∈ ℬ, (swap x y) '' C = C := by
    intro C hC
    apply image_swap_eq
    by_cases hCC : C = C₀
    · subst hCC; exact ⟨fun _ => hy, fun _ => hx⟩
    · have hd := hdisj C hC C₀ hC₀ hCC
      exact ⟨fun h => absurd hx (Set.disjoint_left.mp hd h),
        fun h => absurd hy (Set.disjoint_left.mp hd h)⟩
  intro C
  constructor
  · intro hC; rw [key C hC]; exact hC
  · intro hC
    have := key _ hC
    rw [Set.image_image] at this
    simp only [swap_apply_self, Set.image_id'] at this
    rw [this]; exact hC

omit [DecidableEq Ω] in
/-- **The order of the wreath product** ([DiM, Exercise 2.6.2]): the stabilizer of a
partition of `Ω` into `t` parts of size `k` has order at most `(k!)^t t!`.  The action on
the parts has image in `Sym(ℬ)`, and its kernel embeds in `∏_{C ∈ ℬ} Sym(C)`. -/
theorem card_partStab_le (ℬ : Set (Set Ω)) (k : ℕ) (hcover : ∀ x, ∃ C ∈ ℬ, x ∈ C)
    (hk : ∀ C ∈ ℬ, C.ncard = k) :
    Nat.card (partStab ℬ) ≤ (k !) ^ ℬ.ncard * (ℬ.ncard)! := by
  classical
  have hperm : ∀ σ ∈ partStab ℬ, ∀ B ∈ ℬ, (σ : Perm Ω) '' B ∈ ℬ :=
    fun σ hσ B hB => (hσ B).mp hB
  set bh := blockHom (partStab ℬ) ℬ hperm with hbh
  have e1 : Nat.card (partStab ℬ) = Nat.card bh.ker * Nat.card bh.range := by
    rw [← Subgroup.index_ker, bh.ker.card_mul_index]
  -- the image
  have hrange : Nat.card bh.range ≤ (ℬ.ncard)! := by
    calc Nat.card bh.range ≤ Nat.card (Perm ℬ) := Subgroup.card_le_card_group _
      _ = (ℬ.ncard)! := by rw [Nat.card_perm, Nat.card_coe_set_eq]
  -- the kernel
  have hfix : ∀ σ : bh.ker, ∀ C : ℬ, ∀ x, x ∈ (C : Set Ω) ↔
      ((σ : partStab ℬ) : Perm Ω) x ∈ (C : Set Ω) := by
    intro σ C x
    have hC := (mem_ker_blockHom.mp σ.2) C C.2
    constructor
    · intro hx; rw [← hC]; exact Set.mem_image_of_mem _ hx
    · intro hx
      rw [← hC] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← ((σ : partStab ℬ) : Perm Ω).injective hyx]
  let ψ : bh.ker → ((C : ℬ) → Perm (C : Set Ω)) :=
    fun σ C => ((σ : partStab ℬ) : Perm Ω).subtypePerm (fun x => (hfix σ C x).symm)
  have hψ : Function.Injective ψ := by
    intro σ τ hστ
    apply Subtype.ext; apply Subtype.ext
    ext x
    obtain ⟨C, hC, hx⟩ := hcover x
    have := congrArg (fun f => ((f ⟨C, hC⟩ ⟨x, hx⟩ : (C : Set Ω)) : Ω)) hστ
    simpa [ψ] using this
  have hker : Nat.card bh.ker ≤ (k !) ^ ℬ.ncard := by
    calc Nat.card bh.ker ≤ Nat.card ((C : ℬ) → Perm (C : Set Ω)) :=
          Nat.card_le_card_of_injective ψ hψ
      _ = ∏ C : ℬ, (k !) := by
          rw [Nat.card_pi]
          refine Finset.prod_congr rfl (fun C _ => ?_)
          rw [Nat.card_perm, Nat.card_coe_set_eq, hk C C.2]
      _ = (k !) ^ ℬ.ncard := by
          rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
            Nat.card_coe_set_eq]
  rw [e1]
  exact Nat.mul_le_mul hker hrange

/-! ### Block systems of a transitive group -/

omit [Fintype Ω] [DecidableEq Ω] in
theorem smul_set_eq_image (G : Subgroup (Perm Ω)) (g : G) (C : Set Ω) :
    g • C = (g : Perm Ω) '' C := by
  rw [← Set.image_smul]; rfl

omit [Fintype Ω] [DecidableEq Ω] in
/-- The block system of a block `B` of a transitive group `G`: the orbit of `B`. -/
theorem blockSystem_facts {G : Subgroup (Perm Ω)} (hT : IsPretransitive G Ω) {B : Set Ω}
    (hB : IsBlock G B) (hBne : B.Nonempty) :
    (∀ x, ∃ C ∈ orbit G B, x ∈ C) ∧ (∀ C ∈ orbit G B, C.ncard = B.ncard) ∧
      (∀ C ∈ orbit G B, ∀ D ∈ orbit G B, C ≠ D → Disjoint C D) ∧
      G ≤ partStab (orbit G B) ∧ B.ncard * (orbit G B).ncard = Nat.card Ω := by
  refine ⟨?_, ?_, ?_, ?_, hB.ncard_block_mul_ncard_orbit_eq hBne⟩
  · intro x
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, hg⟩ := hT.exists_smul_eq b x
    exact ⟨g • B, mem_orbit B g, hg ▸ Set.smul_mem_smul_set hb⟩
  · rintro C ⟨g, rfl⟩
    exact Set.ncard_smul_set g B
  · rintro C ⟨g, rfl⟩ D ⟨h, rfl⟩ hne
    exact hB hne
  · intro σ hσ C
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨⟨σ, hσ⟩ * g, ?_⟩
      show (⟨σ, hσ⟩ * g : G) • B = σ '' (g • B)
      rw [mul_smul, smul_set_eq_image G ⟨σ, hσ⟩]
    · rintro ⟨g, hg⟩
      have hg' : g • B = σ '' C := hg
      refine ⟨⟨σ, hσ⟩⁻¹ * g, ?_⟩
      show (⟨σ, hσ⟩⁻¹ * g : G) • B = C
      rw [mul_smul, hg', smul_set_eq_image G ⟨σ, hσ⟩⁻¹, Set.image_image]
      simp

/-! ### The index for two blocks -/

/-- For `G ≤ A` preserving a partition into two halves, `|A : G| < C(n, n/2)` forces
`|A : G| = ½ C(n, n/2)`: the setwise stabilizer `A_{B}` of a half has index `C(n, n/2)`, and
`G ∩ A_{B}` has index at most `2` in `G`. -/
theorem two_mul_relIndex_eq_of_halving {G : Subgroup (Perm Ω)}
    (hGA : G ≤ alternatingGroup Ω) (hn : 5 ≤ Nat.card Ω) (hh : PreservesHalvingPartition G)
    (hlt : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose (Nat.card Ω / 2)) :
    2 * G.relIndex (alternatingGroup Ω) = (Nat.card Ω).choose (Nat.card Ω / 2) := by
  obtain ⟨B, hB2, hpres⟩ := hh
  have hm2 : B.ncard + 2 ≤ Nat.card Ω := by omega
  have hhalf : B.ncard = Nat.card Ω / 2 := by omega
  set A := alternatingGroup Ω
  set Q := setwiseStabilizer A B with hQdef
  set L := G ⊓ Q with hLdef
  have hQA : Q ≤ A := fun σ hσ => hσ.1
  have hQ : Q.relIndex A = (Nat.card Ω).choose (Nat.card Ω / 2) := by
    rw [← hhalf]; exact relIndex_setwiseStabilizer le_rfl hm2 rfl
  have hle2 : L.relIndex G ≤ 2 := relIndex_inf_le_two hGA hpres
  have e1 : L.relIndex Q * Q.relIndex A = L.relIndex A :=
    Subgroup.relIndex_mul_relIndex L Q A inf_le_right hQA
  have e2 : L.relIndex G * G.relIndex A = L.relIndex A :=
    Subgroup.relIndex_mul_relIndex L G A inf_le_left hGA
  have hpos1 : 0 < L.relIndex Q := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hpos2 : 0 < L.relIndex G := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  rw [hQ, ← e2] at e1
  generalize L.relIndex Q = j at *
  generalize L.relIndex G = e at *
  generalize G.relIndex A = h at *
  generalize (Nat.card Ω).choose (Nat.card Ω / 2) = c at *
  have he : e = 1 ∨ e = 2 := by omega
  rcases he with rfl | rfl
  · -- `h = j c ≥ c`
    nlinarith
  · have : j = 1 := by
      rcases Nat.lt_or_ge j 2 with hj | hj
      · omega
      · nlinarith
    subst this; omega

/-! ### The transitive imprimitive case -/

/-- **The transitive imprimitive case of [DiM, Thm. 5.2A]** (proof, second paragraph): a
transitive, not primitive `G ≤ A` with `|A : G| < C(n, r)` is in case (ii) or in the
exceptional case (iii)(a). -/
theorem imprimitive_case (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Perm Ω)} (hGA : G ≤ alternatingGroup Ω)
    (hindex : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose r)
    (hT : IsPretransitive G Ω) (hnp : ¬ IsPreprimitive G Ω) :
    (IsTransitive G ∧ PreservesHalvingPartition G ∧
        2 * G.relIndex (alternatingGroup Ω) = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
      (IsTransitive G ∧ ¬ IsPrimitive G ∧
        Nat.card Ω = 6 ∧ 3 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15) := by
  classical
  have hne : Nonempty Ω := (Nat.card_pos_iff.mp (by omega)).1
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  have hTr : IsTransitive G := (isTransitiveAction_iff G Ω).mpr ⟨hne, hT⟩
  have hmid : (Nat.card Ω).choose r ≤ (Nat.card Ω).choose (Nat.card Ω / 2) :=
    Nat.choose_le_middle r _
  -- a nontrivial block
  obtain ⟨B, hB, hBt⟩ : ∃ B : Set Ω, IsBlock G B ∧ ¬ IsTrivialBlock B := by
    by_contra hcon
    push Not at hcon
    exact hnp { toIsPretransitive := hT, isTrivialBlock_of_isBlock := fun hB => hcon _ hB }
  simp only [IsTrivialBlock, not_or] at hBt
  obtain ⟨hBs, hBu⟩ := hBt
  have hBnt : B.Nontrivial := Set.not_subsingleton_iff.mp hBs
  have hBne : B.Nonempty := hBnt.nonempty
  obtain ⟨hcover, hk, hdisj, hGW, hkt⟩ := blockSystem_facts hT hB hBne
  set ℬ := orbit G B
  set k := B.ncard with hkdef
  set t := ℬ.ncard with htdef
  have hk2 : 2 ≤ k := (Set.one_lt_ncard_iff_nontrivial).mpr hBnt
  have hkn : k < Nat.card Ω := by
    have := Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr hBu)
    rwa [Set.ncard_univ] at this
  have ht2 : 2 ≤ t := by
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t <;> omega
    · exact h
  -- `2|G| ≤ (k!)^t t!`
  obtain ⟨x, hx, y, hy, hxy⟩ := hBnt
  have hsw : swap x y ∈ partStab ℬ := swap_mem_partStab hdisj (mem_orbit_self B) hx hy
  have hGle : G ≤ alternatingGroup Ω ⊓ partStab ℬ := le_inf hGA hGW
  have h2G : 2 * Nat.card G ≤ (k !) ^ t * t ! := by
    calc 2 * Nat.card G ≤ 2 * Nat.card (alternatingGroup Ω ⊓ partStab ℬ : Subgroup _) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hGle)
      _ ≤ Nat.card (partStab ℬ) :=
          two_mul_card_le_of_not_mem inf_le_right hsw
            (fun h => by
              have := (mem_alternatingGroup.mp h.1)
              rw [sign_swap hxy] at this
              exact absurd this (by decide))
      _ ≤ (k !) ^ t * t ! := card_partStab_le ℬ k hcover hk
  have hh0 : 0 < G.relIndex (alternatingGroup Ω) := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  -- `2 |G| h = n!`
  have hGh : 2 * (Nat.card G * G.relIndex (alternatingGroup Ω)) = (Nat.card Ω)! := by
    rw [card_mul_relIndex hGA, two_mul_card_alternatingGroup]
  rcases Nat.lt_or_ge t 3 with ht | ht
  · -- two blocks: case (ii)
    have ht2' : t = 2 := by omega
    left
    have hB2 : 2 * B.ncard = Nat.card Ω := by rw [← hkt, ht2']; ring
    have hpres : PreservesHalvingPartition G := by
      refine ⟨B, hB2, fun σ hσ => ?_⟩
      rcases (isBlock_iff_smul_eq_or_disjoint.mp hB) ⟨σ, hσ⟩ with h | h
      · left; rwa [smul_set_eq_image] at h
      · right
        rw [smul_set_eq_image] at h
        have hsub : (σ : Perm Ω) '' B ⊆ Bᶜ := fun z hz => Set.disjoint_left.mp h hz
        apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
        have e1 := ncard_add_ncard_compl B
        have e2 : ((σ : Perm Ω) '' B).ncard = B.ncard :=
          Set.ncard_image_of_injective _ (σ : Perm Ω).injective
        omega
    exact ⟨hTr, hpres, two_mul_relIndex_eq_of_halving hGA hn hpres (hindex.trans_le hmid)⟩
  · -- at least three blocks
    rcases Nat.lt_or_ge 6 (Nat.card Ω) with h6 | h6
    · -- `n > 6`: Lemma 5.2A (i) gives `C(n, m) < h`
      exfalso
      have hL := lemma_5_2A_i hk2 ht (by rw [hkt]; exact h6)
      rw [hkt] at hL
      have hC := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self (Nat.card Ω) 2)
      set h := G.relIndex (alternatingGroup Ω)
      set m := Nat.card Ω / 2
      -- `C(n,m) m! (n-m)! = n! = 2|G| h ≤ (k!)^t t! h < m!(n-m)! h`
      have hpos : 0 < m ! * (Nat.card Ω - m)! := by positivity
      have hlt : (Nat.card Ω).choose m * (m ! * (Nat.card Ω - m)!) <
          h * (m ! * (Nat.card Ω - m)!) := by
        calc (Nat.card Ω).choose m * (m ! * (Nat.card Ω - m)!) = (Nat.card Ω)! := by
              rw [← hC]; ring
          _ = 2 * Nat.card G * h := by rw [← hGh]; ring
          _ ≤ (k !) ^ t * t ! * h := Nat.mul_le_mul_right _ h2G
          _ < m ! * (Nat.card Ω - m)! * h := by
              exact Nat.mul_lt_mul_of_pos_right hL hh0
          _ = h * (m ! * (Nat.card Ω - m)!) := by ring
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    · -- `n = 6`, three blocks of size `2`
      have hn6 : Nat.card Ω = 6 := by
        have : 2 * 3 ≤ k * t := Nat.mul_le_mul hk2 ht
        omega
      have hk2' : k = 2 := by
        rcases Nat.lt_or_ge k 3 with h | h
        · omega
        · have : 3 * 3 ≤ k * t := Nat.mul_le_mul h ht
          omega
      have ht3 : t = 3 := by rw [hk2'] at hkt; omega
      right
      refine ⟨hTr, fun hP => hnp ((isPrimitive_iff_isPreprimitive G).mp hP), hn6, ?_⟩
      rw [hk2', ht3, show (2 !) ^ 3 * 3 ! = 48 by decide] at h2G
      rw [hn6] at hGh
      have h6G : 6 ∣ Nat.card G := by
        rw [card_eq_card_mul_stabilizer hT x, ← Nat.card_eq_fintype_card, hn6]
        exact dvd_mul_right _ _
      set h := G.relIndex (alternatingGroup Ω)
      have e720 : (6 : ℕ)! = 720 := by decide
      rw [e720] at hGh
      have hcases : h = 15 ∨ h = 20 ∨ h = 30 ∨ h = 60 := by
        obtain ⟨c, hc⟩ := h6G
        rw [hc] at hGh h2G
        have : c ≤ 4 := by omega
        interval_cases c <;> omega
      have hr3 : r ≤ 3 := by omega
      rw [hn6] at hindex
      interval_cases r <;> simp [Nat.choose] at hindex <;> omega

end Babai.DM52
