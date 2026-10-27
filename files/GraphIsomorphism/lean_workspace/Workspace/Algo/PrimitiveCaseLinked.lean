/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sec. 15, line 4: the test of the Master is the paper's test `Ω = Φ`.
-/
import Workspace.Algo.TopMasterHintLink
import Workspace.Master.PrimitiveCaseConstruct

/-!
# Sec. 15, line 4: `IsPrimitiveCase` is the test `Ω = Φ`

Line 4 of the Master Algorithm reads *"if `G` primitive (: i.e. `Ω = Φ` :)"*, where
`Φ = {B_T | T ∈ Γ^{(t)}}` is the set of standard blocks of Theorem 10.5.1 (line 3). The Master
tests `Babai.IsPrimitiveCase`: an identification `Ω ≃ Γ^{(t)}` with `u ↦ T(u)`, for the
parameter `t` of the Johnson hint. `Babai.nonempty_primitiveCaseId_iff` shows that this is the
test *"`u ↦ T(u)` is injective and `|T(u)| = t`"*.

This file removes the second clause for the hints the Master actually carries, those whose giant
representation is the action on the blocks of the hint (`Algo.MasterHintLinked`): when the
standard blocks are singletons, the label of the block of `u` is `T(u)`
(`Algo.MasterHintBlockLink.Tpoint_eq_label`), so `|T(u)| = t` holds automatically. The
argument: a permutation `π ∈ A(Γ)` that fixes `T(u)` setwise comes from some `g ∈ G`, and
Eq. (54) with injectivity of `T` gives `u^g = u`; so `g` fixes the block of `u`, and `π` fixes its
label `S`. A 3-cycle outside `T(u)` shows `S ⊆ T(u)`, and a double transposition moving a point
of `S` to a point of `T(u) ∖ S` shows `T(u) ⊆ S`.

The final statement is `Algo.isPrimitiveCase_iff_standardBlock_singleton`: for a linked hint,
under the hypothesis of Theorem 10.5.1, line 4's test holds exactly when every standard block is
a singleton, that is, when `Ω = Φ`.
-/

namespace Algo
open Babai Equiv MulAction
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B} {m t : ℕ}
    {φ : G →* Perm (Fin m)}

namespace MasterHintBlockLink

omit [Fintype Ω] [DecidableEq Ω] in
/-- A group element that fixes `u` fixes the label of the block that contains `u`. -/
theorem label_fixed (L : MasterHintBlockLink (t := t) hB φ)
    (hs : IsInvariantPartitionOn G Set.univ B) {u : Ω} {β : B} (hu : u ∈ (β : Set Ω))
    {g : G} (hg : (g : Perm Ω) u = u) :
    ((L.label β : Finset (Fin m))).image (φ g) = L.label β := by
  have hβ : blockHom G B hB g β = β := by
    apply Subtype.ext
    rw [blockHom_apply_coe]
    by_contra hne
    have hd := hs.pairwiseDisjoint _ (hB g g.2 β β.2) β β.2 hne
    exact Set.disjoint_left.1 hd ⟨u, hu, hg⟩ hu
  have h := congrArg (fun p : Perm (binom (Fin m) t) => p (L.label β)) (L.action g)
  simp only [Equiv.permCongrHom, MulEquiv.coe_mk, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, hβ] at h
  have h2 := congrArg (fun s : binom (Fin m) t => (s : Finset (Fin m))) h
  simp only [tAction_apply_coe] at h2
  exact h2.symm

/-- **Sec. 15, lines 3–4.** If `Ω = Φ` (the map `u ↦ T(u)` is injective), then `T(u)` is the
label of the block of the hint that contains `u`. -/
theorem Tpoint_eq_label (L : MasterHintBlockLink (t := t) hB φ)
    (hs : IsInvariantPartitionOn G Set.univ B) (ht : 1 ≤ t) (h2t : 2 * t ≤ m)
    (hϕ : IsGiantRep φ) (hk : VeryLargeK m (maxOrbitLength G))
    (hinj : Function.Injective (Tpoint φ)) {u : Ω} {β : B} (hu : u ∈ (β : Set Ω)) :
    Tpoint φ u = ((L.label β : Finset (Fin m)) : Set (Fin m)) := by
  set U := Tpoint φ u with hUdef
  set S : Finset (Fin m) := (L.label β : Finset (Fin m)) with hSdef
  have hScard : S.card = t := (L.label β).2
  have hm9 : 9 ≤ m := by
    have : (9 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have h4 : 4 * U.ncard < m := by
    have := (theorem_10_5_1_a φ hϕ hk u).1.1
    simpa [hUdef] using this
  have hUc : U.ncard = U.toFinset.card := Set.ncard_eq_toFinset_card' U
  -- the key step: an even permutation that fixes `U` setwise fixes `S`
  have key : ∀ π ∈ alternatingGroup (Fin m), π '' U = U → S.image π = S := by
    intro π hπ hπU
    obtain ⟨g, hg⟩ := hϕ hπ
    have hgu : (g : Perm Ω) u = u := by
      apply hinj
      have h54 := theorem_10_5_1_c_eq54 φ hϕ hk u g
      rw [Subgroup.smul_def, Perm.smul_def] at h54
      rw [h54, hg, hπU]
    have := L.label_fixed hs hu hgu
    rwa [hg] at this
  have hsign : ∀ a b c d : Fin m, a ≠ b → c ≠ d →
      swap a b * swap c d ∈ alternatingGroup (Fin m) := by
    intro a b c d hab hcd
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    decide
  -- `S ⊆ U`
  have hSU : ∀ a ∈ S, a ∈ U := by
    intro a haS
    by_contra haU
    set D : Finset (Fin m) := Finset.univ \ (U.toFinset ∪ S ∪ {a}) with hD
    have hDcard : 2 ≤ D.card := by
      have h1 : (U.toFinset ∪ S ∪ {a}).card ≤ U.toFinset.card + t + 1 := by
        calc (U.toFinset ∪ S ∪ {a}).card ≤ (U.toFinset ∪ S).card + ({a} : Finset _).card :=
              Finset.card_union_le _ _
          _ ≤ U.toFinset.card + S.card + 1 := by
              have := Finset.card_union_le U.toFinset S
              simp only [Finset.card_singleton]; omega
          _ = U.toFinset.card + t + 1 := by rw [hScard]
      have h2 : D.card = m - (U.toFinset ∪ S ∪ {a}).card := by
        rw [hD, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
      omega
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 hDcard
    simp only [hD, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Set.mem_toFinset,
      Finset.mem_singleton, true_and, not_or] at hb hc
    have hab : a ≠ b := fun h => hb.2 h.symm
    have hac : a ≠ c := fun h => hc.2 h.symm
    set π := swap a b * swap b c with hπ
    have hπfix : ∀ x ∈ U, π x = x := by
      intro x hx
      have hxa : x ≠ a := fun h => haU (h ▸ hx)
      have hxb : x ≠ b := fun h => hb.1.1 (h ▸ hx)
      have hxc : x ≠ c := fun h => hc.1.1 (h ▸ hx)
      simp only [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc,
        swap_apply_of_ne_of_ne hxa hxb]
    have hπU : π '' U = U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; rw [hπfix y hy]; exact hy
      · intro hx; exact ⟨x, hx, hπfix x hx⟩
    have hS := key π (hsign a b b c hab hbc) hπU
    have hπa : π a = b := by
      simp only [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]
    have : b ∈ S := by
      rw [← hS]; exact Finset.mem_image.2 ⟨a, haS, hπa⟩
    exact hb.1.2 this
  -- `U ⊆ S`
  have hUS : ∀ a ∈ U, a ∈ S := by
    intro a haU
    by_contra haS
    obtain ⟨s, hs'⟩ : S.Nonempty := by
      rw [← Finset.card_pos, hScard]; omega
    have hsU := hSU s hs'
    have hsa : s ≠ a := fun h => haS (h ▸ hs')
    set D : Finset (Fin m) := Finset.univ \ U.toFinset with hD
    have hDcard : 2 ≤ D.card := by
      have h2 : D.card = m - U.toFinset.card := by
        rw [hD, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 hDcard
    simp only [hD, Finset.mem_sdiff, Finset.mem_univ, Set.mem_toFinset, true_and] at hc hd
    set π := swap s a * swap c d with hπ
    have hπmap : ∀ x ∈ U, π x ∈ U := by
      intro x hx
      have hxc : x ≠ c := fun h => hc (h ▸ hx)
      have hxd : x ≠ d := fun h => hd (h ▸ hx)
      simp only [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd]
      rcases eq_or_ne x s with rfl | hxs
      · rw [swap_apply_left]; exact haU
      rcases eq_or_ne x a with rfl | hxa
      · rw [swap_apply_right]; exact hsU
      rw [swap_apply_of_ne_of_ne hxs hxa]; exact hx
    have hπU : π '' U = U := by
      apply Set.eq_of_subset_of_ncard_le
      · rintro _ ⟨y, hy, rfl⟩; exact hπmap y hy
      · rw [Set.ncard_image_of_injective _ π.injective]
      · exact Set.toFinite _
    have hS := key π (hsign s a c d hsa hcd) hπU
    have hsc : s ≠ c := fun h => hc (h ▸ hsU)
    have hsd : s ≠ d := fun h => hd (h ▸ hsU)
    have hπs : π s = a := by
      simp only [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hsc hsd, swap_apply_left]
    have : a ∈ S := by
      rw [← hS]; exact Finset.mem_image.2 ⟨s, hs', hπs⟩
    exact haS this
  ext a
  exact ⟨fun h => Finset.mem_coe.2 (hUS a h), fun h => hSU a (Finset.mem_coe.1 h)⟩

/-- **Sec. 15, lines 3–4.** If `Ω = Φ`, every label `T(u)` has the Johnson parameter `t` of the
hint as its size. -/
theorem tPoint_eq (L : MasterHintBlockLink (t := t) hB φ)
    (hs : IsInvariantPartitionOn G Set.univ B) (ht : 1 ≤ t) (h2t : 2 * t ≤ m)
    (hϕ : IsGiantRep φ) (hk : VeryLargeK m (maxOrbitLength G))
    (hinj : Function.Injective (Tpoint φ)) (u : Ω) : tPoint φ u = t := by
  have hu : u ∈ ⋃₀ B := by rw [hs.covers]; exact Set.mem_univ u
  obtain ⟨β, hβ, hu⟩ := Set.mem_sUnion.1 hu
  rw [tPoint, L.Tpoint_eq_label hs ht h2t hϕ hk hinj (β := ⟨β, hβ⟩) hu, Set.ncard_coe_finset]
  exact (L.label ⟨β, hβ⟩).2

end MasterHintBlockLink

omit [Fintype Ω] [DecidableEq Ω] in
/-- For a transitive group, `u ↦ T(u)` is injective exactly when every standard block of
Theorem 10.5.1 (e) is a singleton, i.e. `Ω = Φ`. -/
theorem injective_Tpoint_iff_standardBlock_singleton (hG : IsTransitive G) :
    Function.Injective (Tpoint φ) ↔ ∀ u : Ω, standardBlock φ u = {u} := by
  have horb : ∀ x y : Ω, y ∈ orbit G x := by
    obtain ⟨x₀, hx₀⟩ := hG
    intro x y
    have hx : x ∈ orbit G x₀ := hx₀ ▸ Set.mem_univ x
    have hy : y ∈ orbit G x₀ := hx₀ ▸ Set.mem_univ y
    rw [orbit_eq_iff.2 hx]; exact hy
  constructor
  · intro hinj u
    ext v
    simp only [standardBlock, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => hinj h.2, fun h => h ▸ ⟨horb _ _, rfl⟩⟩
  · intro hsing u v huv
    have : v ∈ standardBlock φ u := ⟨horb u v, huv.symm⟩
    rw [hsing u] at this
    exact this.symm

/-- **Sec. 15, line 4**: *"if `G` primitive (: i.e. `Ω = Φ` :)"*. For a hint whose giant
representation is its block action (`Algo.MasterHintLinked`), and under the hypothesis of
Theorem 10.5.1 that defines `Φ`, the Master's test `Babai.IsPrimitiveCase` holds exactly when
every standard block is a singleton. -/
theorem isPrimitiveCase_iff_standardBlock_singleton {A : Type*} {i : HintedInstance Ω A}
    (hJ : IsJohnson i) (hL : MasterHintLinked (johnsonData hJ))
    (hk : VeryLargeK (johnsonData hJ).m (maxOrbitLength (johnsonData hJ).windowGroup)) :
    IsPrimitiveCase i ↔
      ∀ u : i.inst.Δ, standardBlock (johnsonData hJ).ϕ u = {u} := by
  set d := johnsonData hJ
  have hG : IsTransitive d.windowGroup := d.transitive
  have hne : Nonempty i.inst.Δ := by obtain ⟨x, -⟩ := hG; exact ⟨x⟩
  refine Iff.trans ?_ (injective_Tpoint_iff_standardBlock_singleton (φ := d.ϕ) hG)
  constructor
  · rintro ⟨h, hn⟩
    exact ((nonempty_primitiveCaseId_iff d.ϕ hne d.giant hk).1 hn).1
  · intro hinj
    obtain ⟨L⟩ := hL
    refine ⟨hJ, (nonempty_primitiveCaseId_iff d.ϕ hne d.giant hk).2 ⟨hinj, fun u => ?_⟩⟩
    exact L.tPoint_eq d.system.isInvariantPartitionOn d.johnson.t_pos d.johnson.two_mul_t_le
      d.giant hk hinj u

end Algo

#print axioms Algo.isPrimitiveCase_iff_standardBlock_singleton
