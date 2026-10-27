/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Combinatorics of the cliques of a Johnson graph, used for Proposition 3.2.11.
-/
import Workspace.Prelim.PermGroups

/-!
# Cliques of the Johnson graph (§3.2.2)

Proposition 3.2.11 says that every automorphism of the Johnson graph `J(Γ,t)` comes from
a permutation of `Γ`.  The paper leaves the route open ("can be derived for instance from
the Erdős–Ko–Rado theorem").  We take the classical route through cliques, which needs no
extremal set theory.

Fix `t ≥ 0` and work with the `(t+1)`-subsets of `Γ`, which are the vertices of
`J(Γ,t+1)`.  Two kinds of cliques matter.

* The *star* of a `t`-set `A` is the set of `(t+1)`-sets containing `A`.  It has
  `|Γ| - t` elements.
* The *top* of a `(t+2)`-set `B` is the set of `(t+1)`-sets contained in `B`.  It has at
  most `t + 2` elements.

The main lemma here (`Babai.Johnson.clique_star_or_top`) says that a clique with two
distinct vertices lies inside a star or inside a top.  When `|Γ| ≥ 2t + 3` a star is
larger than a top, so an automorphism must carry stars to stars.  That step and the
induction on `t` are in `Workspace/Coherent/Classes.lean`.

This file is pure finite-set combinatorics: it speaks of `t`-subsets of `Γ` and of the
cardinality `|S \ T|`, which is the distance of the Johnson graph (Obs. 3.2.10), and it
never mentions the graph itself.
-/

namespace Babai

namespace Johnson

variable {Γ : Type*} [DecidableEq Γ]

/-! ### Two `(t+1)`-sets at distance one -/

/-- If `|S| = |T| = t + 1` and `|S \ T| = 1` then `|S ∩ T| = t`. -/
theorem card_inter_of_card_sdiff_eq_one {t : ℕ} {S T : Finset Γ} (hS : S.card = t + 1)
    (h : (S \ T).card = 1) : (S ∩ T).card = t := by
  have := Finset.card_inter_add_card_sdiff S T
  omega

/-- If `|S| = |T| = t + 1` and `|S \ T| = 1` then `|T \ S| = 1`: both differences have the
same size. -/
theorem card_sdiff_comm {t : ℕ} {S T : Finset Γ} (hS : S.card = t + 1)
    (hT : T.card = t + 1) (h : (S \ T).card = 1) : (T \ S).card = 1 := by
  have h1 := Finset.card_inter_add_card_sdiff S T
  have h2 := Finset.card_inter_add_card_sdiff T S
  rw [Finset.inter_comm] at h2
  omega

/-- If `|S| = |T| = t + 1` and `|S \ T| = 1` then `|S ∪ T| = t + 2`. -/
theorem card_union_of_card_sdiff_eq_one {t : ℕ} {S T : Finset Γ} (hS : S.card = t + 1)
    (hT : T.card = t + 1) (h : (S \ T).card = 1) : (S ∪ T).card = t + 2 := by
  have h1 := Finset.card_inter_add_card_sdiff S T
  have h2 := Finset.card_union_add_card_inter S T
  omega

/-- Two `t`-sets are at Johnson distance one exactly when they are distinct and lie in a
common `(t+1)`-set.  This is what lets an automorphism of `J(Γ,t+1)` act on the stars as
an automorphism of `J(Γ,t)`. -/
theorem card_sdiff_eq_one_iff {t : ℕ} {A B : Finset Γ} (hA : A.card = t) (hB : B.card = t) :
    (A \ B).card = 1 ↔ A ≠ B ∧ ∃ S : Finset Γ, S.card = t + 1 ∧ A ⊆ S ∧ B ⊆ S := by
  have h1 := Finset.card_inter_add_card_sdiff A B
  have h2 := Finset.card_union_add_card_inter A B
  constructor
  · intro h
    refine ⟨fun hAB => by rw [hAB] at h; simp at h, A ∪ B, by omega,
      Finset.subset_union_left, Finset.subset_union_right⟩
  · rintro ⟨hne, S, hScard, hAS, hBS⟩
    have hle : (A ∪ B).card ≤ S.card := Finset.card_le_card (Finset.union_subset hAS hBS)
    have hpos : (A \ B).card ≠ 0 := by
      intro h0
      exact hne (Finset.eq_of_subset_of_card_le
        (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 h0)) (by omega))
    omega

/-- A `t`-set is determined by the `(t+1)`-sets that contain it, as soon as `Γ` has at
least `t + 2` points. -/
theorem eq_of_forall_supset {t : ℕ} [Fintype Γ] {A B : Finset Γ} (hA : A.card = t)
    (hB : B.card = t) (hk : t + 2 ≤ Fintype.card Γ)
    (h : ∀ S : Finset Γ, S.card = t + 1 → A ⊆ S → B ⊆ S) : B = A := by
  classical
  -- two points outside `A`
  have hcompl : 2 ≤ (Aᶜ : Finset Γ).card := by
    rw [Finset.card_compl, hA]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (Aᶜ : Finset Γ).card)
  rw [Finset.mem_compl] at hx hy
  have hcard : ∀ z : Γ, z ∉ A → (insert z A).card = t + 1 := by
    intro z hz; rw [Finset.card_insert_of_notMem hz, hA]
  have h1 := h _ (hcard x hx) (Finset.subset_insert _ _)
  have h2 := h _ (hcard y hy) (Finset.subset_insert _ _)
  have hBA : B ⊆ A := by
    intro b hb
    rcases Finset.mem_insert.1 (h1 hb) with rfl | hbA
    · rcases Finset.mem_insert.1 (h2 hb) with rfl | hbA
      · exact absurd rfl hxy
      · exact hbA
    · exact hbA
  exact Finset.eq_of_subset_of_card_le hBA (by omega)

/-- The triangle inequality for `|A \ C|`, the distance of the Johnson graph
(Obs. 3.2.10). -/
theorem card_sdiff_le_add (A B C : Finset Γ) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  obtain ⟨hxA, hxC⟩ := Finset.mem_sdiff.1 hx
  by_cases hxB : x ∈ B
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hxB, hxC⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hxA, hxB⟩)

/-! ### Stars -/

variable [Fintype Γ]

/-- The *star* of the `t`-set `A`: the vertices of `J(Γ,t+1)` containing `A`. -/
def star (t : ℕ) (A : Finset Γ) : Finset (binom Γ (t + 1)) :=
  Finset.univ.filter fun S => A ⊆ (S : Finset Γ)

@[simp] theorem mem_star {t : ℕ} {A : Finset Γ} {S : binom Γ (t + 1)} :
    S ∈ star t A ↔ A ⊆ (S : Finset Γ) := by
  simp [star]

/-- A star has `|Γ| - t` vertices: its members are the sets `A ∪ {x}` for `x ∉ A`. -/
theorem card_star {t : ℕ} {A : Finset Γ} (hA : A.card = t) :
    (star t A).card = Fintype.card Γ - t := by
  classical
  have hins : ∀ x : Γ, x ∈ (Aᶜ : Finset Γ) → (insert x A).card = t + 1 := by
    intro x hx
    rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 hx), hA]
  have hbij : (Aᶜ : Finset Γ).card = (star t A).card := by
    refine Finset.card_bij (fun x hx => (⟨insert x A, hins x hx⟩ : binom Γ (t + 1)))
      ?_ ?_ ?_
    · intro x hx
      exact mem_star.2 (Finset.subset_insert _ _)
    · intro x hx y hy hxy
      have : insert x A = insert y A := congrArg Subtype.val hxy
      have hxm : x ∈ insert y A := this ▸ Finset.mem_insert_self x A
      rcases Finset.mem_insert.1 hxm with h | h
      · exact h
      · exact absurd h (Finset.mem_compl.1 hx)
    · intro S hS
      have hAS : A ⊆ (S : Finset Γ) := mem_star.1 hS
      have hne : A ≠ (S : Finset Γ) := by
        intro he
        have := S.2
        rw [← he, hA] at this
        omega
      obtain ⟨x, hxS, hxA⟩ :=
        Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hAS, hne⟩)
      have hxc : x ∈ (Aᶜ : Finset Γ) := Finset.mem_compl.2 hxA
      refine ⟨x, hxc, Subtype.ext ?_⟩
      exact Finset.eq_of_subset_of_card_le (Finset.insert_subset hxS hAS)
        (le_of_eq (by rw [S.2, hins x hxc]))
  rw [← hbij, Finset.card_compl, hA]

/-- A star is a clique: two distinct `(t+1)`-sets containing the same `t`-set are at
distance one. -/
theorem star_clique {t : ℕ} {A U V : Finset Γ} (hA : A.card = t) (hU : U.card = t + 1)
    (hV : V.card = t + 1) (hAU : A ⊆ U) (hAV : A ⊆ V) (hUV : U ≠ V) : (U \ V).card = 1 := by
  have h1 := Finset.card_inter_add_card_sdiff U V
  have h2 : A ⊆ U ∩ V := Finset.subset_inter hAU hAV
  have h3 : A.card ≤ (U ∩ V).card := Finset.card_le_card h2
  have h4 : (U ∩ V).card ≤ U.card := Finset.card_le_card Finset.inter_subset_left
  have h5 : (U \ V).card ≠ 0 := by
    intro h0
    exact hUV (Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 h0)) (by omega))
  have h6 : (U ∩ V).card ≠ t + 1 := by
    intro h
    have : U ∩ V = U := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hUVsub : U ⊆ V := by
      intro x hx
      have : x ∈ U ∩ V := by rw [this]; exact hx
      exact (Finset.mem_inter.1 this).2
    exact hUV (Finset.eq_of_subset_of_card_le hUVsub (by omega))
  omega

/-! ### The main clique lemma -/

/-- The key step: if the `(t+1)`-set `U` is at distance one from both `S` and `T`, and `U`
does not contain `S ∩ T`, then `U` lies inside `S ∪ T`, and `U` meets `S ∩ T` in `t - 1`
points (stated without subtraction). -/
theorem subset_union_of_not_subset {t : ℕ} {S T U : Finset Γ} (hS : S.card = t + 1)
    (hT : T.card = t + 1) (hU : U.card = t + 1) (hST : (S \ T).card = 1)
    (hUS : (U \ S).card = 1) (hUT : (U \ T).card = 1) (hnot : ¬ S ∩ T ⊆ U) :
    U ⊆ S ∪ T ∧ (U ∩ (S ∩ T)).card + 1 = t := by
  classical
  set A := S ∩ T with hA
  have hAcard : A.card = t := card_inter_of_card_sdiff_eq_one hS hST
  have hTS : (T \ S).card = 1 := card_sdiff_comm hS hT hST
  obtain ⟨s, hs⟩ := Finset.card_eq_one.1 hST
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hTS
  have hsS : s ∈ S := (Finset.mem_sdiff.1 (hs ▸ Finset.mem_singleton_self s)).1
  have hsT : s ∉ T := (Finset.mem_sdiff.1 (hs ▸ Finset.mem_singleton_self s)).2
  have huT : u ∈ T := (Finset.mem_sdiff.1 (hu ▸ Finset.mem_singleton_self u)).1
  have huS : u ∉ S := (Finset.mem_sdiff.1 (hu ▸ Finset.mem_singleton_self u)).2
  have hsu : s ≠ u := fun h => huS (h ▸ hsS)
  have hsA : s ∉ A := fun h => hsT (Finset.mem_inter.1 h).2
  have huA : u ∉ A := fun h => huS (Finset.mem_inter.1 h).1
  -- `S = A ∪ {s}`
  have hSA : S ⊆ insert s A := by
    intro z hz
    by_cases hzT : z ∈ T
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hz, hzT⟩)
    · have : z ∈ S \ T := Finset.mem_sdiff.2 ⟨hz, hzT⟩
      rw [hs, Finset.mem_singleton] at this
      exact this ▸ Finset.mem_insert_self _ _
  have hTA : T ⊆ insert u A := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hzS, hz⟩)
    · have : z ∈ T \ S := Finset.mem_sdiff.2 ⟨hz, hzS⟩
      rw [hu, Finset.mem_singleton] at this
      exact this ▸ Finset.mem_insert_self _ _
  -- `|U ∩ S| = t` and `|U ∩ T| = t`
  have hUScard : (U ∩ S).card = t := card_inter_of_card_sdiff_eq_one hU hUS
  have hUTcard : (U ∩ T).card = t := card_inter_of_card_sdiff_eq_one hU hUT
  -- `U ∩ S ⊆ (U ∩ A) ∪ {s}`
  have hsub1 : U ∩ S ⊆ insert s (U ∩ A) := by
    intro z hz
    obtain ⟨hzU, hzS⟩ := Finset.mem_inter.1 hz
    rcases Finset.mem_insert.1 (hSA hzS) with rfl | hzA
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hzU, hzA⟩)
  have hsub2 : U ∩ T ⊆ insert u (U ∩ A) := by
    intro z hz
    obtain ⟨hzU, hzT⟩ := Finset.mem_inter.1 hz
    rcases Finset.mem_insert.1 (hTA hzT) with rfl | hzA
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hzU, hzA⟩)
  have hcard1 : t ≤ (U ∩ A).card + 1 := by
    have := Finset.card_le_card hsub1
    have h2 := Finset.card_insert_le s (U ∩ A)
    omega
  -- `U ∩ A` is a proper subset of `A`
  have hUAsub : U ∩ A ⊆ A := Finset.inter_subset_right
  have hUAne : U ∩ A ≠ A := by
    intro he
    refine hnot fun z hz => ?_
    have hz' : z ∈ U ∩ A := by rw [he]; exact hz
    exact (Finset.mem_inter.1 hz').1
  have hUAlt : (U ∩ A).card < t := by
    rcases lt_or_eq_of_le (Finset.card_le_card hUAsub) with h | h
    · omega
    · exact absurd (Finset.eq_of_subset_of_card_le hUAsub (by omega)) hUAne
  have hUAcard : (U ∩ A).card + 1 = t := by omega
  -- `s ∈ U` and `u ∈ U`
  have hsU : s ∈ U := by
    by_contra hsU
    have : U ∩ S ⊆ U ∩ A := by
      intro z hz
      rcases Finset.mem_insert.1 (hsub1 hz) with rfl | h
      · exact absurd (Finset.mem_inter.1 hz).1 hsU
      · exact h
    have := Finset.card_le_card this
    omega
  have huU : u ∈ U := by
    by_contra huU
    have : U ∩ T ⊆ U ∩ A := by
      intro z hz
      rcases Finset.mem_insert.1 (hsub2 hz) with rfl | h
      · exact absurd (Finset.mem_inter.1 hz).1 huU
      · exact h
    have := Finset.card_le_card this
    omega
  refine ⟨?_, hUAcard⟩
  -- `U ⊆ S ∪ T`, by counting: `(U ∩ A) ∪ {s,u} ⊆ U ∩ (S ∪ T)` already has `t+1` elements
  have hbig : insert s (insert u (U ∩ A)) ⊆ U ∩ (S ∪ T) := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_inter.2 ⟨hsU, Finset.mem_union_left _ hsS⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_inter.2 ⟨huU, Finset.mem_union_right _ huT⟩
    · obtain ⟨hzU, hzA⟩ := Finset.mem_inter.1 hz
      exact Finset.mem_inter.2 ⟨hzU, Finset.mem_union_left _ (Finset.mem_inter.1 hzA).1⟩
  have hbigcard : (insert s (insert u (U ∩ A))).card = t + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · omega
    · exact fun h => huA (Finset.mem_inter.1 h).2
    · simp only [Finset.mem_insert, not_or]
      exact ⟨hsu, fun h => hsA (Finset.mem_inter.1 h).2⟩
  have hUeq : U ∩ (S ∪ T) = U := by
    refine Finset.eq_of_subset_of_card_le Finset.inter_subset_left ?_
    have := Finset.card_le_card hbig
    omega
  intro z hz
  have hz' : z ∈ U ∩ (S ∪ T) := by rw [hUeq]; exact hz
  exact (Finset.mem_inter.1 hz').2

/-- A clique of `J(Γ,t+1)` with two distinct vertices `S` and `T` lies inside the star of
`S ∩ T` or inside the top of `S ∪ T`.  This is the combinatorial heart of
Prop. 3.2.11. -/
theorem clique_star_or_top {t : ℕ} (C : Finset (binom Γ (t + 1)))
    (hC : ∀ S ∈ C, ∀ T ∈ C, S ≠ T → ((S : Finset Γ) \ (T : Finset Γ)).card = 1)
    {S T : binom Γ (t + 1)} (hS : S ∈ C) (hT : T ∈ C) (hST : S ≠ T) :
    (∀ U ∈ C, (S : Finset Γ) ∩ (T : Finset Γ) ⊆ (U : Finset Γ)) ∨
      (∀ U ∈ C, (U : Finset Γ) ⊆ (S : Finset Γ) ∪ (T : Finset Γ)) := by
  classical
  by_cases hstar : ∀ U ∈ C, (S : Finset Γ) ∩ (T : Finset Γ) ⊆ (U : Finset Γ)
  · exact Or.inl hstar
  right
  push_neg at hstar
  obtain ⟨U₀, hU₀C, hU₀⟩ := hstar
  have hSTcard := hC S hS T hT hST
  -- the vertex `U₀` avoiding `S ∩ T` lies in `S ∪ T` and meets `S ∩ T` in `t - 1` points
  have hne : ∀ U ∈ C, U ≠ S → U ≠ T →
      ((U : Finset Γ) \ (S : Finset Γ)).card = 1 ∧
      ((U : Finset Γ) \ (T : Finset Γ)).card = 1 :=
    fun U hU hUS hUT => ⟨hC U hU S hS hUS, hC U hU T hT hUT⟩
  have hU₀S : U₀ ≠ S := by
    rintro rfl
    exact hU₀ Finset.inter_subset_left
  have hU₀T : U₀ ≠ T := by
    rintro rfl
    exact hU₀ Finset.inter_subset_right
  obtain ⟨hU₀1, hU₀2⟩ := hne U₀ hU₀C hU₀S hU₀T
  obtain ⟨hU₀sub, hU₀count⟩ :=
    subset_union_of_not_subset S.2 T.2 U₀.2 hSTcard hU₀1 hU₀2 hU₀
  intro V hV
  by_cases hVS : V = S
  · exact hVS ▸ Finset.subset_union_left
  by_cases hVT : V = T
  · exact hVT ▸ Finset.subset_union_right
  obtain ⟨hV1, hV2⟩ := hne V hV hVS hVT
  by_cases hVA : ¬ (S : Finset Γ) ∩ (T : Finset Γ) ⊆ (V : Finset Γ)
  · exact (subset_union_of_not_subset S.2 T.2 V.2 hSTcard hV1 hV2 hVA).1
  push_neg at hVA
  by_cases hsub : (V : Finset Γ) ⊆ (S : Finset Γ) ∪ (T : Finset Γ)
  · exact hsub
  · -- the remaining case is impossible: `V = (S ∩ T) ∪ {v}` with `v ∉ S ∪ T`, and then
    -- `V` would meet `U₀` in too few points
    exfalso
    obtain ⟨v, hvV, hv⟩ : ∃ v ∈ (V : Finset Γ), v ∉ (S : Finset Γ) ∪ (T : Finset Γ) := by
      by_contra hcon
      push_neg at hcon
      exact hsub hcon
    have hAcard : ((S : Finset Γ) ∩ (T : Finset Γ)).card = t :=
      card_inter_of_card_sdiff_eq_one S.2 hSTcard
    have hvA : v ∉ (S : Finset Γ) ∩ (T : Finset Γ) := fun h =>
      hv (Finset.mem_union_left _ (Finset.mem_inter.1 h).1)
    have hVeq : (V : Finset Γ) = insert v ((S : Finset Γ) ∩ (T : Finset Γ)) := by
      refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hvV hVA) ?_).symm
      rw [Finset.card_insert_of_notMem hvA, hAcard, V.2]
    have hvU₀ : v ∉ (U₀ : Finset Γ) := fun h => hv (hU₀sub h)
    have hinter : (V : Finset Γ) ∩ (U₀ : Finset Γ)
        = ((S : Finset Γ) ∩ (T : Finset Γ)) ∩ (U₀ : Finset Γ) := by
      rw [hVeq, Finset.insert_inter_of_notMem hvU₀]
    have hVU₀ : V ≠ U₀ := by
      rintro rfl
      exact hU₀ hVA
    have hVU₀card : ((V : Finset Γ) ∩ (U₀ : Finset Γ)).card = t :=
      card_inter_of_card_sdiff_eq_one V.2 (hC V hV U₀ hU₀C hVU₀)
    rw [hinter, Finset.inter_comm] at hVU₀card
    omega

/-! ### Tops -/

/-- A family of `(t+1)`-sets inside a fixed `(t+2)`-set has at most `t + 2` members. -/
theorem card_le_of_subset_top {t : ℕ} {C : Finset (binom Γ (t + 1))} {B : Finset Γ}
    (hB : B.card = t + 2) (h : ∀ U ∈ C, (U : Finset Γ) ⊆ B) : C.card ≤ t + 2 := by
  classical
  set f : binom Γ (t + 1) → Finset Γ := fun U => B \ (U : Finset Γ) with hf
  have hsub : ∀ U ∈ C, ∀ x, x ∈ (U : Finset Γ) → x ∈ B := fun U hU x hx => h U hU hx
  have hinj : ∀ U ∈ C, ∀ V ∈ C, f U = f V → U = V := by
    intro U hU V hV hUV
    have hUV : B \ (U : Finset Γ) = B \ (V : Finset Γ) := hUV
    refine Subtype.ext (Finset.ext fun x => ?_)
    constructor
    · intro hx
      by_contra hxV
      have : x ∈ B \ (V : Finset Γ) := Finset.mem_sdiff.2 ⟨hsub U hU x hx, hxV⟩
      rw [← hUV] at this
      exact (Finset.mem_sdiff.1 this).2 hx
    · intro hx
      by_contra hxU
      have : x ∈ B \ (U : Finset Γ) := Finset.mem_sdiff.2 ⟨hsub V hV x hx, hxU⟩
      rw [hUV] at this
      exact (Finset.mem_sdiff.1 this).2 hx
  have hmem : ∀ U ∈ C, f U ∈ B.powersetCard 1 := by
    intro U hU
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset, ?_⟩
    have hUB : (U : Finset Γ) ∩ B = (U : Finset Γ) := Finset.inter_eq_left.2 (h U hU)
    show (B \ (U : Finset Γ)).card = 1
    rw [Finset.card_sdiff, hUB, U.2, hB]
    omega
  have hcard : C.card ≤ (B.powersetCard 1).card :=
    Finset.card_le_card_of_injOn f hmem (fun U hU V hV hUV => hinj U hU V hV hUV)
  rwa [Finset.card_powersetCard, hB, Nat.choose_one_right] at hcard

/-! ### The base case: `t = 1` -/

/-- The vertices of `J(Γ,1)` are the points of `Γ`. -/
noncomputable def oneEquiv (Γ : Type*) [DecidableEq Γ] : Γ ≃ binom Γ 1 :=
  Equiv.ofBijective (fun x => ⟨{x}, Finset.card_singleton x⟩)
    ⟨fun x y h => Finset.singleton_injective (congrArg Subtype.val h), fun S => by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 S.2
      exact ⟨x, Subtype.ext hx.symm⟩⟩

@[simp] theorem oneEquiv_apply (x : Γ) : ((oneEquiv Γ x : binom Γ 1) : Finset Γ) = {x} := rfl

end Johnson

end Babai
