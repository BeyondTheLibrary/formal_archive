/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The primitive group of diagonal type, used in the proof of Theorem 10.2.4.
-/
import Workspace.AltQuotients.ONanScottConstr
import Workspace.AltQuotients.ONanScottPi

/-!
# The primitive group of diagonal type

For a nonabelian simple group `T` and `k ≥ 2`, the group `T^k ⋊ S_k` acts on the cosets of
the diagonal `D = {(t, …, t)}` in `T^k`.  This is the group `W` of [DiM, Lemma 4.5A] with
the outer automorphisms left out; by [DiM, Thm. 4.5A] it is primitive with socle `T^k`,
of degree `|T|^{k-1}`.  It is `Babai.ONS.exists_diag_primitive`.

The proof of primitivity: a subgroup `S` of `T^k` with `D ≤ S` that is invariant under the
coordinate permutations is `D` or `T^k`.  If `S ≠ D`, take `y ∈ S` with a trivial coordinate,
`y ≠ 1`, of least support; a commutator with a conjugate of a coordinate-permuted copy of
`y` has smaller support unless the support is one point, and then `S` contains a coordinate
subgroup, hence all of them.
-/

namespace Babai

namespace ONS

open Subgroup

section Diag

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Group R]

/-- Permuting the coordinates of `R^ι`. -/
def permAut : Equiv.Perm ι →* MulAut (ι → R) where
  toFun τ :=
    { toFun := fun f j => f (τ.symm j)
      invFun := fun f j => f (τ j)
      left_inv := fun f => by funext j; simp
      right_inv := fun f => by funext j; simp
      map_mul' := fun f g => by funext j; simp }
  map_one' := by ext f j; simp
  map_mul' τ υ := by ext f j; rfl

omit [DecidableEq ι] in
theorem permAut_apply (τ : Equiv.Perm ι) (f : ι → R) (j : ι) :
    permAut τ f j = f (τ.symm j) := rfl

/-- The diagonal subgroup of `R^ι`. -/
def diag : Subgroup (ι → R) := (Pi.constMonoidHom ι R).range

omit [DecidableEq ι] in
theorem const_mem_diag (r : R) : (fun _ : ι => r) ∈ diag (ι := ι) := ⟨r, rfl⟩

omit [DecidableEq ι] in
theorem mem_diag_iff [Nonempty ι] {f : ι → R} : f ∈ diag ↔ ∀ i j, f i = f j := by
  constructor
  · rintro ⟨r, rfl⟩ i j; rfl
  · intro h
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact ⟨f i₀, funext fun j => h i₀ j⟩

omit [DecidableEq ι] in
theorem diag_inv (τ : Equiv.Perm ι) (x : ι → R) (hx : x ∈ diag) : permAut τ x ∈ diag := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

theorem permAut_swap_mulSingle (a j : ι) (r : R) :
    permAut (Equiv.swap a j) (Pi.mulSingle a r) = Pi.mulSingle j r := by
  funext l
  rw [permAut_apply, Equiv.symm_swap]
  by_cases hl : l = j
  · subst hl; rw [Equiv.swap_apply_right]; simp
  · rw [Pi.mulSingle_eq_of_ne hl]
    have hne : Equiv.swap a j l ≠ a := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact hl h
    rw [Pi.mulSingle_eq_of_ne hne]

theorem coord_le_of_permAut [Fintype ι] {S : Subgroup (ι → R)}
    (hS : ∀ τ : Equiv.Perm ι, ∀ y ∈ S, permAut τ y ∈ S) {a : ι} (ha : coord a ≤ S) :
    S = ⊤ := by
  apply eq_top_of_coord_le
  intro j
  rintro _ ⟨r, rfl⟩
  have := hS (Equiv.swap a j) _ (ha (mulSingle_mem_coord a r))
  rw [permAut_swap_mulSingle] at this
  exact this

variable [IsSimpleGroup R] (hR : ¬ ∀ a b : R, a * b = b * a)

/-- The support of `y`. -/
noncomputable def supp [Fintype ι] (y : ι → R) : Finset ι := by
  classical exact Finset.univ.filter fun i => y i ≠ 1

omit [DecidableEq ι] [IsSimpleGroup R] in
theorem mem_supp [Fintype ι] {y : ι → R} {i : ι} : i ∈ supp y ↔ y i ≠ 1 := by
  classical
  simp [supp]

include hR in
/-- **[DiM, Thm. 4.5A]**, the key step: an overgroup of the diagonal in `R^ι`, invariant
under the coordinate permutations, is the diagonal or `R^ι`. -/
theorem diag_max [Fintype ι] (S : Subgroup (ι → R)) (hdS : diag ≤ S)
    (hS : ∀ τ : Equiv.Perm ι, ∀ y ∈ S, permAut τ y ∈ S) : S = diag ∨ S = ⊤ := by
  by_cases hSd : S ≤ diag
  · exact Or.inl (le_antisymm hSd hdS)
  right
  have hconst : ∀ t : R, ∀ y ∈ S, (fun _ => t) * y * (fun _ => t⁻¹) ∈ S := fun t y hy =>
    mul_mem (mul_mem (hdS (const_mem_diag t)) hy) (hdS (const_mem_diag t⁻¹))
  -- the descent on the support
  have key : ∀ m : ℕ, ∀ y ∈ S, y ≠ 1 → (∃ b, y b = 1) → (supp y).card ≤ m → S = ⊤ := by
    intro m
    induction m with
    | zero =>
      intro y _ hy1 _ hcard
      exfalso
      apply hy1
      funext i
      by_contra hi
      have : i ∈ supp y := mem_supp.2 hi
      have := Finset.card_pos.2 ⟨i, this⟩
      omega
    | succ m ih =>
      intro y hyS hy1 ⟨b, hb⟩ hcard
      obtain ⟨a, ha⟩ : ∃ a, y a ≠ 1 := by
        by_contra h
        push Not at h
        exact hy1 (funext h)
      by_cases hsingle : ∀ a', a' ≠ a → y a' = 1
      · have hy : y = Pi.mulSingle a (y a) := eq_mulSingle_of_mem_coord (mem_coord.2 hsingle)
        have hca : coord a ≤ S := coord_le_of_const_normal hconst ha (hy ▸ hyS)
        exact coord_le_of_permAut hS hca
      · push Not at hsingle
        obtain ⟨a', ha'a, ha'⟩ := hsingle
        have hba : b ≠ a := fun h => ha (h ▸ hb)
        have hba' : b ≠ a' := fun h => ha' (h ▸ hb)
        obtain ⟨t, ht⟩ := exists_not_commute_conj hR ha
        set z := permAut (Equiv.swap a' b) y with hz
        set w : ι → R := (fun _ => t) * z * (fun _ => t⁻¹) with hw
        set c := y * w * y⁻¹ * w⁻¹ with hc
        have hzS : z ∈ S := hS _ _ hyS
        have hwS : w ∈ S := hconst t z hzS
        have hcS : c ∈ S := mul_mem (mul_mem (mul_mem hyS hwS) (inv_mem hyS)) (inv_mem hwS)
        have hcapp : ∀ l, c l = y l * (t * z l * t⁻¹) * (y l)⁻¹ * (t * z l * t⁻¹)⁻¹ := by
          intro l; simp [hc, hw]
        have hzapp : ∀ l, z l = y (Equiv.swap a' b l) := by
          intro l; rw [hz, permAut_apply, Equiv.symm_swap]
        have hca : c a ≠ 1 := by
          rw [hcapp, hzapp, Equiv.swap_apply_of_ne_of_ne ha'a.symm hba.symm]
          intro h
          apply ht
          have h2 : y a * (t * y a * t⁻¹) * (y a)⁻¹ = t * y a * t⁻¹ := by
            calc y a * (t * y a * t⁻¹) * (y a)⁻¹
                = y a * (t * y a * t⁻¹) * (y a)⁻¹ * (t * y a * t⁻¹)⁻¹ * (t * y a * t⁻¹) := by
                  group
              _ = t * y a * t⁻¹ := by rw [h, one_mul]
          calc y a * (t * y a * t⁻¹) = y a * (t * y a * t⁻¹) * (y a)⁻¹ * y a := by group
            _ = t * y a * t⁻¹ * y a := by rw [h2]
        have hc1 : c ≠ 1 := fun h => hca (by rw [h]; rfl)
        have hcb : c b = 1 := by rw [hcapp, hb]; group
        have hsub : supp c ⊆ (supp y).erase a' := by
          intro l hl
          rw [mem_supp] at hl
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro hla
            subst hla
            apply hl
            rw [hcapp, hzapp, Equiv.swap_apply_left, hb]
            group
          · rw [mem_supp]
            intro hyl
            apply hl
            rw [hcapp, hyl]
            group
        have ha'mem : a' ∈ supp y := mem_supp.2 ha'
        have hcard' : (supp c).card ≤ m := by
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem ha'mem] at this
          omega
        exact ih c hcS hc1 ⟨b, hcb⟩ hcard'
  -- a first element with a trivial coordinate
  obtain ⟨x, hxS, hxd⟩ := Set.not_subset.1 hSd
  obtain ⟨a, b, hab⟩ : ∃ a b, x a ≠ x b := by
    by_contra h
    push Not at h
    apply hxd
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, funext fun i => (hι.false i).elim⟩
    · exact (mem_diag_iff).2 h
  set y := x * (fun _ => (x b)⁻¹) with hy
  have hyS : y ∈ S := mul_mem hxS (hdS (const_mem_diag _))
  have hyb : y b = 1 := by simp [hy]
  have hya : y a ≠ 1 := by
    simp only [hy, Pi.mul_apply]
    intro h
    exact hab (mul_inv_eq_one.1 h)
  exact key _ y hyS (fun h => hya (by rw [h]; rfl)) ⟨b, hyb⟩ le_rfl

include hR in
theorem diag_core [Nontrivial ι] (n : ι → R) (hn : ∀ y : ι → R, y⁻¹ * n * y ∈ diag) :
    n = 1 := by
  obtain ⟨c, rfl⟩ : n ∈ diag := by simpa using hn 1
  by_contra hc
  have hc' : c ≠ 1 := fun h => hc (by rw [h]; rfl)
  obtain ⟨t, ht⟩ := exists_not_commute hR hc'
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have h := (mem_diag_iff (f := (Pi.mulSingle i t)⁻¹ * Pi.constMonoidHom ι R c *
    Pi.mulSingle i t)).1 (hn _) i j
  simp [Pi.mulSingle_eq_of_ne hij.symm] at h
  apply ht
  calc c * t = t * (t⁻¹ * c * t) := by group
    _ = t * c := by rw [h]

include hR in
theorem diag_normal_min [Fintype ι] (Y : Subgroup (ι → R)) (hY : Y.Normal)
    (hinv : ∀ τ : Equiv.Perm ι, ∀ y ∈ Y, permAut τ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  · obtain ⟨a, ha⟩ := exists_coord_le_of_normal hR Y hbot
    exact Or.inr (coord_le_of_permAut hinv ha)

omit [DecidableEq ι] [IsSimpleGroup R] in
theorem card_diag [Nonempty ι] : Nat.card (diag (ι := ι) (R := R)) = Nat.card R := by
  have hinj : Function.Injective (Pi.constMonoidHom ι R) := by
    intro a b h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact congrFun h i
  exact Nat.card_range_of_injective hinj

end Diag

universe u

/-- **[DiM, Lemma 4.5A, Thm. 4.5A]**: for a nonabelian simple group `R` and `k ≥ 2` there is
a primitive group of diagonal type with socle `R^k` and degree `|R|^{k-1}`, on a domain in
any universe. -/
theorem exists_diag_primitive {R : Type*} [Group R] [IsSimpleGroup R] [Finite R]
    (hR : ¬ ∀ a b : R, a * b = b * a) {k : ℕ} (hk : 2 ≤ k) :
    ∃ (Ω' : Type u) (_ : Finite Ω') (U : Subgroup (Equiv.Perm Ω')), IsPrimitive U ∧
      Nonempty (socle U ≃* (Fin k → R)) ∧ Nat.card Ω' = Nat.card R ^ (k - 1) := by
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  set φ : Equiv.Perm (Fin k) →* MulAut (Fin k → R) := permAut with hφ
  set X : Subgroup (Fin k → R) := diag with hXdef
  have hX : ∀ τ : Equiv.Perm (Fin k), ∀ x ∈ X, φ τ x ∈ X := diag_inv
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  have hXtop : X ≠ ⊤ := by
    intro h
    obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin k)
    have hm : Pi.mulSingle i r ∈ X := by rw [h]; trivial
    have := (mem_diag_iff.1 hm) i j
    simp [Pi.mulSingle_eq_of_ne hij.symm] at this
    exact hr this
  have hXbot : X ≠ ⊥ := by
    intro h
    have hm : (fun _ : Fin k => r) ∈ X := const_mem_diag r
    rw [h, Subgroup.mem_bot] at hm
    exact hr (congrFun hm ⟨0, by omega⟩)
  have hmax := diag_max hR (ι := Fin k)
  have hU := isPrimitive_permGroup φ X hX hXtop hmax
  have hsoc := socle_permGroup φ X hX hXtop hmax (diag_core hR) hXbot
    (fun Y hY hinv => diag_normal_min hR Y hY hinv)
  set e : (Fin k → R) ⧸ X ≃ ULift.{u} (Fin (Nat.card ((Fin k → R) ⧸ X))) :=
    (Finite.equivFin _).trans Equiv.ulift.symm with he
  obtain ⟨U', hU', hsoc'⟩ := transport e hU hsoc
  refine ⟨_, inferInstance, U', hU', hsoc', ?_⟩
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h1 := X.index_mul_card
  rw [hXdef, card_diag, Nat.card_fun, Nat.card_fin] at h1
  have hpos : 0 < Nat.card R := Nat.card_pos
  have h2 : Nat.card R ^ k = Nat.card R ^ (k - 1) * Nat.card R := by
    rw [← pow_succ]; congr 1; omega
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end ONS

end Babai
