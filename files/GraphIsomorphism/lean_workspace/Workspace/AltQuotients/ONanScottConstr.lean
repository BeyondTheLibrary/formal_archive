/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Constructions of primitive groups used in the proof of Theorem 10.2.4.
-/
import Workspace.AltQuotients.SocleFact
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Primitive groups from a group with automorphisms

Theorem 10.2.4 was an axiom citing Dixon–Mortimer, *Permutation Groups*, GTM 163, Thm. 4.1A.
Its proof (following [DiM, Thm. 4.6A] and [DiM, Thm. 4.3B]) needs, in case (b), a primitive
group `U` with a prescribed socle.  This file builds such groups.

Let `N` be a group, `K` a group acting on `N` by automorphisms through `φ : K →* MulAut N`,
and `X ≤ N` a `K`-invariant subgroup.  Then `N ⋊ K` acts on the left cosets `N ⧸ X` by
`(n, k) · yX = n φ(k)(y) X`; `Babai.ONS.rho` is this action and `Babai.ONS.permGroup` its
image in `Sym(N ⧸ X)`.

* `Babai.ONS.isPrimitive_permGroup`: the image is primitive when no `K`-invariant subgroup
  lies strictly between `X` and `N` (the point stabilizer is then maximal);
* `Babai.ONS.socle_permGroup`: if moreover `N` acts faithfully, `X ≠ 1`, and the only
  `K`-invariant normal subgroups of `N` are `1` and `N`, then the socle of the image is the
  image of `N`, isomorphic to `N`.

The two instances used are the almost simple case (`N = T` simple, `X` a proper nontrivial
subgroup) and the diagonal case (`N = T^k`, `X` the diagonal, `K = S_k`), the groups of
[DiM, Thm. 4.6A (i), (ii)].  `Babai.ONS.transport` moves a primitive group to another
domain of the same size, in any universe.
-/

namespace Babai

namespace ONS

open Subgroup MulAction
open scoped Pointwise

section Construction

variable {N K : Type*} [Group N] [Group K] (φ : K →* MulAut N) (X : Subgroup N)
  (hX : ∀ k : K, ∀ x ∈ X, φ k x ∈ X)

include hX in
theorem act_welldef (p : N ⋊[φ] K) (a b : N) (h : a⁻¹ * b ∈ X) :
    (p.left * φ p.right a)⁻¹ * (p.left * φ p.right b) ∈ X := by
  have : (p.left * φ p.right a)⁻¹ * (p.left * φ p.right b) = φ p.right (a⁻¹ * b) := by
    simp [mul_assoc, map_mul, map_inv]
  rw [this]
  exact hX _ _ h

/-- The action of `N ⋊ K` on the left cosets of `X`. -/
def act (p : N ⋊[φ] K) : N ⧸ X → N ⧸ X :=
  Quotient.map' (fun y => p.left * φ p.right y) (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    exact act_welldef φ X hX p a b h)

theorem act_mk (p : N ⋊[φ] K) (y : N) :
    act φ X hX p (QuotientGroup.mk y) = QuotientGroup.mk (p.left * φ p.right y) := rfl

theorem act_mul (p q : N ⋊[φ] K) (z : N ⧸ X) :
    act φ X hX (p * q) z = act φ X hX p (act φ X hX q z) := by
  induction z using QuotientGroup.induction_on with
  | H y =>
    simp only [act_mk, SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul,
      MulAut.mul_apply, mul_assoc]

theorem act_one (z : N ⧸ X) : act φ X hX 1 z = z := by
  induction z using QuotientGroup.induction_on with
  | H y => simp [act_mk]

/-- The permutation representation of `N ⋊ K` on `N ⧸ X`. -/
def rho : N ⋊[φ] K →* Equiv.Perm (N ⧸ X) where
  toFun p :=
    { toFun := act φ X hX p
      invFun := act φ X hX p⁻¹
      left_inv := fun z => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun z => by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := Equiv.ext fun z => act_one φ X hX z
  map_mul' p q := Equiv.ext fun z => act_mul φ X hX p q z

theorem rho_apply_mk (p : N ⋊[φ] K) (y : N) :
    rho φ X hX p (QuotientGroup.mk y) = QuotientGroup.mk (p.left * φ p.right y) := rfl

theorem rho_inl_mk (n y : N) :
    rho φ X hX (SemidirectProduct.inl n) (QuotientGroup.mk y) = QuotientGroup.mk (n * y) := by
  simp [rho_apply_mk]

theorem rho_inr_mk (k : K) (y : N) :
    rho φ X hX (SemidirectProduct.inr k) (QuotientGroup.mk y) = QuotientGroup.mk (φ k y) := by
  simp [rho_apply_mk]

/-- The permutation group: the image of `N ⋊ K` in `Sym(N ⧸ X)`. -/
def permGroup : Subgroup (Equiv.Perm (N ⧸ X)) := (rho φ X hX).range

/-- `N ⋊ K` onto the permutation group. -/
def rho' : N ⋊[φ] K →* permGroup φ X hX := (rho φ X hX).rangeRestrict

theorem rho'_surjective : Function.Surjective (rho' φ X hX) :=
  MonoidHom.rangeRestrict_surjective _

theorem rho'_apply (p : N ⋊[φ] K) (z : N ⧸ X) :
    ((rho' φ X hX p : permGroup φ X hX) : Equiv.Perm (N ⧸ X)) z = rho φ X hX p z := rfl

/-- The base point `X` of `N ⧸ X`. -/
abbrev base : N ⧸ X := QuotientGroup.mk 1

/-- The image of `N` is transitive. -/
theorem exists_inl_eq (z : N ⧸ X) : ∃ n : N, rho φ X hX (SemidirectProduct.inl n) (base X) = z := by
  induction z using QuotientGroup.induction_on with
  | H y => exact ⟨y, by simp [rho_inl_mk]⟩

theorem isPretransitive_permGroup : IsPretransitive (permGroup φ X hX) (N ⧸ X) := by
  refine ⟨fun z w => ?_⟩
  obtain ⟨a, rfl⟩ := exists_inl_eq φ X hX z
  obtain ⟨b, rfl⟩ := exists_inl_eq φ X hX w
  refine ⟨rho' φ X hX (SemidirectProduct.inl (b * a⁻¹)), ?_⟩
  show rho φ X hX _ (rho φ X hX _ _) = rho φ X hX _ _
  rw [← Equiv.Perm.mul_apply, ← map_mul, ← SemidirectProduct.inl.map_mul (M := N)]
  simp

/-- `N` into the permutation group. -/
def iotaN : N →* permGroup φ X hX := (rho' φ X hX).comp SemidirectProduct.inl

theorem iotaN_smul_mk (n y : N) :
    (iotaN φ X hX n) • (QuotientGroup.mk y : N ⧸ X) = QuotientGroup.mk (n * y) :=
  rho_inl_mk φ X hX n y

theorem inr_smul_base (k : K) :
    (rho' φ X hX (SemidirectProduct.inr k)) • (base X) = base X := by
  show rho φ X hX _ _ = _
  rw [rho_inr_mk, map_one]

theorem iotaN_aut (k : K) (n : N) :
    iotaN φ X hX (φ k n) = rho' φ X hX (SemidirectProduct.inr k) * iotaN φ X hX n *
      (rho' φ X hX (SemidirectProduct.inr k))⁻¹ := by
  simp only [iotaN, MonoidHom.comp_apply, SemidirectProduct.inl_aut, map_mul, map_inv]

theorem iotaN_smul_base_eq_iff (n : N) : (iotaN φ X hX n) • (base X) = base X ↔ n ∈ X := by
  rw [iotaN_smul_mk, mul_one, QuotientGroup.eq]
  simp

/-- **Primitivity.**  If no `K`-invariant subgroup lies strictly between `X` and `N`, the
permutation group is primitive ([DiM, Thm. 1.5A]: the point stabilizer is maximal). -/
theorem isPrimitive_permGroup [Finite N] (hXtop : X ≠ ⊤)
    (hmax : ∀ S : Subgroup N, X ≤ S → (∀ k : K, ∀ y ∈ S, φ k y ∈ S) → S = X ∨ S = ⊤) :
    IsPrimitive (permGroup φ X hX) := by
  obtain ⟨n₀, hn₀⟩ : ∃ n, n ∉ X := by
    by_contra h
    push Not at h
    exact hXtop (eq_top_iff.2 fun n _ => h n)
  haveI : Nontrivial (N ⧸ X) := ⟨⟨QuotientGroup.mk n₀, base X, by
    intro h
    rw [QuotientGroup.eq] at h
    exact hn₀ (by simpa using inv_mem h)⟩⟩
  rw [isPrimitive_iff_isPreprimitive]
  haveI := isPretransitive_permGroup φ X hX
  refine IsPreprimitive.of_isTrivialBlock_base (base X) ?_
  intro B hoB hB
  set S : Subgroup N := (stabilizer (permGroup φ X hX) B).comap (iotaN φ X hX) with hS
  have hmemS : ∀ n, n ∈ S ↔ (iotaN φ X hX n) • B = B := fun n => Iff.rfl
  have hXS : X ≤ S := by
    intro x hx
    rw [hmemS]
    exact hB.smul_eq_of_mem hoB (by rw [(iotaN_smul_base_eq_iff φ X hX x).2 hx]; exact hoB)
  have hinvS : ∀ k : K, ∀ y ∈ S, φ k y ∈ S := by
    intro k y hy
    rw [hmemS] at hy ⊢
    have hk : (rho' φ X hX (SemidirectProduct.inr k)) • B = B :=
      hB.smul_eq_of_mem hoB (by rw [inr_smul_base]; exact hoB)
    have hk' : (rho' φ X hX (SemidirectProduct.inr k))⁻¹ • B = B := by
      rw [inv_smul_eq_iff, hk]
    rw [iotaN_aut, mul_smul, mul_smul, hk', hy, hk]
  rcases hmax S hXS hinvS with h | h
  · left
    intro z hz w hw
    have key : ∀ z ∈ B, z = base X := by
      intro z hz
      obtain ⟨y, rfl⟩ := exists_inl_eq φ X hX z
      have hyS : y ∈ S := by
        rw [hmemS]
        exact hB.smul_eq_of_mem hoB hz
      rw [h] at hyS
      exact (iotaN_smul_base_eq_iff φ X hX y).2 hyS
    rw [key z hz, key w hw]
  · right
    ext z
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y, rfl⟩ := exists_inl_eq φ X hX z
    have hyS : y ∈ S := by rw [h]; trivial
    rw [hmemS] at hyS
    rw [← hyS]
    exact Set.smul_mem_smul_set hoB

/-- `N` acts faithfully when the core of `X` is trivial. -/
theorem iotaN_injective (hcore : ∀ n : N, (∀ y : N, y⁻¹ * n * y ∈ X) → n = 1) :
    Function.Injective (iotaN φ X hX) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have key : ∀ y : N, y⁻¹ * n⁻¹ * y ∈ X := by
    intro y
    have h1 : (iotaN φ X hX n) • (QuotientGroup.mk y : N ⧸ X) = QuotientGroup.mk y := by
      rw [hn, one_smul]
    rw [iotaN_smul_mk, QuotientGroup.eq] at h1
    simpa [mul_assoc] using h1
  exact inv_eq_one.1 (hcore _ key)

/-- **Socle.**  Under the hypotheses of `isPrimitive_permGroup`, if `N` acts faithfully,
`X ≠ 1`, and the only `K`-invariant normal subgroups of `N` are `1` and `N`, then the image
of `N` is the socle, so the socle is isomorphic to `N`.  (The image of `N` is a minimal
normal subgroup that is not semiregular; by [DiM, Thm. 4.3B] a second minimal normal
subgroup would make it semiregular.) -/
theorem socle_permGroup [Finite N] (hXtop : X ≠ ⊤)
    (hmax : ∀ S : Subgroup N, X ≤ S → (∀ k : K, ∀ y ∈ S, φ k y ∈ S) → S = X ∨ S = ⊤)
    (hcore : ∀ n : N, (∀ y : N, y⁻¹ * n * y ∈ X) → n = 1) (hXbot : X ≠ ⊥)
    (hminN : ∀ Y : Subgroup N, Y.Normal → (∀ k : K, ∀ y ∈ Y, φ k y ∈ Y) → Y = ⊥ ∨ Y = ⊤) :
    Nonempty (socle (permGroup φ X hX) ≃* N) := by
  have hU := isPrimitive_permGroup φ X hX hXtop hmax
  have hinj := iotaN_injective φ X hX hcore
  set M := (iotaN φ X hX).range with hM
  have hMnorm : M.Normal := by
    constructor
    rintro _ ⟨n, rfl⟩ g
    obtain ⟨p, rfl⟩ := rho'_surjective φ X hX g
    have hmem : p * SemidirectProduct.inl n * p⁻¹ ∈
        (SemidirectProduct.inl : N →* N ⋊[φ] K).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      rw [MonoidHom.mem_ker]
      simp
    obtain ⟨n', hn'⟩ := hmem
    refine ⟨n', ?_⟩
    simp only [iotaN, MonoidHom.comp_apply]
    rw [hn']
    simp only [map_mul, map_inv]
  obtain ⟨x₀, hx₀X, hx₀⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hXbot (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  have hMne : M ≠ ⊥ := by
    intro h
    have : iotaN φ X hX x₀ ∈ M := ⟨x₀, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx₀ (hinj (by rw [this, map_one]))
  have hMmin : IsMinimalNormal M := by
    refine ⟨hMnorm, hMne, ?_⟩
    intro M' hM'n hM'ne hM'le
    refine le_antisymm hM'le ?_
    set Y := M'.comap (iotaN φ X hX) with hY
    have hYn : Y.Normal := hM'n.comap _
    have hYinv : ∀ k : K, ∀ y ∈ Y, φ k y ∈ Y := by
      intro k y hy
      show iotaN φ X hX (φ k y) ∈ M'
      rw [iotaN_aut]
      exact hM'n.conj_mem _ hy _
    have hYne : Y ≠ ⊥ := by
      intro h
      apply hM'ne
      rw [eq_bot_iff]
      intro m hm
      obtain ⟨y, rfl⟩ := hM'le hm
      have : y ∈ Y := hm
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    rcases hminN Y hYn hYinv with h | h
    · exact absurd h hYne
    · rintro _ ⟨y, rfl⟩
      have : y ∈ Y := by rw [h]; trivial
      exact this
  have hset : {M'' : Subgroup (permGroup φ X hX) | IsMinimalNormal M''} = {M} := by
    ext M''
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun hM'' => ?_, fun h => h ▸ hMmin⟩
    by_contra hne
    have hcent := eq_centralizer_of_isMinimalNormal hU hM'' hMmin hne
    haveI := hM''.1
    have htr := isPretransitive_of_normal_of_isPrimitive hU M'' hM''.2.1
    have hcM : iotaN φ X hX x₀ ∈ Subgroup.centralizer (M'' : Set (permGroup φ X hX)) := by
      rw [← hcent]; exact ⟨x₀, rfl⟩
    have hc : ∀ m ∈ M'', iotaN φ X hX x₀ * m = m * iotaN φ X hX x₀ := fun m hm =>
      ((Subgroup.mem_centralizer_iff.1 hcM) m hm).symm
    have hfix : ((iotaN φ X hX x₀ : permGroup φ X hX) : Equiv.Perm (N ⧸ X)) (base X) =
        base X := (iotaN_smul_base_eq_iff φ X hX x₀).2 hx₀X
    have h1 := eq_one_of_centralizes_of_fixed htr hc hfix
    exact hx₀ (hinj (by rw [h1, map_one]))
  have hsoc : socle (permGroup φ X hX) = M := by
    rw [socle, hset, sSup_singleton]
  exact ⟨(MulEquiv.subgroupCongr hsoc).trans (MonoidHom.ofInjective hinj).symm⟩

end Construction

/-! ### Transport along a bijection of the domain -/

section Transport

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphism carries minimal normal subgroups to minimal normal subgroups. -/
theorem isMinimalNormal_map (f : G ≃* G') {M : Subgroup G} (hM : IsMinimalNormal M) :
    IsMinimalNormal (M.map f.toMonoidHom) := by
  haveI := hM.1
  refine ⟨Subgroup.Normal.map inferInstance _ f.surjective, ?_, ?_⟩
  · intro h
    exact hM.2.1 ((Subgroup.map_eq_bot_iff_of_injective _ f.injective).1 h)
  · intro M' hM'n hM'ne hM'le
    set M'' := M'.comap f.toMonoidHom with hM''
    have hmap : M''.map f.toMonoidHom = M' :=
      Subgroup.map_comap_eq_self_of_surjective f.surjective _
    have hM''n : M''.Normal := hM'n.comap _
    have hM''ne : M'' ≠ ⊥ := by
      intro h
      apply hM'ne
      rw [← hmap, h, Subgroup.map_bot]
    have hM''le : M'' ≤ M := by
      have := Subgroup.comap_mono (f := f.toMonoidHom) hM'le
      rwa [Subgroup.comap_map_eq_self_of_injective f.injective] at this
    have := hM.2.2 M'' hM''n hM''ne hM''le
    rw [← hmap, this]

/-- The socle is carried to the socle by a group isomorphism. -/
theorem socle_map_mulEquiv (f : G ≃* G') : (socle G).map f.toMonoidHom = socle G' := by
  rw [socle, socle, (Subgroup.gc_map_comap f.toMonoidHom).l_sSup, ← sSup_image]
  congr 1
  ext M'
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact isMinimalNormal_map f hM
  · intro hM'
    refine ⟨M'.map f.symm.toMonoidHom, isMinimalNormal_map f.symm hM', ?_⟩
    rw [Subgroup.map_map]
    convert Subgroup.map_id M'
    ext x
    simp

/-- Isomorphic groups have isomorphic socles. -/
theorem nonempty_socle_mulEquiv (f : G ≃* G') : Nonempty (socle G ≃* socle G') :=
  ⟨((socle G).equivMapOfInjective f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr (socle_map_mulEquiv f))⟩

/-- **Transport.**  A primitive group, with its socle, can be moved along a bijection of
its domain; the new domain may lie in another universe. -/
theorem transport {Ω₁ Ω₂ : Type*} [Finite Ω₁] (e : Ω₁ ≃ Ω₂)
    {U : Subgroup (Equiv.Perm Ω₁)} (hU : IsPrimitive U) {T : Type*} [Group T]
    (hsoc : Nonempty (socle U ≃* T)) :
    ∃ U' : Subgroup (Equiv.Perm Ω₂), IsPrimitive U' ∧ Nonempty (socle U' ≃* T) := by
  haveI : Finite Ω₂ := Finite.of_equiv _ e
  haveI := hU.nontrivial_dom
  haveI : Nontrivial Ω₂ := e.symm.nontrivial
  set U' := U.map e.permCongrHom.toMonoidHom with hU'
  set ψ : U ≃* U' := U.equivMapOfInjective _ e.permCongrHom.injective with hψ
  refine ⟨U', ?_, ?_⟩
  · rw [isPrimitive_iff_isPreprimitive] at hU ⊢
    let f : Ω₁ →ₑ[ψ] Ω₂ :=
      { toFun := e
        map_smul' := by
          intro u x
          change e ((u : Equiv.Perm Ω₁) x) = (e.permCongr (u : Equiv.Perm Ω₁)) (e x)
          simp [Equiv.permCongr_apply] }
    exact (isPreprimitive_congr ψ.surjective e.bijective (f := f)).1 hU
  · obtain ⟨g⟩ := hsoc
    obtain ⟨h⟩ := nonempty_socle_mulEquiv ψ.symm
    exact ⟨h.trans g⟩

end Transport

end ONS

end Babai
