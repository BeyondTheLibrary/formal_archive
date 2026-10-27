/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The core of the proof of Theorem 10.2.4, inside a direct power `R^s`.
-/
import Workspace.AltQuotients.ONanScottDiag

/-!
# The O'Nan–Scott analysis inside `R^s`

This is the proof of [DiM, Thm. 4.6A] (Dixon–Mortimer, *Permutation Groups*, GTM 163,
pp. 125–129) reduced to what Theorem 10.2.4 needs, stated for the socle `H ≅ R^s` of a
primitive group, a point stabilizer `X = H_α`, and the automorphisms of `R^s` induced by
the point stabilizer `G_α` (a group `Γ` acting through `ψ : Γ →* Aut(R^s)`):

* `(h1)` the only `Γ`-invariant normal subgroups of `R^s` are `1` and `R^s` (`H` is a
  minimal normal subgroup of `G`);
* `(h2)` the only `Γ`-invariant subgroups containing `X` are `X` and `R^s` (`G_α` is
  maximal in `G`);
* `(h3)` `X ≠ R^s` (`n ≥ 2`).

Let `R_i` be the projection of `X` to the `i`-th coordinate.
* **Case 1** ([DiM, p. 126]): `R_1 < R`.  Then `X = R_1 × ⋯ × R_s` and `n = |R : R_1|^s`,
  and `R_1` is a point stabilizer of a primitive group with socle `R`
  (`Babai.ONS.core_case1`).
* **Case 2** ([DiM, p. 127]): `R_i = R` for all `i`.  With `K_i = X ∩ ker π_i`, `X ≅ R^d`
  where `d` is the number of distinct `K_i`, the `s` indices fall into `d` classes of equal
  size `s/d`, and `n = |R|^{s-d}`; `d = 1` is case (a), `1 < d < s` gives the diagonal group
  with socle `R^{s/d}` (`Babai.ONS.core_case2`).
-/

namespace Babai

namespace ONS

open Subgroup

/-! ### Subdirect products of copies of a nonabelian simple group -/

section Goursat

variable {X R C : Type*} [Group X] [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a)

include hR in
/-- **[DiM, Lemma 4.3A]**, the form used in Case 2: homomorphisms onto a nonabelian simple
group with pairwise distinct kernels are jointly onto. -/
theorem jointly_surjective [DecidableEq C] (κ : C → X →* R)
    (hsurj : ∀ c, Function.Surjective (κ c))
    (hdist : ∀ c c', (κ c).ker = (κ c').ker → c = c') (F : Finset C) :
    ∀ t : C → R, ∃ x : X, ∀ c ∈ F, κ c x = t c := by
  induction F using Finset.induction_on with
  | empty => exact fun t => ⟨1, fun c hc => absurd hc (Finset.notMem_empty c)⟩
  | insert c₀ F hc₀ ih =>
    intro t
    -- the image of `ker κ c₀` in `R^F` is everything
    let Φ : X →* (F → R) := Pi.monoidHom fun c : F => κ c
    have hΦ : Function.Surjective Φ := by
      intro t'
      obtain ⟨x, hx⟩ := ih (fun c => if h : c ∈ F then t' ⟨c, h⟩ else 1)
      refine ⟨x, funext fun c => ?_⟩
      have := hx c c.2
      simp only [c.2, dif_pos] at this
      exact this
    set Z := (κ c₀).ker with hZ
    set W := Z.map Φ with hW
    haveI : W.Normal := Subgroup.Normal.map inferInstance Φ hΦ
    have hWtop : W = ⊤ := by
      apply eq_top_of_coord_le
      intro c
      -- some element of `W` has nontrivial `c`-coordinate
      by_contra hc
      have hcoord : ∀ w ∈ W, w c = 1 := by
        intro w hw
        by_contra hw1
        exact hc (coord_le_of_normal hR W hw hw1)
      have hZle : Z ≤ (κ c).ker := by
        intro z hz
        have := hcoord (Φ z) ⟨z, hz, rfl⟩
        exact this
      -- the image of `ker κ c` in `R` under `κ c₀` is normal, so `1` or `R`
      set V := ((κ c).ker).map (κ c₀) with hV
      haveI : V.Normal := Subgroup.Normal.map inferInstance _ (hsurj c₀)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V inferInstance with h | h
      · have hle : (κ c).ker ≤ Z := by
          intro y hy
          have : κ c₀ y ∈ V := ⟨y, hy, rfl⟩
          rw [h, Subgroup.mem_bot] at this
          exact this
        have := hdist _ _ (le_antisymm hle hZle).symm
        exact hc₀ (this ▸ c.2)
      · obtain ⟨r, hr⟩ := exists_ne (1 : R)
        obtain ⟨x, rfl⟩ := hsurj c r
        apply hr
        have hxV : κ c₀ x ∈ V := by rw [h]; trivial
        obtain ⟨y, hy, hyx⟩ := hxV
        have hz : x * y⁻¹ ∈ Z := by
          rw [hZ, MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
        have h1 := hZle hz
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 hy, inv_one,
          mul_one] at h1
        exact h1
    obtain ⟨x₀, hx₀⟩ := hsurj c₀ (t c₀)
    have hmem : (fun c : F => t c * (κ c x₀)⁻¹) ∈ W := by rw [hWtop]; trivial
    obtain ⟨z, hzZ, hz⟩ := hmem
    refine ⟨z * x₀, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hcF
    · rw [map_mul, MonoidHom.mem_ker.1 hzZ, one_mul, hx₀]
    · have := congrFun hz ⟨c, hcF⟩
      simp only [Φ, Pi.monoidHom_apply] at this
      rw [map_mul, this, inv_mul_cancel_right]

end Goursat

/-! ### The setting -/

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a) {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut (ι → R))

/-- `Y` is invariant under the automorphisms `ψ(Γ)`. -/
def PsiInv (Y : Subgroup (ι → R)) : Prop := ∀ g : Γ, ∀ y ∈ Y, ψ g y ∈ Y

omit [Fintype ι] in
include hR in
theorem sigma_psi_mul (g h : Γ) (i : ι) :
    sigma (ψ (g * h)) i = sigma (ψ g) (sigma (ψ h) i) := by
  rw [map_mul, sigma_mul hR]

omit [Fintype ι] in
include hR in
theorem sigma_psi_inv_left (g : Γ) (i : ι) : sigma (ψ g⁻¹) (sigma (ψ g) i) = i := by
  rw [map_inv, sigma_inv_sigma hR]

omit [Fintype ι] in
include hR in
theorem sigma_psi_inv_right (g : Γ) (i : ι) : sigma (ψ g) (sigma (ψ g⁻¹) i) = i := by
  rw [map_inv, sigma_sigma_inv hR]

omit [Fintype ι] in
include hR in
/-- The coordinate formula `(ψ(g) f)_j = θ(f_{σ⁻¹ j})`. -/
theorem psi_apply (g : Γ) (f : ι → R) (j : ι) :
    ψ g f j = theta (ψ g) (sigma (ψ g⁻¹) j) (f (sigma (ψ g⁻¹) j)) := by
  conv_lhs => rw [← sigma_psi_inv_right hR ψ g j]
  exact apply_sigma hR (ψ g) f _

/-- The subgroup of functions supported on `O`. -/
def suppSub (O : Set ι) : Subgroup (ι → R) where
  carrier := {f | ∀ j, j ∉ O → f j = 1}
  mul_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  one_mem' j _ := rfl
  inv_mem' {a} ha j hj := by simp [ha j hj]

omit [Fintype ι] in
include hR in
/-- **[DiM, Thm. 4.3A]** with minimality: if the only `ψ(Γ)`-invariant normal subgroups of
`R^ι` are `1` and `R^ι`, then `Γ` permutes the coordinates transitively. -/
theorem sigma_transitive
    (h1 : ∀ Y : Subgroup (ι → R), Y.Normal → PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤) (i j : ι) :
    ∃ g : Γ, sigma (ψ g) i = j := by
  set O : Set ι := {l | ∃ g : Γ, sigma (ψ g) i = l} with hO
  set Y : Subgroup (ι → R) := suppSub O with hY
  have hYn : Y.Normal := by
    constructor
    intro f hf g l hl
    simp [hf l hl]
  have hYinv : PsiInv ψ Y := by
    intro g f hf l hl
    rw [psi_apply hR]
    have : sigma (ψ g⁻¹) l ∉ O := by
      rintro ⟨h, hh⟩
      apply hl
      refine ⟨g * h, ?_⟩
      rw [sigma_psi_mul hR, hh, sigma_psi_inv_right hR]
    rw [hf _ this, map_one]
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  rcases h1 Y hYn hYinv with h | h
  · exfalso
    have hm : Pi.mulSingle i r ∈ Y := by
      intro l hl
      have : l ≠ i := fun h => hl ⟨1, by rw [h, map_one, sigma_one]⟩
      simp [Pi.mulSingle_eq_of_ne this]
    rw [h, Subgroup.mem_bot] at hm
    exact hr (by simpa using congrFun hm i)
  · by_contra hj
    have hm : Pi.mulSingle j r ∈ Y := by rw [h]; trivial
    have := hm j (fun ⟨g, hg⟩ => hj ⟨g, hg⟩)
    simp at this
    exact hr this

/-- The projection `R_i` of `X` to the `i`-th coordinate. -/
def rpart (X : Subgroup (ι → R)) (i : ι) : Subgroup R := X.map (Pi.evalMonoidHom _ i)

omit [Fintype ι] [DecidableEq ι] [IsSimpleGroup R] in
theorem mem_rpart {X : Subgroup (ι → R)} {i : ι} {r : R} :
    r ∈ rpart X i ↔ ∃ x ∈ X, x i = r := by
  simp [rpart]

omit [Fintype ι] in
include hR in
theorem theta_mem_rpart {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X) (g : Γ) {i : ι} {r : R}
    (hr : r ∈ rpart X i) : theta (ψ g) i r ∈ rpart X (sigma (ψ g) i) := by
  obtain ⟨x, hx, rfl⟩ := mem_rpart.1 hr
  exact mem_rpart.2 ⟨ψ g x, hXinv g x hx, apply_sigma hR (ψ g) x i⟩

omit [Fintype ι] in
include hR in
theorem card_rpart_le [Finite R] {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X)
    (h1 : ∀ Y : Subgroup (ι → R), Y.Normal → PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤) (i j : ι) :
    Nat.card (rpart X i) ≤ Nat.card (rpart X j) := by
  obtain ⟨g, rfl⟩ := sigma_transitive hR ψ h1 i j
  have hinj : Function.Injective (theta (ψ g) i) := (thetaEquiv hR (ψ g) i).injective
  refine Nat.card_le_card_of_injective
    (fun r : rpart X i => (⟨theta (ψ g) i r, theta_mem_rpart hR ψ hXinv g r.2⟩ :
      rpart X (sigma (ψ g) i))) ?_
  intro a b hab
  exact Subtype.ext (hinj (congrArg Subtype.val hab))

omit [Fintype ι] in
include hR in
theorem card_rpart_eq [Finite R] {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X)
    (h1 : ∀ Y : Subgroup (ι → R), Y.Normal → PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤) (i j : ι) :
    Nat.card (rpart X i) = Nat.card (rpart X j) :=
  le_antisymm (card_rpart_le hR ψ hXinv h1 i j) (card_rpart_le hR ψ hXinv h1 j i)

end Setting

/-! ### Case 1: `R_1 < R` -/

section Case1

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a) {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut (ι → R))

/-- The stabilizer in `Γ` of the coordinate `i₀`. -/
def stabCoord (i₀ : ι) : Subgroup Γ where
  carrier := {g | sigma (ψ g) i₀ = i₀}
  mul_mem' {a b} ha hb := by
    show sigma (ψ (a * b)) i₀ = i₀
    simp only [Set.mem_setOf_eq] at ha hb
    rw [sigma_psi_mul hR ψ, hb, ha]
  one_mem' := by
    show sigma (ψ 1) i₀ = i₀
    rw [map_one, sigma_one]
  inv_mem' {a} ha := by
    show sigma (ψ a⁻¹) i₀ = i₀
    simp only [Set.mem_setOf_eq] at ha
    conv_lhs => rw [← ha]
    exact sigma_psi_inv_left hR ψ a i₀

omit [Fintype ι] in
theorem mem_stabCoord {i₀ : ι} {g : Γ} : g ∈ stabCoord hR ψ i₀ ↔ sigma (ψ g) i₀ = i₀ :=
  Iff.rfl

/-- The action of the coordinate stabilizer on the `i₀`-th factor. -/
noncomputable def stabAct (i₀ : ι) : stabCoord hR ψ i₀ →* MulAut R where
  toFun g := thetaEquiv hR (ψ g) i₀
  map_one' := by
    ext r
    rw [thetaEquiv_apply, OneMemClass.coe_one, map_one, theta_one]
    rfl
  map_mul' g h := by
    ext r
    rw [thetaEquiv_apply, MulAut.mul_apply, thetaEquiv_apply, thetaEquiv_apply,
      Subgroup.coe_mul, map_mul, theta_mul hR, (mem_stabCoord hR ψ).1 h.2]

omit [Fintype ι] in
theorem stabAct_apply (i₀ : ι) (g : stabCoord hR ψ i₀) (r : R) :
    stabAct hR ψ i₀ g r = theta (ψ g) i₀ r := rfl

omit [Fintype ι] in
include hR in
theorem theta_theta (g h : Γ) (i : ι) (r : R) :
    theta (ψ g) (sigma (ψ h) i) (theta (ψ h) i r) = theta (ψ (g * h)) i r := by
  rw [map_mul, theta_mul hR]

universe u

include hR in
/-- **Case 1 of [DiM, Thm. 4.6A]** (p. 126): if `R_{i₀} < R` then `X = R_1 × ⋯ × R_s`,
`n = |R : R_{i₀}|^s`, and there is a primitive group with socle `R` of degree
`|R : R_{i₀}|`. -/
theorem core_case1 [Finite R] {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X)
    (h1 : ∀ Y : Subgroup (ι → R), Y.Normal → PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤)
    (h2 : ∀ Y : Subgroup (ι → R), X ≤ Y → PsiInv ψ Y → Y = X ∨ Y = ⊤)
    (hXbot : X ≠ ⊥) (i₀ : ι) (hne : rpart X i₀ ≠ ⊤) :
    ∃ (Ω' : Type u) (_ : Finite Ω') (U : Subgroup (Equiv.Perm Ω')), IsPrimitive U ∧
      Nonempty (socle U ≃* R) ∧ X.index = Nat.card Ω' ^ Fintype.card ι := by
  have hcard := card_rpart_eq hR ψ hXinv h1
  -- all projections are proper
  have hall : ∀ i, rpart X i ≠ ⊤ := by
    intro i hi
    apply hne
    rw [← Subgroup.card_eq_iff_eq_top, hcard i₀ i, hi, Subgroup.card_top]
  set K : Subgroup (ι → R) := Subgroup.pi Set.univ (rpart X) with hK
  have hXK : X ≤ K := fun x hx i _ => mem_rpart.2 ⟨x, hx, rfl⟩
  have hKinv : PsiInv ψ K := by
    intro g f hf j _
    rw [psi_apply hR]
    have := theta_mem_rpart hR ψ hXinv g (hf (sigma (ψ g⁻¹) j) (Set.mem_univ _))
    rwa [sigma_psi_inv_right hR] at this
  obtain ⟨r₀, hr₀⟩ : ∃ r, r ∉ rpart X i₀ := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun r _ => h r)
  have hKtop : K ≠ ⊤ := by
    intro h
    have hm : Pi.mulSingle i₀ r₀ ∈ K := by rw [h]; trivial
    have := hm i₀ (Set.mem_univ _)
    simp at this
    exact hr₀ this
  have hKX : K = X := (h2 K hXK hKinv).resolve_right hKtop
  have hRbot : rpart X i₀ ≠ ⊥ := by
    intro hb
    apply hXbot
    rw [← hKX, eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    funext i
    have hbi : rpart X i = ⊥ := by
      rw [← Subgroup.card_eq_one, ← hcard i₀ i, hb, Subgroup.card_bot]
    have : f i ∈ rpart X i := hf i (Set.mem_univ _)
    rw [hbi, Subgroup.mem_bot] at this
    exact this
  -- the index
  have hindex : X.index = (rpart X i₀).index ^ Fintype.card ι := by
    have hXKi : X.index = K.index := by rw [hKX]
    rw [hXKi, hK, Subgroup.index_pi]
    have : ∀ i, (rpart X i).index = (rpart X i₀).index := by
      intro i
      have h1' := (rpart X i).index_mul_card
      have h2' := (rpart X i₀).index_mul_card
      rw [hcard i₀ i] at h2'
      have hpos : 0 < Nat.card (rpart X i) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (h1'.trans h2'.symm)
    simp [this]
  -- the almost simple group on the cosets of `R_{i₀}`
  set Γ₀ := stabCoord hR ψ i₀ with hΓ₀
  set φ := stabAct hR ψ i₀ with hφ
  set X₀ := rpart X i₀ with hX₀def
  have hX₀ : ∀ g : Γ₀, ∀ x ∈ X₀, φ g x ∈ X₀ := by
    intro g x hx
    have := theta_mem_rpart hR ψ hXinv (g : Γ) hx
    rwa [(mem_stabCoord hR ψ).1 g.2] at this
  choose gsel hgsel using fun j => sigma_transitive hR ψ h1 i₀ j
  have hmax : ∀ S : Subgroup R, X₀ ≤ S → (∀ g : Γ₀, ∀ y ∈ S, φ g y ∈ S) →
      S = X₀ ∨ S = ⊤ := by
    intro S hS0 hSinv
    set Sj : ι → Subgroup R := fun j => S.map (theta (ψ (gsel j)) i₀) with hSj
    set K' : Subgroup (ι → R) := Subgroup.pi Set.univ Sj with hK'
    have hXK' : X ≤ K' := by
      intro x hx j _
      set y := ψ (gsel j)⁻¹ x with hy
      have hyX : y ∈ X := hXinv _ x hx
      have hxy : x = ψ (gsel j) y := by
        rw [hy, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      refine ⟨y i₀, hS0 (mem_rpart.2 ⟨y, hyX, rfl⟩), ?_⟩
      have := apply_sigma hR (ψ (gsel j)) y i₀
      rw [hgsel j] at this
      rw [hxy, this]
    have hK'inv : PsiInv ψ K' := by
      intro g f hf j _
      rw [psi_apply hR]
      set l := sigma (ψ g⁻¹) j with hl
      obtain ⟨t, htS, ht⟩ := hf l (Set.mem_univ _)
      rw [← ht]
      -- `θ_{g,l} θ_{g_l,i₀} = θ_{g g_l, i₀} = θ_{g_j, i₀} θ_{h, i₀}` with `h ∈ Γ₀`
      have hgl : sigma (ψ (gsel l)) i₀ = l := hgsel l
      have key : theta (ψ g) l (theta (ψ (gsel l)) i₀ t) = theta (ψ (g * gsel l)) i₀ t := by
        have := theta_theta hR ψ g (gsel l) i₀ t
        rwa [hgl] at this
      rw [key]
      set h : Γ := (gsel j)⁻¹ * (g * gsel l) with hh
      have hhmem : h ∈ Γ₀ := by
        rw [mem_stabCoord, hh, sigma_psi_mul hR, sigma_psi_mul hR, hgl, hl,
          sigma_psi_inv_right hR]
        have := sigma_psi_inv_left hR ψ (gsel j) i₀
        rwa [hgsel j] at this
      have heq : g * gsel l = gsel j * h := by rw [hh]; group
      rw [heq, ← theta_theta hR ψ, (mem_stabCoord hR ψ).1 hhmem]
      exact ⟨theta (ψ h) i₀ t, hSinv ⟨h, hhmem⟩ t htS, rfl⟩
    have hg₀ : gsel i₀ ∈ Γ₀ := hgsel i₀
    rcases h2 K' hXK' hK'inv with h | h
    · left
      refine le_antisymm (fun t ht => ?_) hS0
      set r := theta (ψ (gsel i₀)) i₀ t with hr
      have hm : Pi.mulSingle i₀ r ∈ K' := by
        intro j _
        by_cases hj : j = i₀
        · subst hj; simp only [Pi.mulSingle_eq_same]; exact ⟨t, ht, rfl⟩
        · rw [Pi.mulSingle_eq_of_ne hj]; exact Subgroup.one_mem _
      rw [h] at hm
      have hrX : r ∈ X₀ := mem_rpart.2 ⟨_, hm, by simp⟩
      have := hX₀ ⟨(gsel i₀)⁻¹, inv_mem hg₀⟩ r hrX
      rw [stabAct_apply, hr] at this
      have hθ := theta_theta hR ψ (gsel i₀)⁻¹ (gsel i₀) i₀ t
      rw [(mem_stabCoord hR ψ).1 hg₀, inv_mul_cancel, map_one, theta_one] at hθ
      rwa [hθ] at this
    · right
      refine eq_top_iff.2 fun r _ => ?_
      have hm : Pi.mulSingle i₀ r ∈ K' := by rw [h]; trivial
      obtain ⟨t, htS, ht⟩ := hm i₀ (Set.mem_univ _)
      simp only [Pi.mulSingle_eq_same] at ht
      rw [← ht]
      exact hSinv ⟨gsel i₀, hg₀⟩ t htS
  have hcore : ∀ n : R, (∀ y : R, y⁻¹ * n * y ∈ X₀) → n = 1 := by
    intro n hn
    have hc : X₀.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ X₀.normalCore_normal with h | h
      · exact h
      · exact absurd (eq_top_iff.2 (h ▸ X₀.normalCore_le)) hne
    have hmem : n ∈ X₀.normalCore := fun b => by simpa using hn b⁻¹
    rw [hc, Subgroup.mem_bot] at hmem
    exact hmem
  have hU := isPrimitive_permGroup φ X₀ hX₀ hne hmax
  have hsoc := socle_permGroup φ X₀ hX₀ hne hmax hcore hRbot
    (fun Y hY _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal Y hY)
  set e : R ⧸ X₀ ≃ ULift.{u} (Fin (Nat.card (R ⧸ X₀))) :=
    (Finite.equivFin _).trans Equiv.ulift.symm with he
  obtain ⟨U', hU', hsoc'⟩ := transport e hU hsoc
  refine ⟨_, inferInstance, U', hU', hsoc', ?_⟩
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin, hindex]
  rfl

end Case1

/-! ### Case 2: `R_i = R` for all `i` -/

section Case2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a) {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut (ι → R))

/-- The `i`-th coordinate on `X`. -/
def kappa (X : Subgroup (ι → R)) (i : ι) : X →* R :=
  (Pi.evalMonoidHom (fun _ : ι => R) i).comp X.subtype

omit [Fintype ι] [DecidableEq ι] [IsSimpleGroup R] in
theorem kappa_apply (X : Subgroup (ι → R)) (i : ι) (x : X) : kappa X i x = (x : ι → R) i := rfl

omit [Fintype ι] in
include hR in
/-- The kernels `K_i = X ∩ ker π_i` move with the coordinates: `K_i = K_{i'}` implies
`K_{σ i} = K_{σ i'}` ([DiM, p. 128], "condition (4.4)"). -/
theorem ker_kappa_sigma {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X) (g : Γ) {i i' : ι}
    (h : (kappa X i).ker = (kappa X i').ker) :
    (kappa X (sigma (ψ g) i)).ker = (kappa X (sigma (ψ g) i')).ker := by
  have key : ∀ l : ι, ∀ x : X, x ∈ (kappa X (sigma (ψ g) l)).ker ↔
      (⟨ψ g⁻¹ x, hXinv _ _ x.2⟩ : X) ∈ (kappa X l).ker := by
    intro l x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, kappa_apply, kappa_apply]
    have hx : (x : ι → R) = ψ g (ψ g⁻¹ x) := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hx' : (x : ι → R) (sigma (ψ g) l) = theta (ψ g) l ((ψ g⁻¹ (x : ι → R)) l) := by
      conv_lhs => rw [hx]
      exact apply_sigma hR (ψ g) _ l
    rw [hx', ← thetaEquiv_apply hR, MulEquiv.map_eq_one_iff]
  ext x
  rw [key, key, h]

universe u

include hR in
/-- **Case 2 of [DiM, Thm. 4.6A]** (pp. 127–129): if every projection `R_i` is all of `R`,
then `X ≅ R^d` where `d` is the number of distinct kernels `K_i`, the kernels split the `s`
coordinates into `d` classes of equal size, `n = |R|^{s-d}`, and either `d = 1`
(`n = |R|^{s-1}`) or `1 < d < s` and the diagonal group with socle `R^{s/d}` has degree
`ℓ` with `n = ℓ^d`. -/
theorem core_case2 [Finite R] {X : Subgroup (ι → R)} (hXinv : PsiInv ψ X)
    (h1 : ∀ Y : Subgroup (ι → R), Y.Normal → PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤)
    (hXtop : X ≠ ⊤) (hfull : ∀ i, rpart X i = ⊤) (hs : 2 ≤ Fintype.card ι) :
    Nat.card R ^ (Fintype.card ι - 1) ≤ X.index ∨
      ∃ d : ℕ, d ∣ Fintype.card ι ∧ d < Fintype.card ι ∧
        ∃ (Ω' : Type u) (_ : Finite Ω') (U : Subgroup (Equiv.Perm Ω')), IsPrimitive U ∧
          Nonempty (socle U ≃* (Fin d → R)) ∧
            X.index = Nat.card Ω' ^ (Fintype.card ι / d) := by
  classical
  set s := Fintype.card ι with hsdef
  set Kr : ι → Subgroup X := fun i => (kappa X i).ker with hKr
  have hsurj : ∀ i, Function.Surjective (kappa X i) := by
    intro i r
    have : r ∈ rpart X i := by rw [hfull i]; trivial
    obtain ⟨x, hx, rfl⟩ := mem_rpart.1 this
    exact ⟨⟨x, hx⟩, rfl⟩
  set D : Finset (Subgroup X) := Finset.univ.image Kr with hD
  set d := D.card with hd
  have hrep : ∀ K : D, ∃ i, Kr i = K := by
    intro K
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 K.2
    exact ⟨i, hi⟩
  choose rep hrep using hrep
  set Φ : X →* (D → R) := Pi.monoidHom fun K => kappa X (rep K) with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    funext i
    have hKi : Kr i ∈ D := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h1' := congrFun hx ⟨Kr i, hKi⟩
    simp only [hΦ, Pi.monoidHom_apply, Pi.one_apply] at h1'
    have hmem : x ∈ Kr (rep ⟨Kr i, hKi⟩) := MonoidHom.mem_ker.2 h1'
    rw [hrep] at hmem
    exact MonoidHom.mem_ker.1 hmem
  have hΦsurj : Function.Surjective Φ := by
    intro t
    obtain ⟨x, hx⟩ := jointly_surjective hR (fun K : D => kappa X (rep K))
      (fun K => hsurj (rep K))
      (fun K K' h => Subtype.ext (by
        have := hrep K; have := hrep K'
        simp only [hKr] at *
        rw [← hrep K, ← hrep K']; exact h)) Finset.univ t
    exact ⟨x, funext fun K => hx K (Finset.mem_univ K)⟩
  have hcardX : Nat.card X = Nat.card R ^ d := by
    rw [Nat.card_congr (MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).toEquiv, Nat.card_fun,
      Nat.card_eq_fintype_card (α := D), Fintype.card_coe]
  have hindex : X.index * Nat.card R ^ d = Nat.card R ^ s := by
    rw [← hcardX, X.index_mul_card, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hR1 : 1 < Nat.card R := Finite.one_lt_card
  -- the fibres of `i ↦ K_i` all have the same size
  set fib : Subgroup X → Finset ι := fun K => Finset.univ.filter (fun i => Kr i = K) with hfib
  have hfib_le : ∀ i j, (fib (Kr i)).card ≤ (fib (Kr j)).card := by
    intro i j
    obtain ⟨g, hg⟩ := sigma_transitive hR ψ h1 i j
    refine Finset.card_le_card_of_injOn (sigma (ψ g)) ?_ ?_
    · intro l hl
      simp only [hfib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl ⊢
      rw [← hg]
      exact ker_kappa_sigma hR ψ hXinv g hl
    · intro a _ b _ hab
      have := congrArg (sigma (ψ g⁻¹)) hab
      simpa only [sigma_psi_inv_left hR] using this
  have hi₀ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hi₀
  set k := (fib (Kr i₀)).card with hk
  have hfibD : ∀ K ∈ D, (fib K).card = k := by
    intro K hK
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hK
    exact le_antisymm (hfib_le i i₀) (hfib_le i₀ i)
  have hsdk : s = d * k := by
    rw [hsdef, ← Finset.card_univ, Finset.card_eq_sum_card_image Kr Finset.univ]
    rw [Finset.sum_congr rfl (fun K hK => hfibD K hK), Finset.sum_const, smul_eq_mul]
  have hdle : d ≤ s := by
    rw [hd, hD, hsdef]
    exact (Finset.card_image_le).trans (by rw [Finset.card_univ])
  have hdlt : d < s := by
    rcases hdle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hXtop
      rw [← Subgroup.index_eq_one]
      rw [h] at hindex
      have hp : 0 < Nat.card R ^ s := pow_pos hRpos s
      have : X.index * Nat.card R ^ s = 1 * Nat.card R ^ s := by rw [hindex, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hp this
  have hdpos : 0 < d := by
    rw [hd, Finset.card_pos]
    exact ⟨Kr i₀, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hidx : X.index = Nat.card R ^ (s - d) := by
    have h' : Nat.card R ^ s = Nat.card R ^ (s - d) * Nat.card R ^ d := by
      rw [← pow_add]; congr 1; omega
    rw [h'] at hindex
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hRpos d) hindex
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · left
    have : d = 1 := by omega
    rw [hidx, this]
  · right
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k ≤ 1 := by omega
      have : d * k ≤ d := by nlinarith
      omega
    have hks : k < s := by
      rw [hsdk]; nlinarith
    obtain ⟨Ω', hΩ', U, hU, hsoc, hcard⟩ := exists_diag_primitive.{u} hR hk2
    refine ⟨k, ⟨d, by rw [hsdk, mul_comm]⟩, hks, Ω', hΩ', U, hU, hsoc, ?_⟩
    have hsk : s / k = d := by
      rw [hsdk, Nat.mul_div_cancel _ (by omega)]
    rw [hcard, hsk, hidx, ← pow_mul]
    congr 1
    rw [hsdk, Nat.sub_mul, one_mul, mul_comm]

end Case2

/-! ### Normal subgroups of `R^ι` -/

section NormalCard

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Group R] [IsSimpleGroup R]
  (hR : ¬ ∀ a b : R, a * b = b * a)

omit [Fintype ι] [IsSimpleGroup R] in
theorem card_suppSub [Finite R] (S : Finset ι) :
    Nat.card (suppSub (R := R) (S : Set ι)) = Nat.card R ^ S.card := by
  have e : suppSub (R := R) (S : Set ι) ≃ (S → R) :=
    { toFun := fun f i => (f : ι → R) i
      invFun := fun g => ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 1, by
        intro j hj
        have : j ∉ S := hj
        simp [this]⟩
      left_inv := by
        rintro ⟨f, hf⟩
        apply Subtype.ext
        funext i
        by_cases h : i ∈ S
        · simp [h]
        · simp [h, hf i h]
      right_inv := by
        intro g
        funext i
        simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

open Classical in
include hR in
/-- **[DiM, Thm. 4.3A (iii)]**: a normal subgroup of `R^ι` is the product of the coordinate
subgroups it contains, so its order is a power of `|R|`. -/
theorem normal_eq_suppSub (Y : Subgroup (ι → R)) [Y.Normal] :
    Y = suppSub ((Finset.univ.filter fun i => coord (R := R) i ≤ Y : Finset ι) : Set ι) := by
  ext f
  constructor
  · intro hf j hj
    by_contra hfj
    apply hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact coord_le_of_normal hR Y hf hfj
  · intro hf
    refine mem_of_coord_le Y (Finset.univ.filter fun i => coord (R := R) i ≤ Y) ?_ f ?_
    · intro i hi
      exact (Finset.mem_filter.1 hi).2
    · intro i hi
      exact hf i (by simpa using hi)

end NormalCard

end ONS

end Babai
