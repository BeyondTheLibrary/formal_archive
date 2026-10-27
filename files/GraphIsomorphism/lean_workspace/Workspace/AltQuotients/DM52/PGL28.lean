/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: the group `PΓL(2,8)` on nine points.
-/
import Workspace.AltQuotients.DM52.OrbitTools
import Workspace.AltQuotients.NamedGroups
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# `PΓL(2,8)` as a group of permutations of nine points

The exceptional group of degree `9` in [DiM, Thm. 5.2A (iii)(b)] is `PΓL₂(8)`, the group of
permutations of the projective line `ℙ¹(F₈)` induced by the semilinear bijections of `F₈²`
(`Babai.PGammaL_2_8`).  We number the nine points: for a root `α` of `X³ + X + 1`, the point
`i < 7` is `α^i`, the point `7` is `0`, and the point `8` is `∞`; this gives the model
`M9 ≤ Sym(9)`, isomorphic to `PΓL₂(8)`.

We show that `M9` contains the permutations `x ↦ αx`, `x ↦ x²`, `x ↦ 1/x` and `x ↦ x + 1`,
and that `|M9| ≤ 9 · 8 · 7 · 3 = 1512`: an element fixing `∞, 0, 1` is induced by a semilinear
map fixing the three lines, which is a scalar times a field automorphism of `F₈`, and there
are three of these (the image of `α` is a root of `X³ + X + 1`).

To compute in `F₈` we use a concrete copy `F8c` of the field with eight elements, given by
its operation tables (so that its identities can be checked by evaluation), and an
isomorphism `φ8 : F8c ≃+* F₈` (any two fields with eight elements are isomorphic).
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Subgroup
open scoped Matrix

/-! ### A concrete field with eight elements -/

/-- Addition table: the element `k < 7` is `α^k`, and `7` is `0`. -/
def addT8 : Fin 8 → Fin 8 → Fin 8 :=
  ![![7, 3, 6, 1, 5, 4, 2, 0], ![3, 7, 4, 0, 2, 6, 5, 1], ![6, 4, 7, 5, 1, 3, 0, 2],
    ![1, 0, 5, 7, 6, 2, 4, 3], ![5, 2, 1, 6, 7, 0, 3, 4], ![4, 6, 3, 2, 0, 7, 1, 5],
    ![2, 5, 0, 4, 3, 1, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]

/-- Multiplication table: `α^i α^j = α^(i+j)`. -/
def mulT8 (i j : Fin 8) : Fin 8 :=
  if i = 7 ∨ j = 7 then 7 else ⟨(i.val + j.val) % 7, by omega⟩

/-- Inverse table. -/
def invT8 : Fin 8 → Fin 8 := ![0, 6, 5, 4, 3, 2, 1, 7]

/-- A concrete field with eight elements: `⟨k⟩` stands for `α^k` (`k < 7`) and `⟨7⟩` for `0`,
where `α³ = α + 1`. -/
structure F8c where
  /-- The code of the element. -/
  val : Fin 8
  deriving DecidableEq

/-- `F8c ≃ Fin 8`. -/
def F8c.equivFin : F8c ≃ Fin 8 := ⟨F8c.val, F8c.mk, fun _ => rfl, fun _ => rfl⟩

instance : Fintype F8c := Fintype.ofEquiv (Fin 8) F8c.equivFin.symm

instance : Zero F8c := ⟨⟨7⟩⟩
instance : One F8c := ⟨⟨0⟩⟩
instance : Add F8c := ⟨fun a b => ⟨addT8 a.val b.val⟩⟩
instance : Mul F8c := ⟨fun a b => ⟨mulT8 a.val b.val⟩⟩
instance : Neg F8c := ⟨fun a => a⟩
instance : Sub F8c := ⟨fun a b => a + b⟩
instance : Inv F8c := ⟨fun a => ⟨invT8 a.val⟩⟩
instance : Div F8c := ⟨fun a b => a * b⁻¹⟩

instance : Field F8c where
  add_assoc := by decide +kernel
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
  neg_add_cancel := by decide +kernel
  add_comm := by decide +kernel
  left_distrib := by decide +kernel
  right_distrib := by decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  mul_comm := by decide +kernel
  sub_eq_add_neg := by decide +kernel
  exists_pair_ne := ⟨0, 1, by decide +kernel⟩
  mul_inv_cancel := by decide +kernel
  inv_zero := by decide +kernel
  div_eq_mul_inv := by decide +kernel
  nnqsmul := _
  qsmul := _

theorem card_F8c : Fintype.card F8c = 8 := rfl

/-- The element `α`. -/
def aC : F8c := ⟨1⟩

/-- Frobenius table `α^i ↦ α^(2i)`, and its inverse `α^i ↦ α^(4i)`. -/
def frobT8 : Fin 8 → Fin 8 := ![0, 2, 4, 6, 1, 3, 5, 7]
/-- The inverse of `frobT8`. -/
def frobInvT8 : Fin 8 → Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7]

/-- The Frobenius automorphism `x ↦ x²` of `F8c`. -/
def frobC : F8c ≃+* F8c where
  toFun a := ⟨frobT8 a.val⟩
  invFun a := ⟨frobInvT8 a.val⟩
  left_inv a := by revert a; decide +kernel
  right_inv a := by revert a; decide +kernel
  map_mul' := by decide +kernel
  map_add' := by decide +kernel

/-! ### The isomorphism with `F₈` -/

noncomputable instance : Fintype F8 := Fintype.ofFinite F8

theorem card_F8 : Fintype.card F8 = 8 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
  norm_num

/-- An isomorphism `F8c ≃+* F₈`. -/
noncomputable def φ8 : F8c ≃+* F8 :=
  FiniteField.ringEquivOfCardEq (K := F8c) (K' := F8) (by rw [card_F8, card_F8c])

/-! ### The nine points -/

/-- The chosen vector of the point `i`, over `F8c`: `(α^i, 1)` for `i < 7`, `(0, 1)` for `7`,
and `(1, 0)` for `8`. -/
def repC (i : Fin 9) : Fin 2 → F8c :=
  if h : (i : ℕ) < 8 then ![⟨⟨i, h⟩⟩, 1] else ![1, 0]

theorem repC_ne_zero : ∀ i, repC i ≠ 0 := by decide +kernel

/-- The chosen vector of the point `i`, over `F₈`. -/
noncomputable def rep9 (i : Fin 9) : Fin 2 → F8 := fun s => φ8 (repC i s)

theorem rep9_ne_zero (i : Fin 9) : rep9 i ≠ 0 := by
  intro h
  apply repC_ne_zero i
  funext s
  have := congrFun h s
  simpa [rep9] using this

/-- The point `i` of the projective line. -/
noncomputable def pt9 (i : Fin 9) : Projectivization F8 (Fin 2 → F8) :=
  Projectivization.mk F8 (rep9 i) (rep9_ne_zero i)

theorem repC_proportional : ∀ i j : Fin 9, (∃ c : F8c, c • repC j = repC i) → i = j := by
  decide +kernel

/-- Proportional vectors over `F₈` come from proportional vectors over `F8c`. -/
theorem pt9_eq_iff (i j : Fin 9) : pt9 i = pt9 j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F8 _ _ _ _).mp h
  apply repC_proportional
  refine ⟨φ8.symm c, funext fun s => ?_⟩
  have := congrFun hc s
  simp only [rep9, Pi.smul_apply, smul_eq_mul] at this
  apply φ8.injective
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  exact this

theorem card_projLine : Nat.card (Projectivization F8 (Fin 2 → F8)) = 9 := by
  rw [Projectivization.card_of_finrank_two F8 (Fin 2 → F8) (Module.finrank_fin_fun F8),
    Nat.card_eq_fintype_card, card_F8]

/-- The numbering of the nine points. -/
noncomputable def e9 : Fin 9 ≃ Projectivization F8 (Fin 2 → F8) :=
  Equiv.ofBijective pt9 (Function.Injective.bijective_of_nat_card_le (f := pt9)
    (fun i j h => (pt9_eq_iff i j).mp h)
    (by rw [card_projLine, Nat.card_eq_fintype_card, Fintype.card_fin]))

theorem e9_apply (i : Fin 9) : e9 i = pt9 i := rfl

/-- The model of `PΓL₂(8)` on `Fin 9`. -/
noncomputable def M9 : Subgroup (Perm (Fin 9)) := relabel e9.symm PGammaL_2_8

/-- `M9 ≃* PΓL₂(8)`. -/
noncomputable def M9_mulEquiv : M9 ≃* PGammaL_2_8 := (relabelEquiv e9.symm PGammaL_2_8).symm

theorem mem_M9_iff (g : Perm (Fin 9)) : g ∈ M9 ↔ e9.permCongr g ∈ PGammaL_2_8 := by
  rw [M9, mem_relabel, Equiv.symm_symm]

theorem permCongr_e9_pt9 (g : Perm (Fin 9)) (i : Fin 9) : e9.permCongr g (pt9 i) = pt9 (g i) := by
  rw [Equiv.permCongr_apply, ← e9_apply, Equiv.symm_apply_apply, e9_apply]

/-! ### Semilinear maps given by tables -/

section Table

variable (τ : F8c ≃+* F8c) (A B : Matrix (Fin 2) (Fin 2) F8c)

/-- The field automorphism `φ8 τ φ8⁻¹` of `F₈`. -/
noncomputable def σOf : F8 ≃+* F8 := φ8.symm.trans (τ.trans φ8)

theorem σOf_φ8 (x : F8c) : σOf τ (φ8 x) = φ8 (τ x) := by simp [σOf]

/-- The `σ`-semilinear map `v ↦ A (σ v)` of `F₈²`, with inverse `v ↦ σ⁻¹ (B v)`. -/
noncomputable def semiMap (hAB : A * B = 1) (hBA : B * A = 1) :
    (Fin 2 → F8) ≃+ (Fin 2 → F8) where
  toFun v := (A.map φ8) *ᵥ (fun s => σOf τ (v s))
  invFun v := fun s => (σOf τ).symm (((B.map φ8) *ᵥ v) s)
  left_inv v := by
    funext s
    have hBA' : B.map φ8 * A.map φ8 = 1 := by
      rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero φ8) (map_one φ8)]
    simp only [Matrix.mulVec_mulVec, hBA', Matrix.one_mulVec, RingEquiv.symm_apply_apply]
  right_inv v := by
    funext s
    have hAB' : A.map φ8 * B.map φ8 = 1 := by
      rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero φ8) (map_one φ8)]
    simp only [RingEquiv.apply_symm_apply]
    rw [show (fun s => ((B.map φ8) *ᵥ v) s) = (B.map φ8) *ᵥ v from rfl,
      Matrix.mulVec_mulVec, hAB', Matrix.one_mulVec]
  map_add' v w := by
    simp only [Pi.add_apply, map_add]
    rw [← Matrix.mulVec_add]
    rfl

theorem semiMap_smul (hAB : A * B = 1) (hBA : B * A = 1) (c : F8) (v : Fin 2 → F8) :
    semiMap τ A B hAB hBA (c • v) = σOf τ c • semiMap τ A B hAB hBA v := by
  show (A.map φ8) *ᵥ (fun s => σOf τ ((c • v) s)) = σOf τ c • (A.map φ8) *ᵥ _
  rw [← Matrix.mulVec_smul]
  congr 1
  funext s
  simp [map_mul]

theorem semiMap_rep9 (hAB : A * B = 1) (hBA : B * A = 1) (i : Fin 9) :
    semiMap τ A B hAB hBA (rep9 i) = fun s => φ8 ((A *ᵥ (fun t => τ (repC i t))) s) := by
  funext s
  show ((A.map φ8) *ᵥ (fun t => σOf τ (rep9 i t))) s = _
  simp only [rep9, σOf_φ8]
  rw [show (fun t => φ8 (τ (repC i t))) = φ8.toRingHom ∘ (fun t => τ (repC i t)) from rfl,
    show A.map φ8 = A.map φ8.toRingHom from rfl, ← RingHom.map_mulVec]
  rfl

/-- A permutation of the nine points given by a semilinear table lies in `M9`. -/
theorem mem_M9_of_table (hAB : A * B = 1) (hBA : B * A = 1) (g : Perm (Fin 9))
    (h : ∀ i, ∃ c : F8c, A *ᵥ (fun t => τ (repC i t)) = c • repC (g i)) : g ∈ M9 := by
  rw [mem_M9_iff]
  apply Subgroup.subset_closure
  refine ⟨σOf τ, semiMap τ A B hAB hBA, semiMap_smul τ A B hAB hBA, fun v hv hfv => ?_⟩
  -- `v` represents the point `i`
  set i := e9.symm (Projectivization.mk F8 v hv) with hi
  have hvi : Projectivization.mk F8 v hv = pt9 i := by rw [← e9_apply, hi, e9.apply_symm_apply]
  obtain ⟨d, hd⟩ := (Projectivization.mk_eq_mk_iff' F8 _ _ _ _).mp hvi
  rw [hvi, permCongr_e9_pt9]
  obtain ⟨c, hc⟩ := h i
  refine ((Projectivization.mk_eq_mk_iff' F8 _ _ _ _).mpr ⟨σOf τ d * φ8 c, ?_⟩).symm
  rw [← hd, semiMap_smul, semiMap_rep9, hc]
  funext s
  simp [rep9, map_mul, mul_assoc]

end Table

/-! ### The generators -/

/-- `x ↦ αx`. -/
def c9 : Perm (Fin 9) := ofVec ![1, 2, 3, 4, 5, 6, 0, 7, 8] ![6, 0, 1, 2, 3, 4, 5, 7, 8] (by decide)
/-- `x ↦ x²`. -/
def mu9 : Perm (Fin 9) := ofVec ![0, 2, 4, 6, 1, 3, 5, 7, 8] ![0, 4, 1, 5, 2, 6, 3, 7, 8] (by decide)
/-- `x ↦ 1/x`. -/
def io9 : Perm (Fin 9) := ofVec ![0, 6, 5, 4, 3, 2, 1, 8, 7] ![0, 6, 5, 4, 3, 2, 1, 8, 7] (by decide)
/-- `x ↦ x + 1`. -/
def t9 : Perm (Fin 9) := ofVec ![7, 3, 6, 1, 5, 4, 2, 0, 8] ![7, 3, 6, 1, 5, 4, 2, 0, 8] (by decide)

theorem c9_mem_M9 : c9 ∈ M9 :=
  mem_M9_of_table (RingEquiv.refl F8c) !![aC, 0; 0, 1] !![aC⁻¹, 0; 0, 1]
    (by decide +kernel) (by decide +kernel) c9 (by decide +kernel)

theorem mu9_mem_M9 : mu9 ∈ M9 :=
  mem_M9_of_table frobC 1 1 (by decide +kernel) (by decide +kernel) mu9 (by decide +kernel)

theorem io9_mem_M9 : io9 ∈ M9 :=
  mem_M9_of_table (RingEquiv.refl F8c) !![0, 1; 1, 0] !![0, 1; 1, 0]
    (by decide +kernel) (by decide +kernel) io9 (by decide +kernel)

theorem t9_mem_M9 : t9 ∈ M9 :=
  mem_M9_of_table (RingEquiv.refl F8c) !![1, 1; 0, 1] !![1, 1; 0, 1]
    (by decide +kernel) (by decide +kernel) t9 (by decide +kernel)

/-! ### The order of `M9` -/

/-- The permutations of `ℙ¹(F₈)` induced by semilinear bijections (the generating set of
`PΓL₂(8)`). -/
def IsInduced (π : Perm (Projectivization F8 (Fin 2 → F8))) : Prop :=
  ∃ (σ : F8 ≃+* F8) (f : (Fin 2 → F8) ≃+ (Fin 2 → F8)),
    (∀ (c : F8) (v : Fin 2 → F8), f (c • v) = σ c • f v) ∧
      ∀ (v : Fin 2 → F8) (hv : v ≠ 0) (hfv : f v ≠ 0),
        π (Projectivization.mk F8 v hv) = Projectivization.mk F8 (f v) hfv

theorem addEquiv_ne_zero (f : (Fin 2 → F8) ≃+ (Fin 2 → F8)) {v : Fin 2 → F8} (hv : v ≠ 0) :
    f v ≠ 0 := fun h => hv (f.injective (h.trans (map_zero f).symm))

/-- The induced permutations form a group, so every element of `PΓL₂(8)` is induced. -/
theorem isInduced_of_mem {π : Perm (Projectivization F8 (Fin 2 → F8))}
    (hπ : π ∈ PGammaL_2_8) : IsInduced π := by
  induction hπ using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨RingEquiv.refl F8, AddEquiv.refl _, fun c v => rfl, fun v hv hfv => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨σ₁, f₁, h₁, k₁⟩ := hx
    obtain ⟨σ₂, f₂, h₂, k₂⟩ := hy
    refine ⟨σ₂.trans σ₁, f₂.trans f₁, fun c v => ?_, fun v hv hfv => ?_⟩
    · simp [h₁, h₂]
    · rw [Perm.mul_apply, k₂ v hv (addEquiv_ne_zero f₂ hv), k₁]
      rfl
  | inv x _ hx =>
    obtain ⟨σ, f, h, k⟩ := hx
    refine ⟨σ.symm, f.symm, fun c v => ?_, fun v hv hfv => ?_⟩
    · apply f.injective
      rw [AddEquiv.apply_symm_apply, h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    · rw [Perm.inv_eq_iff_eq, k _ hfv (addEquiv_ne_zero f hfv)]
      congr 1
      exact (f.apply_symm_apply v).symm

/-- The point `i` of `Fin 9` sent by a field automorphism `τ` of `F8c`, given `r = τ α`. -/
def autPoint (r : F8c) (i : Fin 9) : Fin 9 :=
  if (i : ℕ) < 8 then
    (if (i : ℕ) = 7 then 7 else Fin.castSucc (r ^ (i : ℕ)).val)
  else 8

/-- The three field automorphisms of `F8c` act on the points as `1, mu9, mu9²`. -/
theorem autPoint_cases : ∀ r : F8c, r ^ 3 + r + 1 = 0 →
    (∀ i, autPoint r i = i) ∨ (∀ i, autPoint r i = mu9 i) ∨ (∀ i, autPoint r i = (mu9 ^ 2) i) := by
  decide +kernel

theorem code_eq_pow : ∀ j : Fin 7, (⟨Fin.castSucc j⟩ : F8c) = aC ^ (j : ℕ) := by decide +kernel

theorem aC_cubic : aC ^ 3 + aC + 1 = 0 := by decide +kernel

theorem repC_castSucc (j : Fin 8) : repC (Fin.castSucc j) = ![⟨j⟩, 1] := by
  simp [repC, Fin.castSucc]

theorem repC_eq_smul_add : ∀ j : Fin 8,
    repC (Fin.castSucc j) = (⟨j⟩ : F8c) • repC 8 + repC 7 := by decide +kernel

theorem repC_zero_eq : repC 0 = repC 8 + repC 7 := by decide +kernel

/-- An element of `M9` fixing `∞ = 8`, `0 = 7` and `1 = 0` is `1`, `mu9` or `mu9²`. -/
theorem M9_stab_three {g : Perm (Fin 9)} (hg : g ∈ M9) (h8 : g 8 = 8) (h7 : g 7 = 7)
    (h0 : g 0 = 0) : g = 1 ∨ g = mu9 ∨ g = mu9 ^ 2 := by
  rw [mem_M9_iff] at hg
  obtain ⟨σ, f, hf, hk⟩ := isInduced_of_mem hg
  -- `f` maps the chosen vector of a fixed point `i` to a multiple of itself
  have hfix : ∀ i, g i = i → ∃ a : F8, f (rep9 i) = a • rep9 i := by
    intro i hi
    have := hk (rep9 i) (rep9_ne_zero i) (addEquiv_ne_zero f (rep9_ne_zero i))
    rw [show Projectivization.mk F8 (rep9 i) (rep9_ne_zero i) = pt9 i from rfl,
      permCongr_e9_pt9, hi] at this
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F8 _ _ _ _).mp this.symm
    exact ⟨a, ha.symm⟩
  obtain ⟨a8, ha8⟩ := hfix 8 h8
  obtain ⟨a7, ha7⟩ := hfix 7 h7
  obtain ⟨a0, ha0⟩ := hfix 0 h0
  -- the three scalars agree
  have hrep : ∀ i, rep9 i = fun s => φ8 (repC i s) := fun i => rfl
  have hr0 : rep9 0 = rep9 8 + rep9 7 := by
    funext s; simp [hrep, repC_zero_eq, map_add]
  have h87 : rep9 8 0 = 1 ∧ rep9 8 1 = 0 ∧ rep9 7 0 = 0 ∧ rep9 7 1 = 1 := by
    simp only [hrep]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    [rw [show repC 8 0 = 1 by decide +kernel]; rw [show repC 8 1 = 0 by decide +kernel];
      rw [show repC 7 0 = 0 by decide +kernel]; rw [show repC 7 1 = 1 by decide +kernel]] <;>
    simp
  have hsum : f (rep9 0) = a8 • rep9 8 + a7 • rep9 7 := by rw [hr0, map_add, ha8, ha7]
  rw [ha0, hr0] at hsum
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h87.1, h87.2.1, h87.2.2.1,
    h87.2.2.2] at e0 e1
  have ha80 : a8 = a0 := by linear_combination -e0
  have ha70 : a7 = a0 := by linear_combination -e1
  -- the automorphism of `F8c` induced by `σ`
  set τ : F8c ≃+* F8c := φ8.trans (σ.trans φ8.symm) with hτ
  have hστ : ∀ x, σ (φ8 x) = φ8 (τ x) := fun x => by simp [hτ]
  -- the image of the point `j < 8`
  have hgj : ∀ j : Fin 8, g (Fin.castSucc j) = Fin.castSucc (τ ⟨j⟩).val := by
    intro j
    have hv : rep9 (Fin.castSucc j) = φ8 ⟨j⟩ • rep9 8 + rep9 7 := by
      funext s; simp [hrep, repC_eq_smul_add j, map_add, map_mul]
    have hfv : f (rep9 (Fin.castSucc j)) = a0 • rep9 (Fin.castSucc (τ ⟨j⟩).val) := by
      rw [hv, map_add, hf, ha8, ha7, ha80, ha70, smul_comm, ← smul_add, hστ]
      congr 1
      funext s; simp [hrep, repC_eq_smul_add (τ ⟨j⟩).val, map_add, map_mul]
    have := hk (rep9 (Fin.castSucc j)) (rep9_ne_zero _)
      (addEquiv_ne_zero f (rep9_ne_zero _))
    rw [show Projectivization.mk F8 (rep9 (Fin.castSucc j)) (rep9_ne_zero _) =
      pt9 (Fin.castSucc j) from rfl, permCongr_e9_pt9] at this
    have ha0' : a0 ≠ 0 := by
      intro h
      rw [h, zero_smul] at hfv
      exact addEquiv_ne_zero f (rep9_ne_zero _) hfv
    rw [← pt9_eq_iff, this]
    apply (Projectivization.mk_eq_mk_iff' F8 _ _ _ _).mpr
    exact ⟨a0, hfv.symm⟩
  -- `τ` is determined by `τ α`, a root of `X³ + X + 1`
  have hroot : τ aC ^ 3 + τ aC + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one τ, ← map_add, aC_cubic, map_zero]
  have hauto : ∀ i, g i = autPoint (τ aC) i := by
    intro i
    by_cases hi8 : (i : ℕ) < 8
    · obtain ⟨j, rfl⟩ : ∃ j : Fin 8, Fin.castSucc j = i := ⟨⟨i, hi8⟩, rfl⟩
      rw [hgj j]
      by_cases hj7 : (j : ℕ) = 7
      · have hj : j = 7 := Fin.ext hj7
        subst hj
        have : (⟨7⟩ : F8c) = 0 := rfl
        simp [autPoint, this]
        rfl
      · have hjlt : (j : ℕ) < 7 := by omega
        have := code_eq_pow ⟨j, hjlt⟩
        simp only [Fin.castSucc_mk] at this
        have hj' : (⟨j⟩ : F8c) = aC ^ (j : ℕ) := by
          rw [← this]
        simp [autPoint, hj7, hj', map_pow]
    · have hi : i = 8 := Fin.ext (by omega)
      subst hi
      simp [autPoint, h8]
  rcases autPoint_cases (τ aC) hroot with h | h | h
  · left; ext i; rw [hauto, h]; rfl
  · right; left; ext i; rw [hauto, h]
  · right; right; ext i; rw [hauto, h]

/-- `|M9| ≤ 9 · 8 · 7 · 3 = 1512`. -/
theorem card_M9_le : Nat.card M9 ≤ 1512 := by
  have b0 := card_le_card_mul_of_mapsTo M9 8 Finset.univ (fun g _ => Finset.mem_univ _)
  set X8 := (M9 ⊓ stabilizer (Perm (Fin 9)) (8 : Fin 9) : Subgroup _)
  have b1 := card_le_card_mul_of_mapsTo X8 7 (Finset.univ.erase 8) (fun g hg => by
    have h8 : g 8 = 8 := hg.2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; exact absurd (g.injective (h.trans h8.symm)) (by decide))
  set X87 := (X8 ⊓ stabilizer (Perm (Fin 9)) (7 : Fin 9) : Subgroup _)
  have b2 := card_le_card_mul_of_mapsTo X87 0 ((Finset.univ.erase 8).erase 7) (fun g hg => by
    have h8 : g 8 = 8 := hg.1.2
    have h7 : g 7 = 7 := hg.2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd (g.injective (h.trans h7.symm)) (by decide)
    · exact absurd (g.injective (h.trans h8.symm)) (by decide))
  have b3 : Nat.card (X87 ⊓ stabilizer (Perm (Fin 9)) (0 : Fin 9) : Subgroup _) ≤ 3 := by
    calc _ ≤ ({1, mu9, mu9 ^ 2} : Finset (Perm (Fin 9))).card := by
          apply card_le_of_subset_finset
          intro g hg
          rcases M9_stab_three hg.1.1.1 hg.1.1.2 hg.1.2 hg.2 with h | h | h <;> simp [h]
      _ ≤ 3 := Finset.card_le_three
  have e1 : (Finset.univ : Finset (Fin 9)).card = 9 := by decide
  have e2 : ((Finset.univ : Finset (Fin 9)).erase 8).card = 8 := by decide
  have e3 : (((Finset.univ : Finset (Fin 9)).erase 8).erase 7).card = 7 := by decide
  rw [e1] at b0
  rw [e2] at b1
  rw [e3] at b2
  calc Nat.card M9 ≤ 9 * Nat.card X8 := b0
    _ ≤ 9 * (8 * (7 * 3)) := by
      apply Nat.mul_le_mul_left
      exact b1.trans (Nat.mul_le_mul_left _ (b2.trans (Nat.mul_le_mul_left _ b3)))
    _ = 1512 := by norm_num

end Babai.DM52
