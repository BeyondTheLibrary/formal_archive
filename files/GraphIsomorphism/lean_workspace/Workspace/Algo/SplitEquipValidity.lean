import Workspace.Algo.SplitEquipRead
import Workspace.SplitOrJohnson.HintBuild

/-! Section 9.7 retains an equipartition hint when the selected refined
color class is large. Admissibility excludes singleton blocks, and the
alpha bound excludes a single block covering the selected class. -/
namespace Babai.ColoredPartition

noncomputable def equipNat {V : Type} (P : ColoredPartition V ℕ) (x : V) : ℕ :=
  Nat.pair (P.color x) ((P.block x).ncard)

theorem equipNat_eq_iff {V : Type} (P : ColoredPartition V ℕ) (x y : V) :
    P.equipNat x = P.equipNat y ↔
      P.color x = P.color y ∧ (P.block x).ncard = (P.block y).ncard := by
  simp [equipNat,Nat.pair_eq_pair]

open scoped Classical in
theorem large_equipClass_structure {V : Type} [Fintype V] (P : ColoredPartition V ℕ)
    (k : ℕ) (hP : P.IsAlphaPartition (3 / 4))
    (hcard : 4 ≤ Fintype.card V)
    (hbig : 3 * Fintype.card V < 4 * (colorClassOf P.equipNat k).ncard) :
    ∃ Z : PartitionStructure ↥(colorClassOf P.equipNat k),
      Z.IsCoherent ∧ Z.IsHomogeneous ∧ Z.rank = 3 ∧
      ∀ x y, Z.natColor x y = if x = y then 0 else if P.part x.val y.val then 1 else 2 := by
  classical
  let S := colorClassOf P.equipNat k
  letI : Fintype ↥S := Fintype.ofFinite _
  change 3 * Fintype.card V < 4 * S.ncard at hbig
  let m := (Nat.unpair k).2
  have hm : ∀ x ∈ S, (P.block x).ncard = m := by
    intro x hx
    change P.equipNat x = k at hx
    simp only [m,← hx,equipNat,Nat.unpair_pair]
  have hcol : ∀ x ∈ S, ∀ y ∈ S, P.color x = P.color y := by
    intro x hx y hy
    exact (P.equipNat_eq_iff x y).mp (hx.trans hy.symm) |>.1
  have hsub : ∀ x ∈ S, P.block x ⊆ S := by
    intro x hx y hy
    change P.equipNat y = k
    rw [← show P.equipNat x = k from hx]
    exact (P.equipNat_eq_iff y x).mpr ⟨P.part_le_color hy,congrArg Set.ncard (P.block_eq_of_part hy)⟩
  have hS : 4 ≤ S.ncard := by omega
  obtain ⟨x₀,hx₀⟩ : S.Nonempty := (Set.ncard_pos).mp (by omega)
  have h2 : 2 ≤ m := by
    rw [← hm x₀ hx₀]
    apply hP.1 x₀
    have hle := Set.ncard_le_ncard (show S ⊆ P.colorClass (P.color x₀) from
      fun y hy => hcol y hy x₀ hx₀) (Set.toFinite _)
    omega
  have hrho : 4 * P.rho ≤ 3 * Fintype.card V := by
    have hh := hP.2
    have : (4 : ℝ) * P.rho ≤ 3 * Fintype.card V := by linarith
    exact_mod_cast this
  have hmr : m ≤ P.rho := by rw [← hm x₀ hx₀]; exact P.ncard_block_le_rho x₀
  have hlt : m < Fintype.card ↥S := by
    have hh : Fintype.card ↥S = S.ncard := by
      rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rw [hh]
    omega
  let R : ↥S → ↥S → Prop := fun x y => P.part x.val y.val
  have hR : Equivalence R :=
    ⟨fun _ => P.part.refl _,fun hh => P.part.symm hh,fun ha hb => P.part.trans ha hb⟩
  have hc : ∀ x : ↥S, {y : ↥S | R x y}.ncard = m := by
    intro x
    have he : Subtype.val '' {y : ↥S | R x y} = P.block x.val := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact P.part.symm hz
      · intro hy
        exact ⟨⟨y,hsub x.val x.property hy⟩,P.part.symm hy,rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective,he,hm x.val x.property]
  refine ⟨eqvConfig hR hc h2 hlt,eqvConfig_isCoherent _ _ _ _,
    eqvConfig_isHomogeneous _ _ _ _,rfl,?_⟩
  intro x y
  change ((eqvColor R x y : Fin 3) : ℕ) = _
  unfold eqvColor
  split_ifs <;> rfl

end Babai.ColoredPartition

namespace Algo
open Babai

def rawEquipFirstSet (P : RawColPart) : Set (Fin P.1.length) :=
  {i | i.val ∈ rawEquipFirst P}

open scoped Classical in
theorem rawEquipFirstSet_eq (P : RawColPart) (hn : 0 < P.1.length) :
    rawEquipFirstSet P = colorSplit (decColPartition P.1.length P).equipNat := by
  ext i
  exact rawEquipFirst_spec P hn i

theorem rawEquipFirstEquiv_exists (P : RawColPart) :
    ∃ e : ↥(rawEquipFirstSet P) ≃ Fin (rawEquipFirst P).length,
      ∀ x, (rawEquipFirst P)[(e x).val] = x.val.val := by
  apply splitNameEquiv_exists (fun x : ↥(rawEquipFirstSet P) => x.val.val)
    (fun x y hh => Subtype.ext (Fin.ext hh)) _ (rawEquipFirst_nodup P)
  intro i
  exact ⟨fun hi => ⟨⟨⟨i,rawEquipFirst_lt hi⟩,hi⟩,rfl⟩,
    fun ⟨x,hx⟩ => hx ▸ x.property⟩

theorem rawEquipFirstSet_ncard (P : RawColPart) :
    (rawEquipFirstSet P).ncard = (rawEquipFirst P).length := by
  obtain ⟨e,_⟩ := rawEquipFirstEquiv_exists P
  simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_congr e

open scoped Classical in
theorem rawEquipFirst_quarter (P : RawColPart) (hn : 0 < P.1.length) :
    P.1.length ≤ 4 * (rawEquipFirst P).length := by
  have hc := card_le_four_mul_colorSplit (decColPartition P.1.length P).equipNat
  simpa only [← rawEquipFirstSet_eq P hn,rawEquipFirstSet_ncard,Fintype.card_fin] using hc

open scoped Classical in
theorem rawEquipFirst_structure (P : RawColPart)
    (hP : (decColPartition P.1.length P).IsAlphaPartition (3 / 4))
    (hn : 4 ≤ P.1.length) (hbig : 3 * P.1.length < 4 * (rawEquipFirstSet P).ncard) :
    ∃ Z : PartitionStructure ↥(rawEquipFirstSet P),
      Z.IsCoherent ∧ Z.IsHomogeneous ∧ Z.rank = 3 ∧
      ∀ x y, rawEquipHintAt (P,(x.val.val,y.val.val)) = Z.natColor x y := by
  classical
  let Q := decColPartition P.1.length P
  have hA := rawEquipFirstSet_eq P (by omega)
  rcases colorSplit_alternative Q.equipNat with hsmall | ⟨k,hk⟩
  · rw [← hA,Fintype.card_fin] at hsmall
    omega
  · have hS : rawEquipFirstSet P = colorClassOf Q.equipNat k := hA.trans hk
    obtain ⟨Z,hco,hhom,hrank,hcol⟩ := Q.large_equipClass_structure k hP
      (by simpa using hn) (by simpa only [← hS,Fintype.card_fin] using hbig)
    let e : ↥(colorClassOf Q.equipNat k) ≃ ↥(rawEquipFirstSet P) := Equiv.setCongr hS.symm
    refine ⟨Z.transport e,PartitionStructure.transport_isCoherent _ hco,
      PartitionStructure.transport_isHomogeneous _ hhom,hrank,?_⟩
    intro x y
    change rawEquipHintAt (P,(x.val.val,y.val.val)) = Z.natColor (e.symm x) (e.symm y)
    rw [rawEquipHintAt_spec P x.val y.val x.property y.property,hcol]
    have heq : e.symm x = e.symm y ↔ x.val = y.val :=
      e.symm.injective.eq_iff.trans Subtype.val_inj.symm
    have hp : Q.part (e.symm x).val (e.symm y).val ↔ Q.part x.val y.val := Iff.rfl
    simp only [heq,hp]

end Algo
