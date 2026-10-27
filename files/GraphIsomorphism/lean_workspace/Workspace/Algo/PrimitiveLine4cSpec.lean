import Workspace.Algo.PrimitiveLine4c
import Workspace.Algo.TopFourPrimitive

/-! # Section 15, line 4c on the RAM: the computed structure is the paper's

The machine's structure of `H(z)` has one relation per entry of the palette
(`line4cPalette`), the relation of the color `a` being the injective `t`-tuples whose
`t`-set has color `a` (`Babai.hyperRel`). This file proves the two facts line 4c needs of it:

* **its automorphism group is `Aut(H(z))`** (`aut_line4c`) as soon as the palette lists every
  color of `H(z)`, which it does for `z = x` and `z = y`; so the relative symmetry defect of
  the structure is the one line 4b tested, and the structure is an admitted input of
  Theorem 9.2.3 exactly when line 4b failed (`extendedInputRep_line4c`);
* **a `G`-shift of the string moves the structure** by the corresponding permutation of `Γ`
  (`IsPaletteStruct.iso`), relation by relation, for every palette.
-/

namespace Algo
open Babai RAM Equiv

/-! ### Structures read off a palette -/

section Palette

variable {Γ : Type*} [DecidableEq Γ] {A : Type*} {t : ℕ}

/-- The relations of a `t`-tuple moved by `σ` are those of the tuple in the shifted
coloring `H ∘ σ^{(t)}`. -/
theorem tupleMap_mem_hyperRel (H : binom Γ t → A) (σ : Perm Γ) (v : Fin t → Γ) (a : A) :
    tupleMap (σ : Γ → Γ) v ∈ hyperRel t H a ↔
      v ∈ hyperRel t (fun s => H (tAction t σ s)) a := by
  have he : edgeOf (tupleMap (σ : Γ → Γ) v) = (edgeOf v).image σ := edgeOf_tupleMap _ v
  have hcard : (edgeOf (tupleMap (σ : Γ → Γ) v)).card = (edgeOf v).card := by
    rw [he, Finset.card_image_of_injective _ σ.injective]
  constructor
  · rintro ⟨hc, hcol⟩
    have hv : (edgeOf v).card = t := hcard ▸ hc
    refine ⟨hv, ?_⟩
    have hs : tAction t σ ⟨edgeOf v, hv⟩ = ⟨edgeOf (tupleMap (σ : Γ → Γ) v), hc⟩ :=
      Subtype.ext (by rw [tAction_apply_coe]; exact he.symm)
    change H (tAction t σ ⟨edgeOf v, hv⟩) = a
    rw [hs]
    exact hcol
  · rintro ⟨hv, hcol⟩
    have hc : (edgeOf (tupleMap (σ : Γ → Γ) v)).card = t := hcard.trans hv
    refine ⟨hc, ?_⟩
    have hs : tAction t σ ⟨edgeOf v, hv⟩ = ⟨edgeOf (tupleMap (σ : Γ → Γ) v), hc⟩ :=
      Subtype.ext (by rw [tAction_apply_coe]; exact he.symm)
    rw [← hs]
    exact hcol

/-- Every `t`-set is the set of entries of an injective `t`-tuple. -/
theorem exists_edgeOf_eq (s : binom Γ t) :
    ∃ (v : Fin t → Γ) (h : (edgeOf v).card = t), (⟨edgeOf v, h⟩ : binom Γ t) = s := by
  obtain ⟨s, hs⟩ := s
  let w : Fin t ≃ ↥(s : Finset Γ) := (finCongr hs.symm).trans s.equivFin.symm
  let v : Fin t → Γ := fun i => ((w i : ↥(s : Finset Γ)) : Γ)
  have hinj : Function.Injective v := fun i j hij => w.injective (Subtype.ext hij)
  have hc : (edgeOf v).card = t := by
    rw [edgeOf, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine ⟨v, hc, Subtype.ext ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [edgeOf, Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact (w i).2
  · change s.card ≤ (edgeOf v).card
    omega

variable {C : Type*}

/-- A `t`-ary structure whose relation `i` is the relation of the color `P[i]` of `H` for
`i` below the length of the palette `P`, and empty beyond it. -/
def IsPaletteStruct (R : KAryRelStruct Γ ℕ t) (H : binom Γ t → A) (P : List A) : Prop :=
  ∀ (i : ℕ) (v : Fin t → Γ), v ∈ R.rel i ↔ ∃ h : i < P.length, v ∈ hyperRel t H P[i]

/-- **The structure moves with the coloring**: if the coloring of the second structure is
the first shifted by `π`, then `π` is an isomorphism, for every palette. -/
theorem IsPaletteStruct.iso {R R' : KAryRelStruct Γ ℕ t} {H : binom Γ t → A} {P : List A}
    (hR : IsPaletteStruct R H P) (π : Perm Γ)
    (hR' : IsPaletteStruct R' (fun s => H (tAction t π⁻¹ s)) P) :
    π ∈ KAryRelStruct.Iso R R' := by
  intro i v
  rw [hR, hR']
  refine exists_congr fun _ => ?_
  rw [tupleMap_mem_hyperRel]
  have hH : (fun s => H (tAction t π⁻¹ (tAction t π s))) = H :=
    funext fun s => by rw [tAction_inv_apply]
  simp only [hH]

/-- **The automorphism group is `Aut(H)`** when the palette lists every color of `H`. -/
theorem IsPaletteStruct.aut_eq {R : KAryRelStruct Γ ℕ t} {H : binom Γ t → A} {P : List A}
    (hR : IsPaletteStruct R H P) (hP : ∀ s, H s ∈ P) : R.Aut = colorAut t H := by
  ext σ
  rw [KAryRelStruct.mem_Aut, mem_colorAut]
  constructor
  · intro h s
    obtain ⟨v, hv, rfl⟩ := exists_edgeOf_eq s
    obtain ⟨i, hi, hPi⟩ := List.mem_iff_getElem.1 (hP ⟨edgeOf v, hv⟩)
    have hmem : v ∈ R.rel i := (hR i v).2 ⟨hi, hv, hPi.symm⟩
    obtain ⟨_, hmem'⟩ := (hR i _).1 ((h i v).1 hmem)
    obtain ⟨hv', hcol⟩ := (tupleMap_mem_hyperRel H σ v _).1 hmem'
    rw [hPi] at hcol
    exact hcol
  · intro h i v
    rw [hR, hR]
    refine exists_congr fun _ => ?_
    rw [tupleMap_mem_hyperRel]
    have hH : (fun s => H (tAction t σ s)) = H := funext h
    rw [hH]

end Palette

/-! ### The machine's structure -/

section Machine

variable {n m t : ℕ} {p : RawAction} {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2))) (id : PrimitiveCaseId ϕ t)

include hp id in
theorem line4cArity_length (x y : RawStr) : (line4cArity ((p, x, y), t)).length = t := by
  have h4 := id.four_t
  rw [Fintype.card_fin] at h4
  simp only [line4cArity, List.length_range, hp.2.1]
  omega

include hp hϕ hk in
/-- **Line 4c: the machine's structure of `H(z)` is read off the palette.** -/
theorem isPaletteStruct_line4c (x y z : RawStr) :
    IsPaletteStruct (decRel m t (line4cAmbient (((p, x, y), t), z)).1.2)
      (hyperColoring id (decStrN n z)) (line4cPalette (p, x, y)) := by
  have hlen := line4cArity_length hp id x y
  intro i v
  by_cases hi : i < (line4cPalette (p, x, y)).length
  · have h := primitiveRelations_index_spec (c := 1) hp.1 hp.2.1 hp.2.2.2.2 hϕ hk id z
      (line4cArity ((p, x, y), t)) (line4cPalette (p, x, y)) hlen
      (by rw [hlen, hp.1]; exact primitiveCase_arity_guard id) i hi v
    simp only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1, Prod.mk.eta] at h
    change v ∈ (decRel m t (primitiveRelations 1 (((p, z), line4cArity ((p, x, y), t)),
      line4cPalette (p, x, y)))).rel i ↔ _
    rw [h]
    exact ⟨fun hv => ⟨hi, hv⟩, fun ⟨_, hv⟩ => hv⟩
  · constructor
    · intro hv
      change tupleOf v ∈ (primitiveRelations 1 _).getD i [] at hv
      rw [getD_of_length_le (by simp only [length_primitiveRelations]; omega)] at hv
      simp at hv
    · rintro ⟨hi', _⟩
      exact absurd hi' hi

/-- The palette lists every letter of the two strings, and the letter `0`. -/
theorem getD_mem_line4cPalette (x y : RawStr) (u : ℕ) :
    x.getD u 0 ∈ line4cPalette (p, x, y) ∧ y.getD u 0 ∈ line4cPalette (p, x, y) := by
  have hmem : ∀ l : RawStr, l.getD u 0 ∈ 0 :: l := by
    intro l
    rw [List.getD_eq_getElem?_getD]
    cases h : l[u]? with
    | none => simp
    | some a => exact List.mem_cons_of_mem _ (List.mem_of_getElem? h)
  refine ⟨?_, ?_⟩
  · rcases List.mem_cons.1 (hmem x) with h | h
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  · rcases List.mem_cons.1 (hmem y) with h | h
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

include hp hϕ hk in
/-- **The automorphism group of the machine's structure of `H(z)` is `Aut(H(z))`**, for
`z = x` and `z = y`. -/
theorem aut_line4c (x y z : RawStr) (hz : z = x ∨ z = y) :
    (decRel m t (line4cAmbient (((p, x, y), t), z)).1.2).Aut =
      colorAut t (hyperColoring id (decStrN n z)) := by
  refine (isPaletteStruct_line4c hp hϕ hk id x y z).aut_eq fun s => ?_
  change z.getD (id.label.symm s : ℕ) 0 ∈ _
  rcases hz with rfl | rfl
  · exact (getD_mem_line4cPalette _ _ _).1
  · exact (getD_mem_line4cPalette _ _ _).2

include hp hϕ hk in
/-- **Line 4c: the structure is an admitted input of Theorem 9.2.3** exactly when the paper
applies Theorem 9.2.3 to it: `t ≥ 2` (line 4b's *"else"*) and a relative symmetry defect
of `H(z)` of at least `1/2` (line 4c's *"now their relative symmetry defect is `≥ 1/2`"*). -/
theorem extendedInputRep_line4c (x y z : RawStr) (hz : z = x ∨ z = y) (ht : 2 ≤ t)
    (hdef : ¬ defect (colorAut t (hyperColoring id (decStrN n z))) < 1 / 2) :
    ExtendedInputRep 1 m (line4cAmbient (((p, x, y), t), z)) := by
  have hlen := line4cArity_length hp id x y
  have h4 := id.four_t
  rw [Fintype.card_fin] at h4
  refine ⟨List.nodup_range, fun i => ?_, ?_, by change 0 < 4; norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · change i ∈ List.range p.2.1.length ↔ i < m
    rw [List.mem_range, hp.2.1]
  · change (line4cArity ((p, x, y), t)).length ≤ guardBound 1 (List.range p.1.1.length).length
    rw [hlen, List.length_range, hp.1]
    exact primitiveCase_arity_guard id
  · change (3 : ℝ) / 4 ≤ ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)
    norm_num
  · change ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) < 1
    norm_num
  · change 2 ≤ (line4cArity ((p, x, y), t)).length
    rw [hlen]; exact ht
  · change 4 * (line4cArity ((p, x, y), t)).length ≤ m
    rw [hlen]; omega
  · have hl : (line4cAmbient (((p, x, y), t), z)).1.1.1.length = t := hlen
    rw [hl, aut_line4c hp hϕ hk id x y z hz]
    change 1 - ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) < _
    have h : (1 / 2 : ℚ) ≤ defect (colorAut t (hyperColoring id (decStrN n z))) :=
      not_lt.1 hdef
    have h' : ((1 / 2 : ℚ) : ℝ) ≤ (defect (colorAut t (hyperColoring id (decStrN n z))) : ℝ) :=
      by exact_mod_cast h
    push_cast at h' ⊢
    linarith

end Machine

end Algo

#print axioms Algo.extendedInputRep_line4c
