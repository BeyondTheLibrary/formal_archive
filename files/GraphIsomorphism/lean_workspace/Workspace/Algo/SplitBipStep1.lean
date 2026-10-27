import Workspace.Algo.SplitNumberings
import Workspace.Algo.SplitBipRestrict
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Section 9.4, step 1 on the RAM

Enumerate the numberings of the bounded first part. For each numbering,
individualize the first `n₁ - floor(α n₁)` points and give the remaining
points color zero. This is precisely `step1Outcome`, including its rounding.
The two output lists give the colors and the blocks in first-part order.
-/

namespace Algo
open Babai RAM RAM.Targets

abbrev RawSbipStep1 := (List ℕ × (ℕ × ℕ)) × RawPerm

def sbipStep1Cut (p : List ℕ × (ℕ × ℕ)) : ℕ :=
  p.1.length - p.2.1 * p.1.length / p.2.2

def sbipStep1Color (z : RawSbipStep1 × ℕ) : ℕ :=
  let a := z.1.2.getD z.2 0
  if a < sbipStep1Cut z.1.1 then a + 1 else 0

def sbipStep1 (p : RawSbipStep1) : RawLab × RawLab :=
  let l := (List.range p.1.1.length).map (fun i => sbipStep1Color (p, i))
  (l, l)

/-- All choices of the individualization, in an explicit order. -/
def sbipStep1Versions (C : ℕ) (p : List ℕ × (ℕ × ℕ)) : List (RawLab × RawLab) :=
  (sbipNumberings C (p.1, p.1)).map (fun row => sbipStep1 (p, row))

theorem polyFun_sbipStep1Cut : PolyFun sbipStep1Cut := by
  have hn : PolyFun (fun p : List ℕ × (ℕ × ℕ) => p.1.length) :=
    polyFun_fst.comp polyFun_length
  exact hn.sub ((((polyFun_snd.comp polyFun_fst).mul hn).pair
    (polyFun_snd.comp polyFun_snd)).comp polyFun_div)

theorem polyFun_sbipStep1Color : PolyFun sbipStep1Color := by
  have ha : PolyFun (fun z : RawSbipStep1 × ℕ => z.1.2.getD z.2 0) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair
      (polyFun_const 0)).comp polyFun_getD
  have hk : PolyFun (fun z : RawSbipStep1 × ℕ => sbipStep1Cut z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_sbipStep1Cut
  exact (PolyFun.ite ((hk.pair ha).comp wftPolyFun_lt)
    (ha.add (polyFun_const 1)) (polyFun_const 0)).of_eq (fun z => by
      by_cases h : z.1.2.getD z.2 0 < sbipStep1Cut z.1.1 <;>
        simp [wftLt, sbipStep1Color, h])

theorem polyFun_sbipStep1 : PolyFun sbipStep1 := by
  have hl : PolyFun (fun p : RawSbipStep1 =>
      (List.range p.1.1.length).map (fun i => sbipStep1Color (p, i))) :=
    (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_sbipStep1Color)
  exact hl.pair hl

theorem quasiFun_sbipStep1Versions (C : ℕ) : QuasiFun (sbipStep1Versions C) :=
  (polyFun_id.quasiFun.pair ((polyFun_fst.pair polyFun_fst).comp_quasiFun
    (quasiFun_sbipNumberings C))).comp_poly (PolyFun.mapParam polyFun_sbipStep1)

theorem sbipStep1Cut_spec (p : List ℕ × (ℕ × ℕ)) :
    sbipStep1Cut p = p.1.length - ⌊sbipAlphaValue p.2 * p.1.length⌋₊ := by
  unfold sbipStep1Cut sbipAlphaValue
  congr 1
  rw [div_mul_eq_mul_div, ← Nat.cast_mul, Nat.floor_div_eq_div]

theorem sbipStep1_get (p : RawSbipStep1) (i : Fin p.1.1.length) :
    labAt (sbipStep1 p).1 i = sbipStep1Color (p, i) := by
  simp [sbipStep1, labAt, i.isLt]

@[simp] theorem sbipStep1_lengths (p : RawSbipStep1) :
    (sbipStep1 p).1.length = p.1.1.length ∧ (sbipStep1 p).2.length = p.1.1.length := by
  simp [sbipStep1]

section Specification

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) {dom : List ℕ} (e : ↥G.V₁ ≃ Fin dom.length)

open scoped Classical in
/-- Extend the decoded numbering by zero outside the first part. -/
noncomputable def sbipPartNumbering (row : RawPerm) (x : ↥s) : ℕ :=
  if h : x ∈ G.V₁ then (decPerm dom.length row (e ⟨x, h⟩)).val else 0

theorem sbipPartNumbering_valid (row : RawPerm) :
    IsPart₁Numbering G (sbipPartNumbering G e row) := by
  have hn : dom.length = G.V₁.ncard := by
    have h := Nat.card_congr e
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using h.symm
  refine ⟨fun x hx => dif_neg hx, ?_, ?_⟩
  · intro x hx y hy he
    have hh : decPerm dom.length row (e ⟨x, hx⟩) =
        decPerm dom.length row (e ⟨y, hy⟩) := by
      apply Fin.ext
      simpa only [sbipPartNumbering, dif_pos hx, dif_pos hy] using he
    exact congrArg Subtype.val (e.injective ((decPerm dom.length row).injective hh))
  · intro x hx
    simp only [sbipPartNumbering, dif_pos hx]
    rw [← hn]
    exact (decPerm dom.length row (e ⟨x, hx⟩)).isLt

theorem sbipPartNumbering_complete {C : ℕ} (hn : dom.length ≤ C)
    (σ : ↥s → ℕ) (hσ : IsPart₁Numbering G σ) :
    ∃ row ∈ sbipNumberings C (dom, dom), sbipPartNumbering G e row = σ := by
  have hcard : dom.length = G.V₁.ncard := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr e).symm
  obtain ⟨row, hrow, he⟩ := sbipNumberings_realizes e (fun x => σ x.val)
    (fun x y hxy => Subtype.ext (hσ.2.1 x.property y.property hxy))
    (fun x => by rw [hcard]; exact hσ.2.2 x.val x.property) (sbip_small_guard hn)
  refine ⟨row, hrow, funext fun x => ?_⟩
  by_cases hx : x ∈ G.V₁
  · simpa only [sbipPartNumbering, dif_pos hx] using he ⟨x, hx⟩
  · simp only [sbipPartNumbering, dif_neg hx, hσ.1 x hx]

theorem sbipStep1_spec (p : ℕ × ℕ) {row : RawPerm}
    (hr : RawPerm.WF dom.length row) (x y : ↥G.V₁) :
    labAt (sbipStep1 ((dom, p), row)).1 (e x) =
      (kerPartition G.V₁ (indivColor (sbipPartNumbering G e row)
        (G.V₁.ncard - ⌊sbipAlphaValue p * G.V₁.ncard⌋₊))).color (mkPt x.property) ∧
    (LabRel (sbipStep1 ((dom, p), row)).2 (e x) (e y) ↔
      (kerPartition G.V₁ (indivColor (sbipPartNumbering G e row)
        (G.V₁.ncard - ⌊sbipAlphaValue p * G.V₁.ncard⌋₊))).part
          (mkPt x.property) (mkPt y.property)) := by
  have hn : dom.length = G.V₁.ncard := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr e).symm
  have hcolor (u : ↥G.V₁) :
      labAt (sbipStep1 ((dom, p), row)).1 (e u) =
        indivColor (sbipPartNumbering G e row)
          (G.V₁.ncard - ⌊sbipAlphaValue p * G.V₁.ncard⌋₊) u := by
    rw [sbipStep1_get]
    have hcut : sbipStep1Cut (dom, p) =
        G.V₁.ncard - ⌊sbipAlphaValue p * G.V₁.ncard⌋₊ := by
      rw [sbipStep1Cut_spec]
      exact congrArg (fun n : ℕ => n - ⌊sbipAlphaValue p * (n : ℝ)⌋₊) hn
    have hu : (e u).val < row.length := by simpa only [hr.length] using (e u).isLt
    simp only [sbipStep1Color, indivColor, sbipPartNumbering, dif_pos u.property,
      hcut, decPerm_val_of_wf hr, List.getD_eq_getElem row 0 hu]
  refine ⟨hcolor x, ?_⟩
  change labAt (sbipStep1 ((dom, p), row)).1 (e x) =
    labAt (sbipStep1 ((dom, p), row)).1 (e y) ↔ _
  rw [hcolor x, hcolor y]
  rfl

end Specification

theorem sbipStep1_good {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) {dom : List ℕ}
    (e : ↥X.obj.1.1.V₁ ≃ Fin dom.length) (row : RawPerm) :
    Good_9_2_2 X ⟨Subtype.val '' X.obj.1.1.V₁,
      Sum.inl (kerPartition X.obj.1.1.V₁
        (indivColor (sbipPartNumbering X.obj.1.1 e row)
          (X.obj.1.1.V₁.ncard - ⌊BipBlockInputs.alpha X * X.obj.1.1.V₁.ncard⌋₊)))⟩ := by
  classical
  obtain ⟨hα, hα1, hinput⟩ := X.obj.2
  exact ⟨rfl, step1Outcome_isAlphaPartition hα hα1 _ hinput.1
    (sbipPartNumbering_valid _ e row) _⟩

theorem sbipStep1Versions_width {C : ℕ} (p : List ℕ × (ℕ × ℕ)) (hn : p.1.length ≤ C) :
    (sbipStep1Versions C p).length ≤ constFactor C := by
  rw [sbipStep1Versions, List.length_map]
  exact (length_sbipNumberings_le (sbip_small_guard hn)).trans (pow_self_le_constFactor hn)

end Algo

#print axioms Algo.quasiFun_sbipStep1Versions
#print axioms Algo.sbipStep1_spec
#print axioms Algo.sbipStep1_good
