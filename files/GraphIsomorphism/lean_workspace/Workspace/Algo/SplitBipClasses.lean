import Workspace.Algo.SplitBipAlpha
import Workspace.Algo.SplitUpccCaseSpec

/-!
# Section 9.4, steps 4 and 5: classes of a supplied binary table

The input carries the table, the ordered first part, and the threshold.
The naming hypothesis identifies its diagonal colors with `wlDiag`.
The raw table keeps the zero-based refinement names. Reading a diagonal adds one,
as `wlDiag` does on actual vertices. The refinement bridge discharges the naming
hypothesis for the output of step 3.
-/

namespace Algo
open Babai RAM

/-- Section 9.4, steps 4 and 5: table, first part, and threshold pair. -/
abbrev RawSbipClasses := (RawConfig × List ℕ) × (ℕ × ℕ)

/-- The diagonal color at one named point, shifted as in `VColBipBlk.wlDiag`. -/
def sbipDiag (z : RawConfig × ℕ) : ℕ := binColor (z.1, (z.2, z.2)) + 1

theorem sbipPoly_diag : PolyFun sbipDiag :=
  ((polyFun_fst.pair (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor).add
    (polyFun_const 1)

/-- A named predicate keeps the filter's RAM proof small. -/
def sbipClassTest (z : (RawConfig × ℕ) × ℕ) : Bool :=
  decide (sbipDiag (z.1.1, z.2) = z.1.2)

theorem sbipPoly_classTest : PolyFun sbipClassTest :=
  (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp sbipPoly_diag).natEq
    (polyFun_fst.comp polyFun_snd)

/-- Section 9.4, step 4: a vertex-color class inside the first part. -/
def sbipClass (z : (RawConfig × List ℕ) × ℕ) : List ℕ :=
  z.1.2.filter (fun u => sbipClassTest ((z.1.1, z.2), u))

theorem sbipPoly_class : PolyFun sbipClass :=
  ((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).pair
    (polyFun_fst.comp polyFun_snd)).comp (PolyFun.filterParam sbipPoly_classTest))

theorem sbipClass_mem (p : RawConfig) (l : List ℕ) (k u : ℕ) :
    u ∈ sbipClass ((p,l),k) ↔ u ∈ l ∧ sbipDiag (p,u) = k := by
  simp [sbipClass, sbipClassTest]

/-- Section 9.4, step 5: the strict dominance test uses cross multiplication. -/
def sbipBig (z : RawSbipClasses × ℕ) : Bool :=
  decide (z.1.2.1 * z.1.1.2.length + 1 ≤
    z.1.2.2 * (sbipClass (z.1.1, z.2)).length)

theorem sbipPoly_big : PolyFun sbipBig := by
  have ha : PolyFun (fun z : RawSbipClasses × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hb : PolyFun (fun z : RawSbipClasses × ℕ => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hn : PolyFun (fun z : RawSbipClasses × ℕ => z.1.1.2.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_length
  have hw : PolyFun (fun z : RawSbipClasses × ℕ => (sbipClass (z.1.1,z.2)).length) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
    sbipPoly_class).comp polyFun_length
  exact ((ha.mul hn).add (polyFun_const 1)).le (hb.mul hw)

/-- Section 9.4, step 5: scan only colors that occur in the first part. -/
def sbipBigColors (r : RawSbipClasses) : List ℕ :=
  (r.1.2.map (fun u => sbipDiag (r.1.1,u))).filter (fun k => sbipBig (r,k))

theorem sbipPoly_bigColors : PolyFun sbipBigColors := by
  have hc : PolyFun (fun z : RawSbipClasses × ℕ => sbipDiag (z.1.1.1,z.2)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
      sbipPoly_diag
  have hm := (polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp (PolyFun.mapParam hc)
  exact (polyFun_id.pair hm).comp (PolyFun.filterParam sbipPoly_big)

/-- Section 9.4, step 4: no class has more than `αn₁` points. -/
def sbipNoDominant (r : RawSbipClasses) : Bool := (sbipBigColors r).isEmpty

theorem sbipPoly_noDominant : PolyFun sbipNoDominant :=
  sbipPoly_bigColors.comp polyFun_isEmpty

/-- Section 9.4, step 5: the dominant color, with zero as the empty fallback. -/
def sbipDominantColor (r : RawSbipClasses) : ℕ := (sbipBigColors r).headD 0

theorem sbipPoly_dominantColor : PolyFun sbipDominantColor := by
  exact (((sbipPoly_bigColors.comp polyFun_headOption).pair (polyFun_const 0)).comp
    polyFun_optionGetD).of_eq (fun _ => List.headD_eq_head?_getD.symm)

/-- Section 9.4, step 5: the selected class `W₁`. -/
def sbipDominant (r : RawSbipClasses) : List ℕ := sbipClass (r.1, sbipDominantColor r)

theorem sbipPoly_dominant : PolyFun sbipDominant :=
  (polyFun_fst.pair sbipPoly_dominantColor).comp sbipPoly_class

/-- Section 9.4, step 5: the new first part and the updated pair. -/
def sbipClassUpdate (r : RawSbipClasses) : List ℕ × (ℕ × ℕ) :=
  (sbipDominant r, sbipAlphaUpdate (r.2, (r.1.2.length, (sbipDominant r).length)))

theorem sbipPoly_classUpdate : PolyFun sbipClassUpdate :=
  sbipPoly_dominant.pair
    ((polyFun_snd.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_length).pair
      (sbipPoly_dominant.comp polyFun_length))).comp sbipPoly_alphaUpdate)

/-- The encoding test checks a binary table, a duplicate-free subset and a positive
denominator. It does not test coherence or construct the mathematical naming. -/
def sbipClassesWFb (r : RawSbipClasses) : Bool :=
  upccCaseTableB r.1.1 && nodupB r.1.2 &&
    upccCaseSubsetB (r.1.2,r.1.1.1) && decide (1 ≤ r.2.2)

theorem sbipClassesWFb_spec (r : RawSbipClasses) :
    sbipClassesWFb r = true ↔ RawWL.WF r.1.1.1.length 2 r.1.1 ∧
      r.1.2.Nodup ∧ r.1.2 ⊆ r.1.1.1 ∧ 0 < r.2.2 := by
  simp only [sbipClassesWFb, Bool.and_eq_true, upccCaseTableB_spec, nodupB_eq_true,
    upccCaseSubsetB_spec, decide_eq_true_eq, Nat.succ_le_iff, and_assoc]

theorem sbipPoly_classesWFb : PolyFun sbipClassesWFb := by
  have hp : PolyFun (fun r : RawSbipClasses => r.1.1) := polyFun_fst.comp polyFun_fst
  have hl : PolyFun (fun r : RawSbipClasses => r.1.2) := polyFun_fst.comp polyFun_snd
  exact polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd
    (hp.comp upccCasePoly_table) (hl.comp polyFun_nodupB))
      ((hl.pair (hp.comp polyFun_fst)).comp (upccCasePoly_subset polyFun_natEq)))
        ((polyFun_const 1).le ((polyFun_snd.comp polyFun_snd)))

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : ↥X.obj.1.1.V₁ → ℕ)

/-- Section 9.4, steps 4 and 5: a supplied table has the mathematical diagonal
colors. Names are injective on the first part and list exactly that part. -/
structure SbipClassNames (r : RawSbipClasses) : Prop where
  injective : Function.Injective name
  names : name '' Set.univ = {a | a ∈ r.1.2}
  diagonal : ∀ x, sbipDiag (r.1.1,name x) = VColBipBlk.wlDiag X.obj.1.1 x
  threshold : sbipAlphaValue r.2 = BipBlockInputs.alpha X

variable {X name} {r : RawSbipClasses} (h : SbipClassNames X name r)

include h

theorem sbipName_mem (x : ↥X.obj.1.1.V₁) : name x ∈ r.1.2 := by
  have hx := Set.mem_image_of_mem name (Set.mem_univ x)
  rw [h.names] at hx
  exact hx

theorem sbipName_surj {a : ℕ} (ha : a ∈ r.1.2) : ∃ x, name x = a := by
  have hx : a ∈ name '' Set.univ := by rw [h.names]; exact ha
  simpa using hx

theorem sbipPart_size (hnd : r.1.2.Nodup) : r.1.2.length = BipBlockInputs.n₁ X := by
  have hs := upccCaseSize_image Set.univ name h.injective r.1.2 hnd h.names
  simpa [Set.ncard_univ, Nat.card_coe_set_eq, BipBlockInputs.n₁] using hs

/-- Section 9.4, step 4: the computed cell is exactly `Babai.colorClass₁`. -/
theorem sbipClass_spec (x : ↥X.obj.1.1.V₁) (k : ℕ) :
    name x ∈ sbipClass (r.1,k) ↔ (x : ↥X.car) ∈ colorClass₁ X k := by
  rw [sbipClass_mem, h.diagonal]
  simp only [sbipName_mem h x, true_and, colorClass₁, Set.mem_setOf_eq, x.property]

theorem sbipClass_size (hnd : r.1.2.Nodup) (k : ℕ) :
    (sbipClass (r.1,k)).length = (colorClass₁ X k).ncard := by
  let S : Set ↥X.obj.1.1.V₁ := {x | (x : ↥X.car) ∈ colorClass₁ X k}
  have himg : name '' S = {a | a ∈ sbipClass (r.1,k)} := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (sbipClass_spec h x k).2 hx
    · intro ha
      obtain ⟨x,rfl⟩ := sbipName_surj h ((sbipClass_mem _ _ _ _).1 ha).1
      exact ⟨x,(sbipClass_spec h x k).1 ha,rfl⟩
  have hval : Subtype.val '' S = colorClass₁ X k := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hx.1⟩,hx,rfl⟩
  have hs : (sbipClass (r.1,k)).length = S.ncard :=
    upccCaseSize_image S name h.injective _ (hnd.filter _) himg
  rw [hs, ← hval,
    Set.ncard_image_of_injective _ Subtype.val_injective]

theorem sbipBig_spec (hnd : r.1.2.Nodup) (hb : 0 < r.2.2) (k : ℕ) :
    sbipBig (r,k) = true ↔ k ∈ dominantColors X := by
  have hbR : (0 : ℝ) < r.2.2 := by exact_mod_cast hb
  have hn := sbipPart_size h hnd
  have hc := sbipClass_size h hnd k
  change decide (r.2.1 * r.1.2.length + 1 ≤
    r.2.2 * (sbipClass (r.1,k)).length) = true ↔
      BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) < (colorClass₁ X k).ncard
  rw [← h.threshold]
  simp only [sbipAlphaValue, decide_eq_true_eq, Nat.succ_le_iff, hn, hc]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hbR]
  norm_cast
  rw [Nat.mul_comm r.2.2]

theorem sbipBigColors_spec (hnd : r.1.2.Nodup) (hb : 0 < r.2.2) (k : ℕ) :
    k ∈ sbipBigColors r ↔ k ∈ dominantColors X := by
  simp only [sbipBigColors, List.mem_filter, sbipBig_spec h hnd hb]
  constructor
  · exact And.right
  · intro hk
    obtain ⟨x,hx,hk'⟩ := exists_mem_of_mem_dominantColors hk
    exact ⟨List.mem_map.2 ⟨name ⟨x,hx⟩, sbipName_mem h _,
      (h.diagonal ⟨x,hx⟩).trans hk'⟩,hk⟩

/-- Section 9.4, step 4: the raw branch test is `Babai.AllClassesSmall`. -/
theorem sbipNoDominant_iff (hnd : r.1.2.Nodup) (hb : 0 < r.2.2) :
    sbipNoDominant r = true ↔ AllClassesSmall X := by
  simp only [sbipNoDominant, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
    sbipBigColors_spec h hnd hb, dominantColors, Set.mem_setOf_eq, not_lt]
  exact (allClassesSmall_iff X).symm

/-- Section 9.4, step 5: uniqueness identifies the scan with the exact
mathematical `dominantColor`, despite the input order. -/
theorem sbipDominantColor_spec (hnd : r.1.2.Nodup) (hb : 0 < r.2.2)
    (hd : ¬ AllClassesSmall X) : sbipDominantColor r = dominantColor X := by
  have hm := (sbipBigColors_spec h hnd hb (dominantColor X)).2 (dominantColor_mem hd)
  have hh : sbipDominantColor r ∈ sbipBigColors r := by
    unfold sbipDominantColor
    cases he : sbipBigColors r with
    | nil => simp [he] at hm
    | cons a l => simp
  exact dominantColors_subsingleton X
    ((sbipBigColors_spec h hnd hb _).1 hh) (dominantColor_mem hd)

theorem sbipDominant_spec (hnd : r.1.2.Nodup) (hb : 0 < r.2.2)
    (hd : ¬ AllClassesSmall X) (x : ↥X.obj.1.1.V₁) :
    name x ∈ sbipDominant r ↔ (x : ↥X.car) ∈ dominantClass X := by
  rw [sbipDominant, sbipDominantColor_spec h hnd hb hd]
  exact sbipClass_spec h x _

theorem sbipDominant_size (hnd : r.1.2.Nodup) (hb : 0 < r.2.2)
    (hd : ¬ AllClassesSmall X) :
    (sbipDominant r).length = (dominantClass X).ncard := by
  rw [sbipDominant, sbipDominantColor_spec h hnd hb hd]
  exact sbipClass_size h hnd _

/-- Section 9.4, step 5: the computed first-part size and real threshold
agree with `step5Obj` and `alphaNew`. -/
theorem sbipClassUpdate_spec (hnd : r.1.2.Nodup) (hb : 0 < r.2.2)
    (hd : ¬ AllClassesSmall X) :
    (sbipClassUpdate r).1.length = (step5Obj X).V₁.ncard ∧
      sbipAlphaValue (sbipClassUpdate r).2 = alphaNew X := by
  constructor
  · change (sbipDominant r).length = _
    rw [sbipDominant_size h hnd hb hd, step5Obj_V₁_ncard]
  · exact sbipAlphaUpdate_spec X r.2 _ _ h.threshold (sbipPart_size h hnd)
      (sbipDominant_size h hnd hb hd)

end Specification

/-- Section 9.4, steps 4 and 5: transport the table and the ordered first part. -/
def sbipRelabelClasses (π : RawPerm) (r : RawSbipClasses) : RawSbipClasses :=
  ((relabelWL (π,r.1.1),permList π r.1.2),r.2)

theorem sbipPoly_relabelClasses : PolyFun (fun z : RawPerm × RawSbipClasses =>
    sbipRelabelClasses z.1 z.2) := by
  have hp : PolyFun (fun z : RawPerm × RawSbipClasses => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hl : PolyFun (fun z : RawPerm × RawSbipClasses => z.2.1.2) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_snd
  exact (((polyFun_fst.pair hp).comp polyFun_splitRelabelWL).pair
    ((polyFun_fst.pair hl).comp polyFun_splitPermList)).pair
      (polyFun_snd.comp polyFun_snd)

section Transport
variable {n : ℕ} {p : RawConfig} {π : RawPerm} {l : List ℕ}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π) (hl : ∀ a ∈ l, a < n)

include hp hπ

theorem sbipDiag_relabel {u : ℕ} (hu : u < n) :
    sbipDiag (relabelWL (π,p),rawApply (π,u)) = sbipDiag (p,u) :=
  congrArg (· + 1) (binColor_relabel hp hπ hu hu)

include hl

theorem sbipClass_relabel (k : ℕ) :
    sbipClass ((relabelWL (π,p),permList π l),k) = permList π (sbipClass ((p,l),k)) := by
  simp only [sbipClass, permList, List.filter_map]
  congr 1
  apply List.filter_congr
  intro u hu
  dsimp only [Function.comp_def, sbipClassTest]
  rw [sbipDiag_relabel hp hπ (hl u hu)]

theorem sbipBig_relabel (q : ℕ × ℕ) (k : ℕ) :
    sbipBig (sbipRelabelClasses π ((p,l),q),k) = sbipBig (((p,l),q),k) := by
  simp only [sbipBig, sbipRelabelClasses, sbipClass_relabel hp hπ hl, length_permList]

theorem sbipBigColors_relabel (q : ℕ × ℕ) :
    sbipBigColors (sbipRelabelClasses π ((p,l),q)) = sbipBigColors ((p,l),q) := by
  have hm : (permList π l).map (fun u => sbipDiag (relabelWL (π,p),u)) =
      l.map (fun u => sbipDiag (p,u)) := by
    simp only [permList, List.map_map]
    exact List.map_congr_left (fun u hu => sbipDiag_relabel hp hπ (hl u hu))
  unfold sbipBigColors
  change ((permList π l).map (fun u => sbipDiag (relabelWL (π,p),u))).filter _ = _
  rw [hm]
  apply List.filter_congr
  intro k _
  exact sbipBig_relabel hp hπ hl q k

theorem sbipNoDominant_relabel (q : ℕ × ℕ) :
    sbipNoDominant (sbipRelabelClasses π ((p,l),q)) = sbipNoDominant ((p,l),q) := by
  simp only [sbipNoDominant, sbipBigColors_relabel hp hπ hl]

theorem sbipDominantColor_relabel (q : ℕ × ℕ) :
    sbipDominantColor (sbipRelabelClasses π ((p,l),q)) = sbipDominantColor ((p,l),q) := by
  simp only [sbipDominantColor, sbipBigColors_relabel hp hπ hl]

theorem sbipDominant_relabel (q : ℕ × ℕ) :
    sbipDominant (sbipRelabelClasses π ((p,l),q)) = permList π (sbipDominant ((p,l),q)) := by
  unfold sbipDominant
  rw [sbipDominantColor_relabel hp hπ hl]
  exact sbipClass_relabel hp hπ hl _

/-- Section 9.4, step 5: the whole computed update commutes with relabeling.
The first part moves and the threshold pair stays equal. -/
theorem sbipClassUpdate_relabel (q : ℕ × ℕ) :
    sbipClassUpdate (sbipRelabelClasses π ((p,l),q)) =
      (permList π (sbipClassUpdate ((p,l),q)).1, (sbipClassUpdate ((p,l),q)).2) := by
  unfold sbipClassUpdate
  rw [sbipDominant_relabel hp hπ hl]
  simp only [sbipRelabelClasses, length_permList]

end Transport

/-- Section 9.4, step 5: every raw update satisfies the one-step size bound,
even when the input is malformed. A filter never enlarges the first part. -/
theorem sbipClassUpdate_bits (r : RawSbipClasses) :
    Nat.size (sbipClassUpdate r).2.1 + Nat.size (sbipClassUpdate r).2.2 ≤
      Nat.size r.2.1 + Nat.size r.2.2 + 2 * Nat.size r.1.2.length := by
  exact sbipAlphaUpdate_bits r.2 (Nat.le_refl _) (List.length_filter_le _ _)

end Algo
