import Workspace.Algo.NamedWL
import Workspace.Algo.SplitBipClasses

/-!
# Section 9.4, step 3 and its link to steps 4–5

The input table encodes the initial coloring on the actual vertices. Step 3 runs
the raw binary WL routine. Its zero-based names equal the named mathematical
refinement. Reading them with the shift in `sbipDiag` gives `wlDiag`, so the class
routines no longer need a separate assumption about their output names.
-/

namespace Algo

open Babai RAM

/-- Section 9.4, step 3: refine the table on its actual vertex list. -/
def sbipStep3 (p : RawConfig) : RawConfig := rawWLStable p

/-- The complete step-3 routine has a polynomial RAM implementation. -/
theorem sbipPoly_step3 : PolyFun sbipStep3 := polyFun_rawWLStable

section VertexSpecification

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {n : ℕ} (G : VColBipBlk ↥s ℕ) (e : G.Vtx ≃ Fin n)

include e in
/-- The mathematical round bound covers the raw table's round count. -/
theorem sbipNamed_round_bound : n ^ 2 * n ^ 2 ≤ wlRounds Ω := by
  have hn : n = Nat.card G.Vtx := by rw [Nat.card_congr e, Nat.card_fin]
  have hv : Nat.card G.Vtx ≤ Nat.card (Set ↥s) :=
    Nat.card_le_card_of_injective (fun A : G.Vtx => A.val) Subtype.val_injective
  calc
    n ^ 2 * n ^ 2 = (Nat.card G.Vtx * Nat.card G.Vtx) *
        (Nat.card G.Vtx * Nat.card G.Vtx) := by rw [hn, pow_two]
    _ ≤ (Nat.card (Set ↥s) * Nat.card (Set ↥s)) *
        (Nat.card (Set ↥s) * Nat.card (Set ↥s)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hv hv) (Nat.mul_le_mul hv hv)
    _ = Nat.card ((Set ↥s × Set ↥s) × (Set ↥s × Set ↥s)) := by simp
    _ ≤ wlRounds Ω := card_le_wlRounds s

/-- Section 9.4, step 3: the raw output has equal names to the mathematical refinement. -/
theorem sbipStep3_named {p : RawConfig} (hp : NamedBinaryWF n p)
    (hi : ∀ A B : G.Vtx, namedBin n p (e A) (e B) = G.vtxInitColor A B)
    (A B : G.Vtx) : namedBin n (sbipStep3 p) (e A) (e B) = G.wlNamed A B := by
  classical
  letI : Fintype G.Vtx := Fintype.ofFinite _
  rw [sbipStep3, namedBinary_stable_rounds hp (sbipNamed_round_bound G e),
    VColBipBlk.wlNamed_eq]
  exact WL.namedIter_map e hi _ A B

/-- Section 9.4, step 3: adding the vertex shift gives exactly `wlColor`. -/
theorem sbipStep3_spec {p : RawConfig} (hp : NamedBinaryWF n p)
    (hi : ∀ A B : G.Vtx, namedBin n p (e A) (e B) = G.vtxInitColor A B)
    (A B : G.Vtx) :
    binColor (sbipStep3 p, ((e A).val, (e B).val)) + 1 = G.wlColor A.val B.val := by
  classical
  rw [VColBipBlk.wlColor, dif_pos ⟨A.property, B.property⟩]
  exact congrArg (· + 1) (sbipStep3_named G e hp hi A B)

/-- The output table satisfies the usual bound on integer names. -/
theorem sbipStep3_wf {p : RawConfig} (hp : NamedBinaryWF n p) :
    RawWL.WF n 2 (sbipStep3 p) := namedBinary_stable_wf hp

end VertexSpecification

/-- Run step 3 while carrying the first-part list and threshold to steps 4–5. -/
def sbipNamedClasses (r : RawSbipClasses) : RawSbipClasses :=
  ((sbipStep3 r.1.1, r.1.2), r.2)

theorem sbipPoly_namedClasses : PolyFun sbipNamedClasses :=
  (((polyFun_fst.comp polyFun_fst).comp sbipPoly_step3).pair
    (polyFun_fst.comp polyFun_snd)).pair polyFun_snd

section Classes

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (X : Pt (BipBlockInputs Ω)) (e : X.obj.1.1.Vtx ≃ Fin n)

/-- A first-part point is encoded by the table index of its singleton vertex. -/
noncomputable def sbipNamedPoint (x : ↥X.obj.1.1.V₁) : ℕ :=
  (e ⟨{x.val}, Or.inl ⟨x.val, x.property, rfl⟩⟩).val

/-- Well-formed input for step 3 and the following class tests. Only the initial
coloring is specified here. There is no hypothesis about refined names. -/
structure SbipNamedInput (r : RawSbipClasses) : Prop where
  table : NamedBinaryWF n r.1.1
  initial : ∀ A B : X.obj.1.1.Vtx,
    namedBin n r.1.1 (e A) (e B) = X.obj.1.1.vtxInitColor A B
  firstPart : sbipNamedPoint X e '' Set.univ = {a | a ∈ r.1.2}
  firstNodup : r.1.2.Nodup
  threshold : sbipAlphaValue r.2 = BipBlockInputs.alpha X
  denominator : 0 < r.2.2

/-- The vertex enumeration gives distinct table indices to distinct first-part points. -/
theorem sbipNamedPoint_injective : Function.Injective (sbipNamedPoint X e) := by
  intro x y hxy
  have he : e ⟨{x.val}, Or.inl ⟨x.val, x.property, rfl⟩⟩ =
      e ⟨{y.val}, Or.inl ⟨y.val, y.property, rfl⟩⟩ := Fin.ext hxy
  have hs := congrArg (fun A : X.obj.1.1.Vtx => A.val) (e.injective he)
  exact Subtype.ext (Set.singleton_injective hs)

variable {X e} {r : RawSbipClasses}

/-- The output of step 3 discharges the naming hypothesis of steps 4–5. -/
theorem sbipNamedClasses_names (h : SbipNamedInput X e r) :
    SbipClassNames X (sbipNamedPoint X e) (sbipNamedClasses r) where
  injective := sbipNamedPoint_injective X e
  names := h.firstPart
  diagonal x := sbipStep3_spec X.obj.1.1 e h.table h.initial
    ⟨{x.val}, Or.inl ⟨x.val, x.property, rfl⟩⟩
    ⟨{x.val}, Or.inl ⟨x.val, x.property, rfl⟩⟩
  threshold := h.threshold

/-- The table and first-part list produced for steps 4–5 pass their encoding check. -/
theorem sbipNamedClasses_wf (h : SbipNamedInput X e r) :
    sbipClassesWFb (sbipNamedClasses r) = true := by
  have ht := sbipStep3_wf h.table
  apply (sbipClassesWFb_spec _).2
  refine ⟨?_, h.firstNodup, ?_, h.denominator⟩
  · change RawWL.WF (sbipStep3 r.1.1).1.length 2 (sbipStep3 r.1.1)
    rw [card_eq_length_dom ht]
    exact ht
  · intro a ha
    have hm : a ∈ sbipNamedPoint X e '' Set.univ := by rw [h.firstPart]; exact ha
    obtain ⟨x, _, rfl⟩ := hm
    exact (ht.domMem _).2
      (e ⟨{x.val}, Or.inl ⟨x.val, x.property, rfl⟩⟩).isLt

/-- Section 9.4, step 4, with the naming hypothesis supplied by step 3. -/
theorem sbipNamedClasses_class (h : SbipNamedInput X e r) (x : ↥X.obj.1.1.V₁) (k : ℕ) :
    sbipNamedPoint X e x ∈ sbipClass ((sbipNamedClasses r).1, k) ↔
      x.val ∈ colorClass₁ X k := sbipClass_spec (sbipNamedClasses_names h) x k

/-- Section 9.4, step 4: the raw branch test agrees with the mathematical branch. -/
theorem sbipNamedClasses_noDominant (h : SbipNamedInput X e r) :
    sbipNoDominant (sbipNamedClasses r) = true ↔ AllClassesSmall X :=
  sbipNoDominant_iff (sbipNamedClasses_names h) h.firstNodup h.denominator

/-- Section 9.4, step 5: the computed dominant color has the exact mathematical name. -/
theorem sbipNamedClasses_dominantColor (h : SbipNamedInput X e r) (hd : ¬ AllClassesSmall X) :
    sbipDominantColor (sbipNamedClasses r) = dominantColor X :=
  sbipDominantColor_spec (sbipNamedClasses_names h) h.firstNodup h.denominator hd

/-- Section 9.4, step 5: the selected points are exactly the mathematical dominant class. -/
theorem sbipNamedClasses_dominant (h : SbipNamedInput X e r) (hd : ¬ AllClassesSmall X)
    (x : ↥X.obj.1.1.V₁) : sbipNamedPoint X e x ∈ sbipDominant (sbipNamedClasses r) ↔
      x.val ∈ dominantClass X :=
  sbipDominant_spec (sbipNamedClasses_names h) h.firstNodup h.denominator hd x

/-- Section 9.4, step 5: the computed size and threshold are the mathematical update. -/
theorem sbipNamedClasses_update (h : SbipNamedInput X e r) (hd : ¬ AllClassesSmall X) :
    (sbipClassUpdate (sbipNamedClasses r)).1.length = (step5Obj X).V₁.ncard ∧
      sbipAlphaValue (sbipClassUpdate (sbipNamedClasses r)).2 = alphaNew X :=
  sbipClassUpdate_spec (sbipNamedClasses_names h) h.firstNodup h.denominator hd

end Classes

/-- Steps 3–4 together have a polynomial RAM implementation. -/
theorem sbipPoly_namedNoDominant :
    PolyFun (fun r => sbipNoDominant (sbipNamedClasses r)) :=
  sbipPoly_namedClasses.comp sbipPoly_noDominant

/-- Steps 3 and 5 together have a polynomial RAM implementation. -/
theorem sbipPoly_namedClassUpdate :
    PolyFun (fun r => sbipClassUpdate (sbipNamedClasses r)) :=
  sbipPoly_namedClasses.comp sbipPoly_classUpdate

end Algo
