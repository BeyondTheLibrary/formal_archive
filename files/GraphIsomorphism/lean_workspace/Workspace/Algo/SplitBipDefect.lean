import Workspace.Algo.SplitTwins
import Workspace.Algo.SplitUpccCaseRaw
import Workspace.SplitOrJohnson.Imprimitive

/-! # Section 9: test the first-part symmetry defect

Two first-part vertices are twins precisely when their neighborhoods agree.
We count these classes and test that none occupies more than half the part.
This is the branch test used in Section 9.6.
-/
namespace Algo
open Babai RAM

open scoped Classical in
/-- The largest twin set is bounded exactly when every equal-neighborhood
class is bounded. -/
theorem bipSymmetricity_le_iff {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (X : BipGraph A B) (m : ℕ) :
    X.symmetricity₁ ≤ m ↔
      ∀ a : A, {b : A | ∀ w : B, (a,w) ∈ X.E ↔ (b,w) ∈ X.E}.ncard ≤ m := by
  classical
  rw [BipGraph.symmetricity₁_eq_sup, Finset.sup_le_iff]
  constructor
  · intro h a
    let T : Finset A := Finset.univ.filter (fun b =>
      ∀ w : B, (a,w) ∈ X.E ↔ (b,w) ∈ X.E)
    have hc : (↑T : Set A) = {b : A | ∀ w : B, (a,w) ∈ X.E ↔ (b,w) ∈ X.E} := by
      ext b; simp [T]
    rw [← hc, Set.ncard_coe_finset]
    apply h T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx y hy w
    exact ((Finset.mem_filter.1 hx).2 w).symm.trans ((Finset.mem_filter.1 hy).2 w)
  · intro h T hT
    have ht := (Finset.mem_filter.1 hT).2
    by_cases he : T.Nonempty
    · obtain ⟨a,ha⟩ := he
      have hs : (↑T : Set A) ⊆ {b : A | ∀ w : B, (a,w) ∈ X.E ↔ (b,w) ∈ X.E} :=
        fun b hb w => ht a ha b hb w
      exact (Set.ncard_le_ncard hs).trans (h a) |>.trans' (by simp)
    · simp [Finset.not_nonempty_iff_eq_empty.1 he]

open scoped Classical in
/-- The integer comparison also handles an empty first part. -/
theorem bipHalfDefect_iff {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (X : BipGraph A B) :
    1 / 2 ≤ X.defect₁ ↔ 2 * X.symmetricity₁ ≤ Fintype.card A := by
  constructor
  · intro h
    by_cases hz : Fintype.card A = 0
    · have hs : X.symmetricity₁ ≤ 0 := (bipSymmetricity_le_iff X 0).2 (fun a =>
        (False.elim ((Fintype.card_pos_iff.mpr ⟨a⟩).ne' hz)))
      omega
    · have hn : (0 : ℚ) < Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero hz
      change 1 / 2 ≤ 1 - (X.symmetricity₁ : ℚ) / Fintype.card A at h
      have hh : (X.symmetricity₁ : ℚ) / Fintype.card A ≤ 1 / 2 := by linarith
      have := (div_le_iff₀ hn).1 hh
      have hh' : (2 : ℚ) * X.symmetricity₁ ≤ Fintype.card A := by linarith
      exact_mod_cast hh'
  · exact BipGraph.half_le_defect₁

/-- Test one first-part twin class. -/
def bipHalfClass (z : RawBipConstituent × ℕ) : Bool :=
  decide (2 * classSizeRaw (bipTwinsRaw z.1,z.2) ≤ z.1.2.1.length)

theorem polyFun_bipHalfClass : PolyFun bipHalfClass :=
  ((polyFun_const 2).mul (((polyFun_fst.comp polyFun_bipTwinsRaw).pair
    polyFun_snd).comp polyFun_classSizeRaw)).le
      (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_length)

/-- The full symmetry-defect test, with no promise on the raw table. -/
def bipHalfDefect (z : RawBipConstituent) : Bool :=
  upccCaseAllB bipHalfClass (z,List.range z.2.1.length)

theorem polyFun_bipHalfDefect : PolyFun bipHalfDefect :=
  (polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (upccCasePoly_all polyFun_bipHalfClass)

theorem bipHalfDefect_spec (z : RawBipConstituent) :
    bipHalfDefect z = true ↔ 1 / 2 ≤ (decBipConstituent z).defect₁ := by
  rw [bipHalfDefect,upccCaseAllB_spec,bipHalfDefect_iff]
  have he : ∀ u : Fin z.2.1.length,
      classSizeRaw (bipTwinsRaw z,u) =
        {v : Fin z.2.1.length | ∀ w : Fin z.2.2.length,
          (u,w) ∈ (decBipConstituent z).E ↔ (v,w) ∈ (decBipConstituent z).E}.ncard := by
    intro u
    rw [bipTwinSize_spec]
    congr 1
    ext v
    simp only [Set.mem_setOf_eq]
    rw [← bipTwinTest_spec, bipTwinTest_neighborhoods, Set.ext_iff]
    rfl
  have hs := bipSymmetricity_le_iff (decBipConstituent z) (z.2.1.length / 2)
  simp only [bipHalfClass,decide_eq_true_eq,List.mem_range,Fintype.card_fin]
  constructor
  · intro h
    have : (decBipConstituent z).symmetricity₁ ≤ z.2.1.length / 2 := hs.2 (by
      intro u
      rw [← he]
      have := h u u.isLt
      omega)
    omega
  · intro h u hu
    have hh := hs.1 (by omega) ⟨u,hu⟩
    rw [← he] at hh
    change classSizeRaw (bipTwinsRaw z,u) ≤ z.2.1.length / 2 at hh
    omega

end Algo
