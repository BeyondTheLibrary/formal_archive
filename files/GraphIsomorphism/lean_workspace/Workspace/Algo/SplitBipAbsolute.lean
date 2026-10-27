import Workspace.Algo.SplitBipDefect

/-! # The absolute-defect test of Procedure Reduce-Part2-by-Color

Section 9.3 asks for absolute defect at least `(n₁ - 1)/2`. This is an
inclusive bound of `(n₁ + 1)/2` on each twin class. The extra one matters
for odd first-part sizes.
-/
namespace Algo
open Babai RAM

def bipCoverClass (z : RawBipConstituent × ℕ) : Bool :=
  decide (2 * classSizeRaw (bipTwinsRaw z.1,z.2) ≤ z.1.2.1.length + 1)

def bipCoverDefect (z : RawBipConstituent) : Bool :=
  upccCaseAllB bipCoverClass (z,List.range z.2.1.length)

theorem polyFun_bipCoverClass : PolyFun bipCoverClass :=
  ((polyFun_const 2).mul (((polyFun_fst.comp polyFun_bipTwinsRaw).pair
    polyFun_snd).comp polyFun_classSizeRaw)).le
      ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_length).add
        (polyFun_const 1))

theorem polyFun_bipCoverDefect : PolyFun bipCoverDefect :=
  (polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (upccCasePoly_all polyFun_bipCoverClass)

theorem bipCoverDefect_spec (z : RawBipConstituent) :
    bipCoverDefect z = true ↔ ((z.2.1.length : ℚ) - 1) / 2 ≤
      (z.2.1.length : ℚ) - (decBipConstituent z).symmetricity₁ := by
  rw [bipCoverDefect,upccCaseAllB_spec]
  have he : ∀ u : Fin z.2.1.length,
      classSizeRaw (bipTwinsRaw z,u) =
        {v : Fin z.2.1.length | ∀ w : Fin z.2.2.length,
          (u,w) ∈ (decBipConstituent z).E ↔ (v,w) ∈ (decBipConstituent z).E}.ncard := by
    intro u
    rw [bipTwinSize_spec]
    congr 1
    ext v
    simp only [Set.mem_setOf_eq]
    rw [← bipTwinTest_spec,bipTwinTest_neighborhoods,Set.ext_iff]
    rfl
  have hs := bipSymmetricity_le_iff (decBipConstituent z) ((z.2.1.length + 1) / 2)
  have harith : ((z.2.1.length : ℚ) - 1) / 2 ≤
      (z.2.1.length : ℚ) - (decBipConstituent z).symmetricity₁ ↔
        2 * (decBipConstituent z).symmetricity₁ ≤ z.2.1.length + 1 := by
    constructor
    · intro hh
      have hh' : (2 : ℚ) * (decBipConstituent z).symmetricity₁ ≤ z.2.1.length + 1 := by
        linarith
      exact_mod_cast hh'
    · intro hh
      have hh' : (2 : ℚ) * (decBipConstituent z).symmetricity₁ ≤ z.2.1.length + 1 := by
        exact_mod_cast hh
      linarith
  rw [harith]
  simp only [bipCoverClass,decide_eq_true_eq,List.mem_range,Fintype.card_fin]
  constructor
  · intro hh
    have hh' : (decBipConstituent z).symmetricity₁ ≤ (z.2.1.length + 1) / 2 := hs.2 (by
      intro u
      rw [← he]
      have := hh u u.isLt
      omega)
    omega
  · intro hh u hu
    have hh' := hs.1 (by omega) ⟨u,hu⟩
    rw [← he] at hh'
    change classSizeRaw (bipTwinsRaw z,u) ≤ (z.2.1.length + 1) / 2 at hh'
    omega

end Algo
