import Workspace.Algo.TopFourOutput
import Workspace.Algo.PrimitiveCaseTest
import Workspace.Algo.PrimitiveSymmetry

/-! # The computed primitive small-defect branch
The standard-block test supplies the unique identification by `T(u)`.
The symmetry test then computes both dominant twin classes. These actual
lists feed the automatic top-action entry of Section 15, line 4b.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

def top4PrimitiveInput (p : RawTop3) : Top4AutoInput :=
  ((p, primitiveDominantClass (p.1, p.2.1)), primitiveDominantClass (p.1, p.2.2))
def top4PrimitiveEnter (p : RawTop3) : Top4aNode := top4AutoEnter (top4PrimitiveInput p)

theorem polyFun_top4PrimitiveInput : PolyFun top4PrimitiveInput :=
  (polyFun_id.pair ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp
    polyFun_primitiveDominantClass)).pair
      ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_primitiveDominantClass)
theorem polyFun_top4PrimitiveEnter : PolyFun top4PrimitiveEnter :=
  polyFun_top4PrimitiveInput.comp polyFun_top4AutoEnter

theorem top4PrimitiveEnter_uniform_wf (A B e f : ℕ) : ∃ c d : ℕ,
    ∀ (n : ℕ) (p : RawTop3), p.1.1.1.length = n → Enc.size p ≤ topcsContextCap A B n →
      Top4aWF c d e f (top4PrimitiveEnter p) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4PrimitiveInput.size.exists_polyBound
  obtain ⟨a, b, hab⟩ := hF.comp (polyBound_topcsContextCap A B)
  obtain ⟨c, d, hcd⟩ := top4AutoEnter_uniform_wf a b e f
  exact ⟨c, d, fun n p hn hp => hcd n (top4PrimitiveInput p) hn
    ((hsF p).trans ((hmF _ _ hp).trans (hab n)))⟩

section Checked
variable {n m t : ℕ} {p : RawAction} {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p ϕ) (hG : IsTransitive (decGroup n p.1.2)) (hϕ : IsGiantRep ϕ)
    (hm : HugeM m (Nat.card (Fin n))) (ht : primitiveCaseTest (p, t) = true)

noncomputable def top4PrimitiveId : PrimitiveCaseId ϕ t := by
  have hn : 0 < n := by obtain ⟨u⟩ := hG.nonempty; exact Nat.zero_lt_of_lt u.isLt
  have hi := primitiveCaseTest_spec (t := t) hp.1 hp.2.1 hn hp.2.2.2.2 hϕ (veryLargeK_of_hugeM hG hm)
  simp only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at hi
  exact Classical.choice (hi.mp ht)

include hp hϕ in
theorem primitiveDominantClass_spec_raw (id : PrimitiveCaseId ϕ t)
    (hk : VeryLargeK m (maxOrbitLength (decGroup n p.1.2))) (x : RawStr) :
    colorClass (bigTwinColoring id) (decStrN n x) true = winSet m (primitiveDominantClass (p, x)) := by
  have h := primitiveDominantClass_spec hp.1 hp.2.1 hp.2.2.2.2 hϕ hk id x
  simp only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at h
  exact h.symm

include hp in
theorem primitiveDominantClass_names (x : RawStr) :
    (primitiveDominantClass (p, x)).Nodup ∧ ∀ u ∈ primitiveDominantClass (p, x), u < m :=
  ⟨List.Nodup.filter _ List.nodup_range, fun u hu => by
    simpa only [hp.2.1] using List.mem_range.mp (List.mem_filter.mp hu).1⟩

variable (x y : RawStr) (hsmall : primitiveSmallDefect (p, x) = true)

include hsmall in
theorem top4Primitive_defect :
    defect (colorAut t (hyperColoring (top4PrimitiveId hp hG hϕ hm ht) (decStrN n x))) < 1 / 2 := by
  have h := primitiveSmallDefect_spec hp.1 hp.2.1 hp.2.2.2.2 hϕ (veryLargeK_of_hugeM hG hm)
    (top4PrimitiveId hp hG hϕ hm ht) x
  simp only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at h
  exact h.mp hsmall

include hp hG hϕ hm ht hsmall in
theorem top4Primitive_large : m < 2 * (winSet m (primitiveDominantClass (p, x))).ncard := by
  have h := (smallDefect_data (top4PrimitiveId hp hG hϕ hm ht) hϕ (decStrN n x)
    (top4Primitive_defect hp hG hϕ hm ht x hsmall)).2.1
  rwa [primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) x] at h

noncomputable def top4PrimitiveSource : Top4Source n m :=
  Top4Source.ofRaw hp hG hϕ (veryLargeK_of_hugeM hG hm) (primitiveDominantClass (p, x))
    (primitiveDominantClass_names hp x).1 (primitiveDominantClass_names hp x).2
    (top4Primitive_large hp hG hϕ hm ht x hsmall)

theorem top4PrimitiveSource_action : (top4PrimitiveSource hp hG hϕ hm ht x hsmall).action = p :=
  Top4Source.ofRaw_action _ _ _ _ _ _ _ _

noncomputable def top4PrimitiveTree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (top4PrimitiveSource hp hG hϕ hm ht x hsmall).autoTree hm x y (primitiveDominantClass (p, y))
    (bigTwinColoring (top4PrimitiveId hp hG hϕ hm ht)) true
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) x)
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) y)

theorem top4Primitive_loop {c d e f : ℕ} (hcap : TopwpCap e f) (solve : RawWinSI → RawCoset) :
    let I := top4PrimitiveEnter (p, x, y)
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound c d e f solve).width I) 0 (top4aInit I)
      (top4PrimitiveTree hp hG hϕ hm ht x y hsmall) := by
  have h := (top4PrimitiveSource hp hG hϕ hm ht x hsmall).autoTree_loop (c := c) (d := d)
    hm hcap x y (primitiveDominantClass (p, y)) (primitiveDominantClass_names hp y).1
    (primitiveDominantClass_names hp y).2 (bigTwinColoring (top4PrimitiveId hp hG hϕ hm ht)) true
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) x)
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) y) solve
  dsimp only at h
  rw [top4PrimitiveSource_action] at h
  exact h

theorem top4Primitive_spec :
    let T := top4PrimitiveTree hp hG hϕ hm ht x y hsmall
    T.run = strIso (decGroup n p.1.2 : Set (Perm (Fin n))) (decStrN n x) (decStrN n y) ∧
      T.calls.length ≤ 7 * n ∧ (∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * n) := by
  have hh := smallDefect_data (top4PrimitiveId hp hG hϕ hm ht) hϕ (decStrN n x)
    (top4Primitive_defect hp hG hϕ hm ht x hsmall)
  exact (top4PrimitiveSource hp hG hϕ hm ht x hsmall).autoTree_spec hm x y
    (primitiveDominantClass (p, y)) (bigTwinColoring (top4PrimitiveId hp hG hϕ hm ht)) true
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) x)
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) y) hh.1 hh.2.2

end Checked
end Algo
