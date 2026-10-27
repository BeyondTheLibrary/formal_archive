import Workspace.Algo.TopMasterRoute

/-! # The live line 4b phase of the master dispatcher
The route provides the actual primitive and small-defect tests. Its
strict line 2 comparison supplies the large-degree hypothesis. The
computed branch then matches the supplied top-action tree on the window,
with every call lifted to the original ambient domain.
-/
set_option synthInstance.maxSize 4096
set_option quotPrecheck false
namespace Algo
open RAM RAM.Targets Babai Equiv

section Branch
variable {n m : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hgs : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3)

local notation "hm" => masterHintRoute_huge hp.2.1 hn (by omega : masterHintRoute p ≠ 1)
local notation "ht" => ((masterHintRoute_line4b p).mp hr).2.1
local notation "hs" => ((masterHintRoute_line4b p).mp hr).2.2.2
local notation "ix" => (masterHintTop p).2.1
local notation "iy" => (masterHintTop p).2.2
local notation "inner" => top4PrimitiveTree hp hG hϕ hm ht ix iy hs

noncomputable def masterLine4bTree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1) inner

include hgs in
theorem masterLine4b_group :
    decGroup p.1.1.length (masterHintTop p).1.1.2 =
      (winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :=
  decGroup_rawRestrictGens_of_raw hgs hnd hlt hinv

include hp hG hϕ hn hr in
theorem masterLine4b_inner_calls : ∀ J ∈ (inner).calls,
    J.K ⊆ (decGroup p.1.1.length (masterHintTop p).1.1.2 : Set (Perm (Fin p.1.1.length))) := by
  let F := top4PrimitiveSource hp hG hϕ hm ht ix hs
  exact F.autoTree_calls_K hm ix iy (primitiveDominantClass ((masterHintTop p).1, iy))
    (bigTwinColoring (top4PrimitiveId hp hG hϕ hm ht)) true
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) ix)
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) iy)

include hp hG hϕ hn hr in
theorem masterLine4b_inner_coset : ∀ J ∈ (inner).calls,
    IsCosetInstance (decGroup p.1.1.length (masterHintTop p).1.1.2) J := by
  let F := top4PrimitiveSource hp hG hϕ hm ht ix hs
  exact F.autoTree_calls_coset hm ix iy (primitiveDominantClass ((masterHintTop p).1, iy))
    (bigTwinColoring (top4PrimitiveId hp hG hϕ hm ht)) true
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) ix)
    (primitiveDominantClass_spec_raw hp hϕ _ (veryLargeK_of_hugeM hG hm) iy)

include hx hgs in
theorem masterLine4b_loop {a b c d e f u v : ℕ} (hcap : TopwpCap e f)
    (houter : Top4wCap e f u v) (solve : RawWinSI → RawCoset) :
    let I := masterLine4bEnter p
    LoopMatch (top4wRound a b c d e f u v solve) (top4wDecode n) (decCoset n) I
      ((top4wRound a b c d e f u v solve).width I) 0 (top4wInit I)
      (masterLine4bTree hnd hlt hinv hp hG hϕ hn hr) := by
  have hg := masterLine4b_group hgs hnd hlt hinv
  have hh := top4Primitive_loop hp hG hϕ hm ht ix iy hs (c := c) (d := d) hcap solve
  have hc : ∀ J ∈ (inner).calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range : Set (Perm (Fin p.1.1.length))) := by
    rw [← hg]
    exact masterLine4b_inner_calls (n := n) hp hG hϕ hn hr
  have ha : (inner).run ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range : Set (Perm (Fin p.1.1.length))) := by
    rw [(top4Primitive_spec hp hG hϕ hm ht ix iy hs).1, ← hg]
    exact fun _ h => h.1
  have h := top4wLoopMatch (a := a) (b := b) (gens := p.1.2.1.map (decPerm n)) hx hx hnd hlt hinv
    houter solve hh hc ha
  simp only [map_encPerm_decPerm hgs] at h
  exact h

include hx hgs in
theorem masterLine4b_spec :
    let T := masterLine4bTree hnd hlt hinv hp hG hϕ hn hr
    T.run = wIso (winSet n p.1.1) (decGroup n p.1.2.1 : Set (Perm (Fin n)))
      (decStrN n p.1.2.2.2.1) (strAct (decStrN n p.1.2.2.2.2) (decPerm n p.1.2.2.1)⁻¹) ∧
      T.calls.length ≤ 7 * p.1.1.length ∧
        ∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * p.1.1.length := by
  have hg := masterLine4b_group hgs hnd hlt hinv
  have hc : ∀ J ∈ (inner).calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range : Set (Perm (Fin p.1.1.length))) := by
    rw [← hg]
    exact masterLine4b_inner_calls (n := n) hp hG hϕ hn hr
  obtain ⟨hval, hlen, hwin⟩ := top4Primitive_spec hp hG hϕ hm ht ix iy hs
  rw [hg] at hval
  have hix : decStrN p.1.1.length ix =
      fun i => decStrN n p.1.2.2.2.1 (winEquiv n p.1.1 hnd hlt i) :=
    topwRestrictStr_decode hnd hlt _
  have hiy : decStrN p.1.1.length iy =
      fun i => strAct (decStrN n p.1.2.2.2.2) (decPerm n p.1.2.2.1)⁻¹ (winEquiv n p.1.1 hnd hlt i) :=
    top4aTarget_restrict hx hnd hlt _ _
  rw [hix, hiy] at hval
  exact top4wTree_spec hnd hlt hinv _ _ inner hc hval hlen hwin

end Branch
end Algo
