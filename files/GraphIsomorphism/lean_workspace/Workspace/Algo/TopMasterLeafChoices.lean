import Workspace.Algo.TopMasterReduceBounds

/-! # The exact early exits enter the mathematical choice family
The source-fixing and small-order tests concern the induced window group,
even when the ambient window is large. Their evidence constructs the new
`Line1Case` leaf cases. The group frame uses the actual shifted target.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

def masterGroupInstance (n : ℕ) (W : RawWinSI) : SIInstance (Fin n) ℕ :=
  ⟨(decGroup n W.2.1 : Set (Perm (Fin n))), winSet n W.1, decStrN n W.2.2.2.1,
    decStrN n (top4aTarget (W.2.2.2.1, W.2.2.1, W.2.2.2.2))⟩

noncomputable def masterGroupData {n : ℕ} {W : RawWinSI}
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) :
    WindowData (masterGroupInstance n W) where
  K := decGroup n W.2.1
  isGroup := rfl
  invariant := hinv

section Window
variable {n : ℕ} {W : RawWinSI} (hw : RawGens.WF n W.2.1)
  (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
  (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hw hnd hlt in
theorem masterGroupData_card :
    Nat.card (masterGroupData hinv).windowGroup =
      Nat.card (decGroup W.1.length (primitiveWindowInput W).1) := by
  have he := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  change Nat.card (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) = _
  change decGroup W.1.length (primitiveWindowInput W).1 = _ at he
  rw [he]
  exact Nat.card_congr (topwGroupEquiv W.1 hnd hlt (decGroup n W.2.1) hinv).symm.toEquiv

include hw hnd hlt in
theorem masterGroupData_fixed (ht : masterAutTest (primitiveWindowInput W) = true) :
    (masterGroupData hinv).K ≤ wAutSubgroup (masterGroupData hinv).K
      (masterGroupInstance n W).Δ (masterGroupData hinv).invariant (masterGroupInstance n W).x := by
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have ha := (masterAutTest_spec (length_rawRestrictStr _ _) hgs).mp ht
  have he := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  intro g hg
  refine ⟨hg, ?_⟩
  intro u hu
  have hr : winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv ⟨g, hg⟩ ∈
      decGroup W.1.length (primitiveWindowInput W).1 := he.symm ▸ ⟨⟨g, hg⟩, rfl⟩
  have hf := ha _ hr
  change strAct (decStrN W.1.length (rawRestrictStr (W.2.2.2.1, W.1))) _ =
    decStrN W.1.length (rawRestrictStr (W.2.2.2.1, W.1)) at hf
  rw [topwRestrictStr_decode hnd hlt] at hf
  have hu' := strAct_eq_iff.mp hf ((winEquiv n W.1 hnd hlt).symm ⟨u, hu⟩)
  simpa only [winRestrictHom_apply, Equiv.apply_symm_apply] using hu'

/-- The first actual route gives the paper's step-1 branch evidence. -/
noncomputable def masterFixedStringCase (q B C₀ : ℕ)
    (hr : masterReduceRoute B C₀ W = 0) : Line1Case (masterGroupInstance n W) q :=
  .fixedString (masterGroupData hinv)
    (masterGroupData_fixed hw hnd hlt hinv ((masterReduceRoute_trivial B C₀ W).mp hr))

/-- The second actual route gives the paper's fixed-cutoff step-2 evidence. -/
noncomputable def masterSmallGroupCase (q B : ℕ)
    (hr : masterReduceRoute B bruteForceOrderThreshold.{0} W = 1) :
    Line1Case (masterGroupInstance n W) q := by
  apply Line1Case.smallGroup (masterGroupData hinv)
  rw [masterGroupData_card hw hnd hlt hinv]
  obtain ⟨_, ho⟩ := (masterReduceRoute_brute B bruteForceOrderThreshold.{0} W).mp hr
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have he := rawOrder_spec W.1 rfl ((primitiveWindowInput W).1.map (decPerm W.1.length))
  rw [map_encPerm_decPerm hgs] at he
  change rawOrder (W.1, (primitiveWindowInput W).1) < _ at ho
  rw [he] at ho
  exact ho
end Window

/-- Equation (59) restores the group frame's answer to the original candidate coset. -/
theorem masterGroupInstance_answer {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) :
    decPerm n W.2.2.1 • (masterGroupInstance n W).answer = (decWinSI n W).answer := by
  change decPerm n W.2.2.1 • wIso (winSet n W.1) (decGroup n W.2.1 : Set (Perm (Fin n)))
    (decStrN n W.2.2.2.1) (decStrN n (top4aTarget (W.2.2.2.1, W.2.2.1, W.2.2.2.2))) =
      wIso (winSet n W.1) (decCoset n (some (W.2.1, W.2.2.1))) _ _
  rw [top4aTarget_spec hx, decCoset_some, wIso_smul]
  rfl

/-- Exact matching to the first paper branch, including restoration of its candidate frame. -/
theorem masterFixedStringCase_loop (a b q B C₀ : ℕ) {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 0) :
    LoopMatch (masterLeafRound a b masterWindowTrivialLeaf) (decWinSI n) (decCoset n)
      W 0 0 0 ((masterFixedStringCase hw hnd hlt hinv q B C₀ hr).branch.bind
        (fun A => .done (decPerm n W.2.2.1 • A))) :=
  .done 0 0 0 _ rfl ((masterWindowTrivialLeaf_spec hx hw hnd hlt hinv hr).trans
    (masterGroupInstance_answer hx).symm)

/-- Exact matching to the second paper branch, with its one fixed absolute cutoff. -/
theorem masterSmallGroupCase_loop (a b q B : ℕ) {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B bruteForceOrderThreshold.{0} W = 1) :
    LoopMatch (masterLeafRound a b (masterWindowBruteLeaf bruteForceOrderThreshold.{0}))
      (decWinSI n) (decCoset n) W 0 0 0
      ((masterSmallGroupCase hw hnd hlt hinv q B hr).branch.bind
        (fun A => .done (decPerm n W.2.2.1 • A))) :=
  .done 0 0 0 _ rfl ((masterWindowBruteLeaf_spec hx hw hnd hlt hinv hr).trans
    (masterGroupInstance_answer hx).symm)
end Algo
