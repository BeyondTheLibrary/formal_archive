import Workspace.Algo.TopMasterReduceRoute

/-! # Returning a local leaf answer on the ambient window
Observation 11.1.11 takes the full preimage of the local coset, including
the pointwise kernel. Equation (59) then restores the candidate representative.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

def masterWindowReturn (q : RawWinSI × RawCoset) : RawCoset :=
  top3Shift (q.1.2.2.2.1, q.1.2.2.1,
    topwCosetPreimage ((q.1.2.2.2.1, q.1.2.1), q.1.1, q.2))

def masterWindowTrivialLeaf (W : RawWinSI) : RawCoset :=
  masterWindowReturn (W, masterTrivialLeaf (primitiveWindowInput W))

theorem polyFun_masterWindowReturn : PolyFun masterWindowReturn := by
  have hw : PolyFun (fun q : RawWinSI × RawCoset => q.1) := polyFun_fst
  have hx := (((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr := ((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hg := (hw.comp polyFun_snd).comp polyFun_fst
  exact (hx.pair (hr.pair (((hx.pair hg).pair ((hw.comp polyFun_fst).pair polyFun_snd)).comp
    polyFun_topwCosetPreimage))).comp polyFun_top3Shift

theorem polyFun_masterWindowTrivialLeaf : PolyFun masterWindowTrivialLeaf :=
  (polyFun_id.pair (polyFun_primitiveWindowInput.comp polyFun_masterTrivialLeaf)).comp
    polyFun_masterWindowReturn

theorem masterWindowReturn_size (q : RawWinSI × RawCoset) :
    Enc.size (masterWindowReturn q) ≤ chainBound q.1.2.2.2.1.length :=
  size_top3Shift_le rfl le_rfl _ _

/-- The group and both strings are the actual local input of the preceding leaf. -/
theorem masterWindowReturn_spec {n : ℕ} {W : RawWinSI} {c : RawCoset}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : decCoset W.1.length c = strIso
      (decGroup W.1.length (primitiveWindowInput W).1 : Set (Perm (Fin W.1.length)))
      (decStrN W.1.length (primitiveWindowInput W).2.1)
      (decStrN W.1.length (primitiveWindowInput W).2.2)) :
    decCoset n (masterWindowReturn (W, c)) = (decWinSI n W).answer := by
  have he := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  dsimp only [primitiveWindowInput] at hc
  rw [he, topwRestrictStr_decode hnd hlt, top4aTarget_restrict hx hnd hlt] at hc
  have hsub : decCoset W.1.length c ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range : Set (Perm (Fin W.1.length))) := by
    rw [hc]
    exact fun _ h => h.1
  have hpre := topwCosetPreimage_spec (gens := W.2.1.map (decPerm n)) hx hnd hlt hinv c hsub
  simp only [map_encPerm_decPerm hw] at hpre
  change decCoset n _ = topwPreimageSet W.1 hnd hlt (decGroup n W.2.1) hinv
    (decCoset W.1.length c) at hpre
  rw [masterWindowReturn, decCoset_top3Shift hx, hpre, hc, topwPreimage_strIso hnd hlt hinv]
  change _ = wIso (winSet n W.1) (decCoset n (some (W.2.1, W.2.2.1))) _ _
  rw [decCoset_some, wIso_smul]
  rfl

/-- The first Reduce-to-Johnson exit returns the original candidate-window answer. -/
theorem masterWindowTrivialLeaf_spec {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 0) :
    decCoset n (masterWindowTrivialLeaf W) = (decWinSI n W).answer := by
  apply masterWindowReturn_spec hx hw hnd hlt hinv
  exact masterTrivialLeaf_spec (length_rawRestrictStr _ _) (length_rawRestrictStr _ _)
    (rawRestrictGens_wf_of_raw hw hnd hlt hinv) ((masterReduceRoute_trivial B C₀ W).mp hr)
end Algo
