import Workspace.Algo.TopPrimitiveLeafEntry
import Workspace.Algo.TopFourAmbientOutput

/-! # Line 4a on an ambient window and candidate coset
Equation (59) first shifts the target by the candidate representative.
The direct leaf solves the restricted action in the displayed window
labels. Observation 11.1.11 lifts its entire coset, including the kernel,
and the representative then shifts that answer back.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

def primitiveWindowInput (p : RawWinSI) : RawSI :=
  (rawRestrictGens ((p.2.2.2.1, p.2.1), p.1),
    rawRestrictStr (p.2.2.2.1, p.1),
    rawRestrictStr (top4aTarget (p.2.2.2.1, p.2.2.1, p.2.2.2.2), p.1))
def primitiveWindowLeaf (p : RawWinSI) : RawCoset :=
  top3Shift (p.2.2.2.1, p.2.2.1,
    topwCosetPreimage ((p.2.2.2.1, p.2.1), p.1, primitiveLeaf (primitiveWindowInput p)))

theorem polyFun_primitiveWindowInput : PolyFun primitiveWindowInput := by
  have hw : PolyFun (fun p : RawWinSI => p.1) := polyFun_fst
  have hg : PolyFun (fun p : RawWinSI => p.2.1) := polyFun_snd.comp polyFun_fst
  have hr : PolyFun (fun p : RawWinSI => p.2.2.1) := (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hx : PolyFun (fun p : RawWinSI => p.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun p : RawWinSI => p.2.2.2.2) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  exact (((hx.pair hg).pair hw).comp polyFun_rawRestrictGens).pair
    (((hx.pair hw).comp polyFun_rawRestrictStr).pair
      ((((hx.pair (hr.pair hy)).comp polyFun_top4aTarget).pair hw).comp polyFun_rawRestrictStr))

theorem polyFun_primitiveWindowLeaf : PolyFun primitiveWindowLeaf := by
  have hw : PolyFun (fun p : RawWinSI => p.1) := polyFun_fst
  have hg : PolyFun (fun p : RawWinSI => p.2.1) := polyFun_snd.comp polyFun_fst
  have hr : PolyFun (fun p : RawWinSI => p.2.2.1) := (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hx : PolyFun (fun p : RawWinSI => p.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact (hx.pair (hr.pair (((hx.pair hg).pair
    (hw.pair (polyFun_primitiveWindowInput.comp polyFun_primitiveLeaf))).comp
      polyFun_topwCosetPreimage))).comp polyFun_top3Shift

theorem primitiveWindowLeaf_size (p : RawWinSI) :
    Enc.size (primitiveWindowLeaf p) ≤ chainBound p.2.2.2.1.length :=
  size_top3Shift_le rfl le_rfl _ _

section Window
variable {n : ℕ} {dom Δ : List ℕ} {gs : RawGens}
    (hgs : RawGens.WF n gs) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (decGroup n gs) (winSet n Δ))
include hgs hnd hlt hinv

theorem rawRestrictGens_wf_of_raw :
    RawGens.WF Δ.length (rawRestrictGens ((dom, gs), Δ)) := by
  intro r hr
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
  have hgm : decPerm n g ∈ decGroup n gs :=
    Subgroup.subset_closure (List.mem_map.mpr ⟨g, hg, rfl⟩)
  rw [← encPerm_decPerm (hgs g hg), rawRestrictPerm_spec hnd hlt hinv hgm]
  exact wf_encPerm _ _

theorem decGroup_rawRestrictGens_of_raw :
    decGroup Δ.length (rawRestrictGens ((dom, gs), Δ)) =
      (winRestrictHom n Δ hnd hlt (decGroup n gs) hinv).range := by
  have h := decGroup_rawRestrictGens hnd hlt dom (gs.map (decPerm n)) hinv
  simpa only [map_encPerm_decPerm hgs] using h

end Window

theorem primitiveWindowLeaf_spec {n : ℕ} {p : RawWinSI}
    (hx : p.2.2.2.1.length = n) (hgs : RawGens.WF n p.2.1)
    (hnd : p.1.Nodup) (hlt : ∀ u ∈ p.1, u < n)
    (hinv : IsInvariant (decGroup n p.2.1) (winSet n p.1))
    (hgiant : alternatingGroup (Fin p.1.length) ≤
      (winRestrictHom n p.1 hnd hlt (decGroup n p.2.1) hinv).range) :
    decCoset n (primitiveWindowLeaf p) = (decWinSI n p).answer := by
  have hgroup := decGroup_rawRestrictGens_of_raw (dom := p.2.2.2.1) hgs hnd hlt hinv
  have hi := primitiveLeaf_spec (p := primitiveWindowInput p)
    (rawRestrictGens_wf_of_raw (dom := p.2.2.2.1) hgs hnd hlt hinv)
    (length_rawRestrictStr p.2.2.2.1 p.1)
    (length_rawRestrictStr (top4aTarget (p.2.2.2.1, p.2.2.1, p.2.2.2.2)) p.1)
    (hgroup.symm ▸ hgiant)
  change decCoset p.1.length (primitiveLeaf (primitiveWindowInput p)) = _ at hi
  dsimp only [primitiveWindowInput] at hi
  rw [hgroup, topwRestrictStr_decode hnd hlt, top4aTarget_restrict hx hnd hlt] at hi
  change decCoset p.1.length (primitiveLeaf (primitiveWindowInput p)) = _ at hi
  have hsub : decCoset p.1.length (primitiveLeaf (primitiveWindowInput p)) ⊆
      ((winRestrictHom n p.1 hnd hlt (decGroup n p.2.1) hinv).range : Set (Perm (Fin p.1.length))) := by
    rw [hi]
    exact fun _ h => h.1
  have hpre := topwCosetPreimage_spec (gens := p.2.1.map (decPerm n)) hx hnd hlt hinv
    (primitiveLeaf (primitiveWindowInput p)) hsub
  simp only [map_encPerm_decPerm hgs] at hpre
  change decCoset n _ = topwPreimageSet p.1 hnd hlt (decGroup n p.2.1) hinv
    (decCoset p.1.length (primitiveLeaf (primitiveWindowInput p))) at hpre
  rw [primitiveWindowLeaf, decCoset_top3Shift hx, hpre, hi]
  rw [topwPreimage_strIso hnd hlt hinv]
  change _ = wIso (winSet n p.1) (decCoset n (some (p.2.1, p.2.2.1))) _ _
  rw [decCoset_some, wIso_smul]
  rfl

end Algo
