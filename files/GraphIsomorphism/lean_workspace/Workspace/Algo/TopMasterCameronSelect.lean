import Workspace.Algo.TopMasterCameronChain

/-! # The executable Cameron branch on one fold-state carrier
A single computed orbit keeps the Johnson hint. Otherwise the same node
evaluates each representative's orbit chain. Both cases use the final
coset register for the accumulated answer.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterCamHasHint (p : RawCameron × MasterDescInput) : Bool :=
  decide ((aggnrWindows (masterCamLists p)).length = 1)

def masterCamFoldEmbed (a : RawCoset) : AggnRecomputeState := (0, 0, none, a)

def masterCamSelectOps (f : RawMasterSI → RawCameron × MasterDescInput) :
    MasterOps AggnRecomputeState where
  width p := if masterCamHasHint (f p) then masterCamOpenWidth (f p)
    else masterDescFoldWidth (masterCamLists (f p))
  child z := if masterCamHasHint (f z.1) then masterCamOpenChild (f z.1, z.2.1, z.2.2.2.2.2)
    else masterDescFoldChild (masterCamLists (f z.1), z.2)
  init p := if masterCamHasHint (f p) then masterCamFoldEmbed none
    else masterDescFoldInit (masterCamLists (f p))
  combine z := if masterCamHasHint (f z.1) then
      masterCamFoldEmbed (masterDescJoin (z.1.1.2.2.2.1, z.2.2.1.2.2.2, z.2.2.2))
    else masterDescFoldCombine (masterCamLists (f z.1), z.2)
  finish z := top2NormC z.1.1.2.2.2.1 z.2.2.2.2

theorem polyFun_masterCamHasHint : PolyFun masterCamHasHint := by
  have hw : PolyFun (fun p : RawCameron × MasterDescInput =>
      (aggnrWindows (masterCamLists p)).length) :=
    ((((polyFun_masterCamLists.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_length)
  exact hw.natEq (polyFun_const 1)

theorem polyFun_masterCamFoldEmbed : PolyFun masterCamFoldEmbed :=
  (polyFun_const 0).pair ((polyFun_const 0).pair ((polyFun_const none).pair polyFun_id))

theorem masterCamFoldEmbed_size (a : RawCoset) :
    Enc.size (masterCamFoldEmbed a) ≤ 16 * (Enc.size a + 4) := by
  have h1 := size_pair_le' (masterCamFoldEmbed a)
  have h2 := size_pair_le' (masterCamFoldEmbed a).2
  have h3 := size_pair_le' (masterCamFoldEmbed a).2.2
  have h0 := size_nat_le_self 0
  dsimp only [masterCamFoldEmbed] at h1 h2 h3 ⊢
  rw [size_none] at h3
  omega

theorem masterCamSelect_polyFun (f : RawMasterSI → RawCameron × MasterDescInput)
    (hf : PolyFun f) :
    PolyFun (masterCamSelectOps f).width ∧ PolyFun (masterCamSelectOps f).child ∧
    PolyFun (masterCamSelectOps f).init ∧ PolyFun (masterCamSelectOps f).combine ∧
    PolyFun (masterCamSelectOps f).finish := by
  have ht := hf.comp polyFun_masterCamHasHint
  have hl := hf.comp polyFun_masterCamLists
  have hx : PolyFun (fun p : RawMasterSI => p.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun s : AggnRecomputeState => s.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PolyFun.ite ht (hf.comp polyFun_masterCamOpenWidth) (hl.comp polyFun_masterDescFoldWidth)
  · dsimp only [masterCamSelectOps]
    apply PolyFun.ite (polyFun_fst.comp ht)
    · exact (((polyFun_fst.comp hf).pair ((polyFun_snd.comp polyFun_fst).pair
        ((polyFun_snd.comp polyFun_snd).comp ha))).comp polyFun_masterCamOpenChild)
    · exact ((polyFun_fst.comp hl).pair polyFun_snd).comp polyFun_masterDescFoldChild
  · exact PolyFun.ite ht (polyFun_const (masterCamFoldEmbed none)) (hl.comp polyFun_masterDescFoldInit)
  · dsimp only [masterCamSelectOps]
    apply PolyFun.ite (polyFun_fst.comp ht)
    · exact ((((polyFun_fst.comp hx).pair ((((polyFun_snd.comp polyFun_snd).comp
        polyFun_fst).comp ha).pair ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp
        polyFun_masterDescJoin).comp polyFun_masterCamFoldEmbed)
    · exact ((polyFun_fst.comp hl).pair polyFun_snd).comp polyFun_masterDescFoldCombine
  · exact ((polyFun_fst.comp hx).pair (polyFun_snd.comp ha)).comp polyFun_top2NormC

theorem masterCamSelect_runCostQ (a b : ℕ) (f : RawMasterSI → RawCameron × MasterDescInput)
    (hf : PolyFun f) (hsource : ∀ p, (f p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterCamSelectOps f))) := by
  obtain ⟨B, hB, hmB, hb⟩ := masterStoredDesc_uniform_bounds a b
    (fun p => masterCamLists (f p)) (hf.comp polyFun_masterCamLists).quasiFun hsource
  let C := fun n => 16 * (B n + chainBound n + n + 10)
  have hC : QuasiPolyBound C := (polyBound_const 16).quasiPoly.mul
    (((hB.add polyBound_chainBound.quasiPoly).add polyBound_id.quasiPoly).add
      (polyBound_const 10).quasiPoly)
  have hmC : Monotone C := by
    intro i j hij
    have h1 := hmB hij
    have h2 := mono_chainBound hij
    dsimp only [C]
    omega
  obtain ⟨hw, hc, hi, hu, hfin⟩ := masterCamSelect_polyFun f hf
  refine ⟨masterAdmittedRunCostQ a b (masterCamSelectOps f) C C hC hmC hC
    hw.quasiFun hc.quasiFun hi.quasiFun hu.quasiFun hfin.quasiFun ?_ ?_ ?_ ?_⟩
  · intro p hp
    have h0 := masterCamFoldEmbed_size none
    rw [size_none] at h0
    have h1 : Enc.size (masterDescFoldInit (masterCamLists (f p))) ≤ B (masterDegree p) :=
      (hb p hp).1
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega
  · intro p j s A hp _ _
    have h0 := masterCamFoldEmbed_size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A))
    have h1 := size_top2NormC_le (dom := p.1.2.2.2.1) rfl le_rfl
      (rawCosetJoin (p.1.2.2.2.1, s.2.2.2, A))
    change Enc.size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A)) ≤ chainBound (masterDegree p) at h1
    have h2 : Enc.size (masterDescFoldCombine (masterCamLists (f p), j, s, A)) ≤
        B (masterDegree p) := (hb p hp).2.1 j s A
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega
  · intro p s _ _
    have hs := size_top2NormC_le (n := masterDegree p) (dom := p.1.2.2.2.1) rfl le_rfl s.2.2.2
    exact hs.trans (by unfold masterInputCap; omega)
  · intro p hp
    have h0 : masterCamOpenWidth (f p) ≤ masterDegree p :=
      (Nat.min_le_right _ _).trans_eq (congrArg List.length (hsource p))
    have h1 : masterDescFoldWidth (masterCamLists (f p)) ≤ B (masterDegree p) := (hb p hp).2.2
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega
end Algo
