import Workspace.Algo.TopMasterCameronWindow

/-! # Recognition enters the ambient master descent
Choose the existing Cameron routine before any degree is supplied. Its
computed minimal-block input yields the signed action for descent and the
first-coordinate hint for each transitive child. All these data use the
original ambient generators and the current window.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterWindowCameron (cameron : RawGens × List ℕ → Option RawCameron)
    (W : RawWinSI) : Option (RawCameron × MasterDescInput) :=
  (cameron ((masterWindowBlockAction W).2.2, (masterWindowBlockAction W).2.1)).map
    (fun c => (c, masterWindowBlockInput W))

theorem polyFun_masterWindowCameron
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron) :
    PolyFun (masterWindowCameron cameron) := by
  have hin := ((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_snd).pair
    ((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_fst)
  have hout : PolyFun (fun q : RawCameron × RawWinSI => some (q.1, masterWindowBlockInput q.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_masterWindowBlockInput)).comp polyFun_some
  exact (((hin.comp hc).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hout)).of_eq
      (fun W => by unfold masterWindowCameron; cases (cameron
        ((masterWindowBlockAction W).2.2, (masterWindowBlockAction W).2.1)) <;> rfl)

def MasterWindowCameronSpec (f : RawWinSI → Option (RawCameron × MasterDescInput)) : Prop :=
  ∀ (n : ℕ) (W : RawWinSI), W.2.2.2.1.length = n → RawGens.WF n W.2.1 →
    W.1.Nodup → (∀ u ∈ W.1, u < n) →
    IsInvariant (decGroup n W.2.1) (winSet n W.1) →
    IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) → 2 ≤ W.1.length →
    max 25 camDescentThreshold ≤ (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length →
    ((rawMinBlocks ((primitiveWindowInput W).1, W.1)).length : ℝ) ^
      (1 + Real.logb 2 (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length) ≤
      Nat.card (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2) →
    ∃ (c : RawCameron), c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ∧
      f W = some (c, masterWindowBlockInput W) ∧
      (∀ j : ℕ, ∃ ψ : decGroup W.1.length
          (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2 →*
            Perm (Fin c.k),
        RawAction.WF W.1.length c.k
          (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1 ψ ∧
          IsGiantRep ψ) ∧
      (masterDescTree n (masterCameronDescInput (c, masterWindowBlockInput W))).calls.length ≤
        (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ∧
      Real.logb 2 (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ (c.k : ℝ)

/-- The actual recognition output supplies every action image and the descent width. -/
theorem masterWindowCameron_spec
    {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) (hs : CameronSpec cameron) :
    MasterWindowCameronSpec (masterWindowCameron cameron) := by
  intro n W hx hw hnd hlt hinv htr hn hm hb
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hprim := masterWindowBlockAction_primitive hw hnd hlt hinv htr hn
  obtain ⟨c, h, he, _, hlo, hhi⟩ := hs _ _ _ hp.2.1 hp.2.2.2.1
    ((le_max_left _ _).trans hm) hprim hb
  obtain ⟨c', h', he', hidx, hlog⟩ := camRecognize_index cameron hc hs _ _ _
    hp.2.1 hp.2.2.2.1 ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) hprim hb
  have hec : c' = c := Option.some.inj (he'.symm.trans he)
  subst c'
  have hfix : pointwiseStab (decGroup n W.2.1) (winSet n W.1) ≤
      (masterWindowBlockHom hx hw hnd hlt hinv htr hn).ker := by
    intro g hg
    exact masterWindowBlockHom_pointwise hx hw hnd hlt hinv htr hn g hg
  refine ⟨c, h, by simp only [masterWindowCameron, he, Option.map_some], ?_, ?_, hlog⟩
  · intro j
    exact masterCameronChild_wf (p := masterWindowBlockInput W) hp h hhi hlo hnd hlt hinv hfix j
  · exact masterCameronDesc_calls (p := masterWindowBlockInput W) hp h hhi hidx

/-- A single polynomial producer for all ambient degrees, using the cited Cameron witness. -/
theorem exists_polyFun_masterWindowCameronSpec :
    ∃ f : RawWinSI → Option (RawCameron × MasterDescInput),
      PolyFun f ∧ MasterWindowCameronSpec f := by
  obtain ⟨cameron, hc, hs⟩ := exists_polyFun_cameronSpec
  exact ⟨masterWindowCameron cameron, polyFun_masterWindowCameron hc,
    masterWindowCameron_spec hc hs⟩
end Algo
