import Workspace.Algo.TopMasterCameronHint

/-! # A closed Cameron-to-hint producer
Use the existing cited Cameron routine once. Everything after recognition
is the polynomial kernel and first-coordinate computation proved above.
The output contract includes the subgroup, giant action, and descent index.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def camRecognizeLift (cameron : RawGens × List ℕ → Option RawCameron)
    (p : RawAction) : Option (RawCameron × RawAction) :=
  (cameron (p.2.2, p.2.1)).map (fun c => (c, camLiftAction (c, p)))

theorem polyFun_camRecognizeLift
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron) :
    PolyFun (camRecognizeLift cameron) := by
  have hin : PolyFun (fun p : RawAction => (p.2.2, p.2.1)) :=
    (polyFun_snd.comp polyFun_snd).pair (polyFun_snd.comp polyFun_fst)
  have hout : PolyFun (fun q : RawCameron × RawAction => some (q.1, camLiftAction q)) :=
    (polyFun_fst.pair polyFun_camLiftAction).comp polyFun_some
  exact (((hin.comp hc).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hout)).of_eq
      (fun p => by unfold camRecognizeLift; cases cameron (p.2.2, p.2.1) <;> rfl)

def CameronLiftSpec (f : RawAction → Option (RawCameron × RawAction)) : Prop :=
  ∀ (n m : ℕ) (p : RawAction) (ϕ : decGroup n p.1.2 →* Perm (Fin m)),
    RawAction.WF n m p ϕ → max 25 camDescentThreshold ≤ m →
    IsPrimitive (decGroup m p.2.2) →
    (m : ℝ) ^ (1 + Real.logb 2 m) ≤ Nat.card (decGroup m p.2.2) →
    ∃ (c : RawCameron) (h : c.WF m) (A : RawAction)
        (ψ : decGroup n A.1.2 →* Perm (Fin c.k)),
      f p = some (c, A) ∧ A = camLiftAction (c, p) ∧
      RawAction.WF n c.k A ψ ∧ IsGiantRep ψ ∧
      decGroup n A.1.2 = camLiftSubgroup (ϕ := ϕ) h ∧
      (decGroup n A.1.2).relIndex (decGroup n p.1.2) ≤ m ∧
      Real.logb 2 m ≤ (c.k : ℝ) ∧ A.1.2.length ≤ n * n

theorem camRecognizeLift_spec
    {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) (hs : CameronSpec cameron) :
    CameronLiftSpec (camRecognizeLift cameron) := by
  intro n m p ϕ hp hm hprim hbig
  obtain ⟨c, h, he, _, hlo, hhi⟩ := hs m p.2.2 p.2.1 hp.2.1 hp.2.2.2.1
    ((le_max_left _ _).trans hm) hprim hbig
  obtain ⟨c', h', he', hidx, hlog⟩ := camRecognize_index cameron hc hs m p.2.2 p.2.1
    hp.2.1 hp.2.2.2.1 ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) hprim hbig
  have hec : c' = c := Option.some.inj (he'.symm.trans he)
  subst c'
  refine ⟨c, h, camLiftAction (c, p), camLiftGiantHom hp h hhi,
    by simp [camRecognizeLift, he], rfl, camLiftAction_wf hp h hhi,
    camLiftGiantHom_giant hp h hhi hlo, camLiftGens_spec hp h hhi, ?_, hlog,
    camLiftGens_length hp⟩
  exact (camLiftGens_index hp h hhi).le.trans hidx

/-- The only effective recognition assumption is the existing cited witness. -/
theorem exists_polyFun_cameronLiftSpec :
    ∃ f : RawAction → Option (RawCameron × RawAction), PolyFun f ∧ CameronLiftSpec f := by
  obtain ⟨cameron, hc, hs⟩ := exists_polyFun_cameronSpec
  exact ⟨camRecognizeLift cameron, polyFun_camRecognizeLift hc, camRecognizeLift_spec hc hs⟩
end Algo
