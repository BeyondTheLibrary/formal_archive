import Workspace.Algo.TopMasterWindowAction
import Workspace.Master.AlignDominantData

/-! # The computed Cameron hint on a descended window
The ambient block action is trivial on permutations fixing the window.
Its recovered first-coordinate action therefore factors through the
window restriction. The same ordered image rows become the live hint.
As in Section 11.3, an intransitive child first returns to the Chain Rule.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- A descended child with the actual first-coordinate images. -/
def masterCameronChildInput (q : (RawCameron × MasterDescInput) × ℕ) : MasterHintInput :=
  (masterDescJob (masterCameronDescInput q.1, q.2),
    camLiftHint (q.1.1, masterDescAction q.1.2))

/-- Keep the hint precisely when the current window action is transitive. -/
def masterCameronChild (q : (RawCameron × MasterDescInput) × ℕ) : RawMasterSI :=
  let p := masterCameronChildInput q
  (p.1, if rawIsTransitive ((primitiveWindowInput p.1).1, p.1.1) then some p.2 else none)

theorem polyFun_masterCameronChildInput : PolyFun masterCameronChildInput :=
  (((polyFun_fst.comp polyFun_masterCameronDescInput).pair polyFun_snd).comp
    polyFun_masterDescJob).pair
      (((polyFun_fst.comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_snd).comp polyFun_masterDescAction)).comp polyFun_camLiftHint)

theorem polyFun_masterCameronChild : PolyFun masterCameronChild := by
  have hw := polyFun_masterCameronChildInput.comp polyFun_fst
  have ht := (((hw.comp polyFun_primitiveWindowInput).comp polyFun_fst).pair
    (hw.comp polyFun_fst)).comp polyFun_rawIsTransitive
  exact hw.pair (PolyFun.ite ht
    ((polyFun_masterCameronChildInput.comp polyFun_snd).comp polyFun_some) (polyFun_const none))

/-- The source restriction and image order agree as raw arrays. -/
theorem masterCameronChild_action (c : RawCameron) (p : MasterDescInput) (j : ℕ) :
    (masterHintTop (masterCameronChildInput ((c, p), j))).1 =
      topwAction (camLiftAction (c, masterDescAction p), p.1.1) := rfl

section Factor
variable {n m : ℕ} {p : RawAction} {c : RawCameron}
  {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
  (hp : RawAction.WF n m p ϕ) (h : c.WF m)
  (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
    wreathProduct (JohnsonS c.k c.t) c.s)
  {Δ : Set (Fin n)} (hfix : pointwiseStab (decGroup n p.1.2) Δ ≤ ϕ.ker)

include hfix in
/-- Recovering a coordinate image keeps the pointwise-window kernel. -/
theorem camLiftGiantHom_pointwise :
    pointwiseStab (decGroup n (camLiftGens (c, p))) Δ ≤
      (camLiftGiantHom (p := p) hp h hhi).ker := by
  intro g hg
  have hg' : Subgroup.inclusion (camLiftGens_le hp h hhi) g ∈
      pointwiseStab (decGroup n p.1.2) Δ := by
    apply mem_pointwiseStab.mpr
    intro u hu
    exact mem_pointwiseStab.mp hg u hu
  have he : camLiftIntoNbar hp h hhi g = 1 := Subtype.ext (hfix hg')
  change camNbarPointHom h (camLiftIntoNbar hp h hhi g) = 1
  rw [he]
  exact (camNbarPointHom h).map_one
end Factor

section Child
variable {n m : ℕ} {p : MasterDescInput} {c : RawCameron}
  {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
  (hp : RawAction.WF n m (masterDescAction p) ϕ) (h : c.WF m)
  (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
    wreathProduct (JohnsonS c.k c.t) c.s)
  (hlo : basePower (JohnsonA c.k c.t) c.s ≤
    (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom)
  (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
  (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
  (hfix : pointwiseStab (decGroup n p.1.2.1) (winSet n p.1.1) ≤ ϕ.ker)

include hp h hhi hlo hnd hlt hinv hfix in
/-- The computed hint has a giant action on the exact restricted child generators. -/
theorem masterCameronChild_wf (j : ℕ) :
    ∃ ψ : decGroup p.1.1.length
        (masterHintTop (masterCameronChildInput ((c, p), j))).1.1.2 →* Perm (Fin c.k),
      RawAction.WF p.1.1.length c.k
        (masterHintTop (masterCameronChildInput ((c, p), j))).1 ψ ∧ IsGiantRep ψ := by
  have hsub := camLiftGens_le hp h hhi
  have hi := isInvariant_of_le hinv hsub
  have hf := camLiftGiantHom_pointwise hp h hhi hfix
  let ρ := restrictFactor hi (camLiftGiantHom (p := masterDescAction p) hp h hhi) hf
  have hg : IsGiantRep ρ :=
    isGiantRep_restrictFactor hi _ hf (camLiftGiantHom_giant hp h hhi hlo)
  have hfactor : ∀ g : decGroup n (camLiftGens (c, masterDescAction p)),
      camLiftGiantHom hp h hhi g =
        ρ ⟨restrictHom _ _ hi g, ⟨g, rfl⟩⟩ := by
    intro g
    exact (restrictFactor_restrictOnto hi _ hf g).symm
  have hh := topwAction_WF_raw (camLiftAction_wf hp h hhi) hnd hlt hi ρ hg hfactor
  simpa only [masterCameronChild_action] using hh

include hp h hhi hnd hlt hinv in
/-- A stored hint is installed only on a transitive window, as required at master entry. -/
theorem masterCameronChild_transitive (j : ℕ) (r : RawMasterHint)
    (hr : (masterCameronChild ((c, p), j)).2 = some r) :
    IsTransitive (decGroup p.1.1.length
      (masterHintTop (masterCameronChildInput ((c, p), j))).1.1.2) := by
  have ht : rawIsTransitive
      ((primitiveWindowInput (masterCameronChildInput ((c, p), j)).1).1, p.1.1) = true := by
    dsimp only [masterCameronChild] at hr
    split_ifs at hr with ht
    exact ht
  have hw := rawRestrictGens_wf_of_raw (dom := p.1.2.2.2.1) (camLiftGens_wf hp) hnd hlt
    (isInvariant_of_le hinv (camLiftGens_le hp h hhi))
  exact (rawIsTransitive_eq_true_iff hw rfl).mp ht
end Child
end Algo
