import Workspace.Algo.TopMasterHintLink

/-! # The Johnson representation retains its block labeling
The inverse of the faithful action on proper, nonempty subsets recovers
exactly the block permutation. Restricting to the equal group induced by
the lifted window keeps this equation.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

 theorem johnsonGiantRep_action {Ω : Type*} {G : Subgroup (Perm Ω)}
    {B : Set (Set Ω)} {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} (ht : 1 ≤ t) (hm : 2 * t < m) (h : ActsAsJohnsonA G B hB m t)
    (g : G) : tAction t (johnsonGiantRep ht hm h g) = johnsonBlockRep h g := by
  have hinj : Function.Injective (tAction (Ω := Fin m) t) :=
    tAction_injective ht (by rw [Fintype.card_fin]; omega)
  change (MonoidHom.ofInjective hinj
    ((MonoidHom.ofInjective hinj).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

 noncomputable def masterHintBlockLink_johnson {Ω : Type*} {G : Subgroup (Perm Ω)}
    {B : Set (Set Ω)} {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} (ht : 1 ≤ t) (hm : 2 * t < m) (h : ActsAsJohnsonA G B hB m t) :
    MasterHintBlockLink (t := t) hB (johnsonGiantRep ht hm h) where
  label := h.choose
  action g := (johnsonGiantRep_action ht hm h g).symm

 noncomputable def MasterHintBlockLink.inclusion {Ω : Type*}
    {G H : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} {φ : G →* Perm (Fin m)} (L : MasterHintBlockLink (t := t) hB φ)
    (h : H ≤ G) (hB' : ∀ g ∈ H, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B) :
    MasterHintBlockLink (t := t) hB' (φ.comp (Subgroup.inclusion h)) where
  label := L.label
  action g := by
    have hb : blockHom H B hB' g = blockHom G B hB (Subgroup.inclusion h g) := by
      apply Equiv.ext
      intro U
      apply Subtype.ext
      rfl
    rw [hb]
    exact L.action _

 theorem masterHintLinked_descent {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {I : SIInstance Ω A} (d : DescentData I) (htr : IsTransitive d.G₁) (y : Ω → A) :
    MasterHintLinked (d.johnsonCaseData htr y) := by
  let L : MasterHintBlockLink (t := d.t)
      (isSystemOfImprimitivity_descentBlocks d.blocks.system d.N_normal.le d.𝒞_system).permutes
      d.representation.φ := ⟨d.representation.label, d.representation.action⟩
  exact ⟨L.inclusion (le_of_eq d.restrictTo_K₁) (d.johnsonCaseData htr y).system.permutes⟩

 theorem masterHintLinked_descent_hint {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {I : SIInstance Ω A} (d : DescentData I) {J : SIInstance Ω A}
    {r : JohnsonCaseData J} (hr : d.hint J = some r) : MasterHintLinked r := by
  unfold DescentData.hint at hr
  split_ifs at hr with htr he
  · have hh := Option.some.inj hr
    rw [← hh]
    have transport {I J : SIInstance Ω A} (h : I = J) (q : JohnsonCaseData I)
        (hq : MasterHintLinked q) : MasterHintLinked (h ▸ q) := by
      cases h
      exact hq
    exact transport he _ (masterHintLinked_descent d htr _)

end Algo
