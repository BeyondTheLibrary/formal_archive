import Workspace.Master.Descent

/-! # A supplied Johnson action and its exact block labels
The representation inferred at Section 15, line 3 may use the labels
computed in Section 11.3. Retaining their action equation prevents an
existential choice from replacing the computed representation.
-/
namespace Babai
open Equiv
open scoped Classical

structure JohnsonActionData {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    (hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B) (m t : ℕ) where
  φ : G →* Perm (Fin m)
  giant : IsGiantRep φ
  label : B ≃ binom (Fin m) t
  action : ∀ g : G, label.permCongrHom (blockHom G B hB g) = tAction t (φ g)

 theorem johnsonGiantRep_tAction {Ω : Type*} {G : Subgroup (Perm Ω)}
    {B : Set (Set Ω)} {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} (ht : 1 ≤ t) (hm : 2 * t < m) (h : ActsAsJohnsonA G B hB m t)
    (g : G) : tAction t (johnsonGiantRep ht hm h g) = johnsonBlockRep h g := by
  have hinj : Function.Injective (tAction (Ω := Fin m) t) :=
    tAction_injective ht (by rw [Fintype.card_fin]; omega)
  change (MonoidHom.ofInjective hinj
    ((MonoidHom.ofInjective hinj).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

 noncomputable def JohnsonActionData.default {Ω : Type*} {G : Subgroup (Perm Ω)}
    {B : Set (Set Ω)} {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} (ht : 1 ≤ t) (hm : 2 * t < m) (h : ActsAsJohnsonA G B hB m t) :
    JohnsonActionData hB m t where
  φ := johnsonGiantRep ht hm h
  giant := isGiantRep_johnsonGiantRep ht hm h
  label := h.choose
  action g := (johnsonGiantRep_tAction ht hm h g).symm

end Babai
