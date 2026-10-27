import Workspace.Algo.TopMasterJohnsonLink
import Workspace.Master.HintTransport

/-! # Transporting the retained block-action equation
The point map transports each block by its image. Composing the retained
label with the inverse block map preserves the exact action, hence also
its kernel.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

 noncomputable def MasterHintBlockLink.transport {Ω Λ : Type*}
    {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Λ)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B}
    {m t : ℕ} {φ : G →* Perm (Fin m)} (L : MasterHintBlockLink (t := t) hB φ)
    (e : Ω ≃ Λ) (F : H →* G) (hF : ∀ g : H, e.permCongrHom (F g).val = g.val)
    (hB' : ∀ g ∈ H, ∀ U ∈ blockImage e B, (g : Perm Λ) '' U ∈ blockImage e B) :
    MasterHintBlockLink (t := t) hB' (φ.comp F) where
  label := (blockImageEquiv e B).symm.trans L.label
  action g := by
    have hb (U : B) : blockImageEquiv e B (blockHom G B hB (F g) U) =
        blockHom H (blockImage e B) hB' g (blockImageEquiv e B U) := by
      apply Subtype.ext
      change (e : Ω → Λ) '' ((F g).val '' U.val) =
        g.val '' ((e : Ω → Λ) '' U.val)
      rw [← hF g]
      exact (image_permCongrHom_image_gen e (F g).val U.val).symm
    apply Equiv.ext
    intro T
    have ha := congrArg (fun f : Perm (binom (Fin m) t) => f T) (L.action (F g))
    change L.label ((blockImageEquiv e B).symm
      (blockHom H (blockImage e B) hB' g (blockImageEquiv e B (L.label.symm T)))) = _
    rw [← hb, Equiv.symm_apply_apply]
    exact ha

 theorem masterHintLinked_ofWindow {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {K : Subgroup (Perm Ω)} {Δ : Set Ω} (hinv : IsInvariant K Δ) (x : Ω → A)
    {J : SIInstance Δ A} (d : JohnsonCaseData J) (hle : d.K ≤ restrictTo K Δ hinv)
    (hd : MasterHintLinked d) : MasterHintLinked (d.ofWindow hinv x hle) := by
  obtain ⟨L⟩ := hd
  refine ⟨L.transport (windowSetEquiv Δ J.Δ)
    (windowRestrictMulEquiv hinv hle d.invariant).toMonoidHom ?_
      (d.ofWindow hinv x hle).system.permutes⟩
  intro g
  change (windowSetEquiv Δ J.Δ).permCongrHom
    ((windowRestrictMulEquiv hinv hle d.invariant) g).val = g.val
  have h := (windowRestrictMulEquiv hinv hle d.invariant).symm_apply_apply g
  exact congrArg Subtype.val h

end Algo
