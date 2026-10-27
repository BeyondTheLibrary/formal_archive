import Workspace.Algo.TopMasterDescentPreparedSpec
import Workspace.Algo.TopMasterHintLinkTransport

/-! # The numbered hint supplies the live window action
The window dictionary conjugates the stored action and transports its
blocks. The original generator order is preserved, so the ambient action
used by the prepared descent is exactly the composition with restriction.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section Window
variable {n m t : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hw : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))

noncomputable def masterHintWindowEquiv :
    decGroup p.1.1.length (masterHintTop p).1.1.2 ≃*
      restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv :=
  (MulEquiv.subgroupCongr (decGroup_rawRestrictGens_of_raw
    (dom := p.1.2.2.2.1) hw hnd hlt hinv)).trans
    (topwGroupEquiv p.1.1 hnd hlt (decGroup n p.1.2.1) hinv)

 theorem masterHintWindowEquiv_coe (g : decGroup p.1.1.length (masterHintTop p).1.1.2) :
    (masterHintWindowEquiv hw hnd hlt hinv g).val =
      (winEquiv n p.1.1 hnd hlt).permCongrHom g.val := rfl

 theorem masterHintWindowEquiv_restrict (g : decGroup n p.1.2.1) :
    masterHintWindowEquiv hw hnd hlt hinv
      (camActionRange (masterRestrictionAction_wf hx hw hnd hlt hinv) g) = restrictOnto hinv g :=
  topwGroupEquiv_restrict hnd hlt hinv g

variable (φ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m))

noncomputable def masterHintWindowHom :
    restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m) :=
  φ.comp (masterHintWindowEquiv hw hnd hlt hinv).symm.toMonoidHom

 theorem masterHintWindowHom_restrict :
    (masterHintWindowHom hw hnd hlt hinv φ).comp (restrictOnto hinv) =
      masterHintDescHom hx hw hnd hlt hinv (ϕ := φ) := by
  apply MonoidHom.ext
  intro g
  change φ ((masterHintWindowEquiv hw hnd hlt hinv).symm (restrictOnto hinv g)) = _
  rw [← masterHintWindowEquiv_restrict hx hw hnd hlt hinv g, MulEquiv.symm_apply_apply]
  rfl

include hx in
 theorem masterHintWindowHom_wf
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 φ) :
    RawAction.WF n m (masterDescAction (masterHintDescInput p))
      ((masterHintWindowHom hw hnd hlt hinv φ).comp (restrictOnto hinv)) := by
  exact (masterHintWindowHom_restrict hx hw hnd hlt hinv φ).symm ▸
    masterHintDescInput_wf hx hw hnd hlt hinv hp

include hw in
 theorem masterHintWindowGroup_map :
    (decGroup p.1.1.length (masterHintTop p).1.1.2).map
      (winEquiv n p.1.1 hnd hlt).permCongrHom.toMonoidHom =
      restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv := by
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (masterHintWindowEquiv hw hnd hlt hinv ⟨q, hq⟩).property
  · intro hg
    refine ⟨(masterHintWindowEquiv hw hnd hlt hinv).symm ⟨g, hg⟩,
      ((masterHintWindowEquiv hw hnd hlt hinv).symm ⟨g, hg⟩).property, ?_⟩
    exact congrArg Subtype.val ((masterHintWindowEquiv hw hnd hlt hinv).apply_symm_apply ⟨g, hg⟩)

variable {B : Set (Set (Fin p.1.1.length))}
    (hs : IsSystemOfImprimitivity (decGroup p.1.1.length (masterHintTop p).1.1.2) Set.univ B)

include hw hs in
 theorem masterHintWindowSystem :
    IsSystemOfImprimitivity (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv)
      Set.univ (blockImage (winEquiv n p.1.1 hnd hlt) B) := by
  have h := isSystemOfImprimitivity_map_permCongrHom (winEquiv n p.1.1 hnd hlt) hs
  rwa [masterHintWindowGroup_map hw hnd hlt hinv] at h

 noncomputable def masterHintWindowLink (L : MasterHintBlockLink (t := t) hs.permutes φ) :
    MasterHintBlockLink (t := t) (masterHintWindowSystem hw hnd hlt hinv hs).permutes
      (masterHintWindowHom hw hnd hlt hinv φ) :=
  L.transport (winEquiv n p.1.1 hnd hlt) (masterHintWindowEquiv hw hnd hlt hinv).symm.toMonoidHom
    (fun g => congrArg Subtype.val ((masterHintWindowEquiv hw hnd hlt hinv).apply_symm_apply g))
    (masterHintWindowSystem hw hnd hlt hinv hs).permutes

include hw hnd hlt in
 theorem masterHintWindow_transitive
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2)) :
    IsTransitive (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv) := by
  have h := isTransitive_map_permCongrHom (winEquiv n p.1.1 hnd hlt) hG
  rwa [masterHintWindowGroup_map hw hnd hlt hinv] at h

 theorem masterHintWindow_two (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) :
    ∃ U ∈ blockImage (winEquiv n p.1.1 hnd hlt) B,
      ∃ V ∈ blockImage (winEquiv n p.1.1 hnd hlt) B, U ≠ V := by
  obtain ⟨U, hU, V, hV, hne⟩ := hB
  exact ⟨_, image_mem_blockImage _ hU, _, image_mem_blockImage _ hV,
    fun he => hne ((Set.image_injective.mpr (winEquiv n p.1.1 hnd hlt).injective) he)⟩
end Window
end Algo
