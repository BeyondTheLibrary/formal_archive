import Workspace.Algo.TopMasterHintLink

/-! # The computed image order as the live line-2 block order
The retained label identifies the two image groups. Mapping an image
list through that identification keeps its order, its length, and each
lifting coset. The kernel orbit list is unchanged.
-/
namespace Algo
open Babai Equiv
open scoped Classical

namespace MasterHintBlockLink
variable {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B} {m t : ℕ}
    {φ : G →* Perm (Fin m)} (L : MasterHintBlockLink (t := t) hB φ)

 noncomputable def imageHom : φ.range →* (blockHom G B hB).range :=
  (((L.label.permCongrHom.symm.toMonoidHom).comp (tAction t)).comp φ.range.subtype).codRestrict _
    (fun a => by
      obtain ⟨g, hg⟩ := a.property
      change L.label.permCongrHom.symm (tAction t a.val) ∈ (blockHom G B hB).range
      rw [← hg, ← L.action, MulEquiv.symm_apply_apply]
      exact ⟨g, rfl⟩)

 theorem imageHom_apply (g : G) : L.imageHom (φ.rangeRestrict g) =
    (blockHom G B hB).rangeRestrict g := by
  apply Subtype.ext
  change L.label.permCongrHom.symm (tAction t (φ g)) = blockHom G B hB g
  rw [← L.action, MulEquiv.symm_apply_apply]

 theorem imageHom_bijective (ht : 1 ≤ t) (hm : t < m) : Function.Bijective L.imageHom := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply tAction_injective ht (by simpa only [Fintype.card_fin] using hm)
    exact L.label.permCongrHom.symm.injective (congrArg Subtype.val hab)
  · intro b
    obtain ⟨g, hg⟩ := b.property
    exact ⟨φ.rangeRestrict g, (L.imageHom_apply g).trans (Subtype.ext hg)⟩

 noncomputable def imageEquiv (ht : 1 ≤ t) (hm : t < m) :
    φ.range ≃* (blockHom G B hB).range := MulEquiv.ofBijective L.imageHom (L.imageHom_bijective ht hm)

 theorem imageEquiv_apply (ht : 1 ≤ t) (hm : t < m) (g : G) :
    L.imageEquiv ht hm (φ.rangeRestrict g) = (blockHom G B hB).rangeRestrict g :=
  L.imageHom_apply g

 include L in
 theorem range_kernel (ht : 1 ≤ t) (hm : t < m) :
    kerSubgroup φ.rangeRestrict = kerSubgroup (blockHom G B hB).rangeRestrict := by
  simp only [kerSubgroup, MonoidHom.ker_rangeRestrict]
  exact L.kernel ht hm

variable [Fintype Ω] [DecidableEq Ω]

 noncomputable def line2Enum (ht : 1 ≤ t) (hm : t < m) (E : Line2Enum φ.rangeRestrict) :
    Line2Enum (blockHom G B hB).rangeRestrict where
  elements := E.elements.map (L.imageEquiv ht hm)
  cover b := List.mem_map.mpr ⟨(L.imageEquiv ht hm).symm b, E.cover _, (L.imageEquiv ht hm).apply_symm_apply b⟩
  length := by
    rw [List.length_map, ← Fintype.card_congr (L.imageEquiv ht hm).toEquiv]
    exact E.length
  orbits := ⟨E.orbits.windows, by rw [← L.range_kernel ht hm]; exact E.orbits.spec⟩

 theorem preimage_imageEquiv (ht : 1 ≤ t) (hm : t < m) (a : φ.range) :
    preimageSet (blockHom G B hB).rangeRestrict (L.imageEquiv ht hm a) =
      preimageSet φ.rangeRestrict a := by
  ext g
  change (∃ hg : g ∈ G, (blockHom G B hB).rangeRestrict ⟨g, hg⟩ = L.imageEquiv ht hm a) ↔ _
  constructor
  · rintro ⟨hg, he⟩
    exact ⟨hg, (L.imageEquiv ht hm).injective ((L.imageEquiv_apply ht hm ⟨g, hg⟩).trans he)⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, (L.imageEquiv_apply ht hm ⟨g, hg⟩).symm.trans (congrArg (L.imageEquiv ht hm) he)⟩

 theorem liftAll_imageEquiv {A : Type*} (ht : 1 ≤ t) (hm : t < m)
    (x y : Ω → A) (S : List φ.range) :
    cosetLiftAll (blockHom G B hB).rangeRestrict x y (S.map (L.imageEquiv ht hm)) =
      cosetLiftAll φ.rangeRestrict x y S := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [List.map_cons, cosetLiftAll, cosetLift, L.preimage_imageEquiv ht hm, ih]

 theorem line2Reduction_imageEquiv {A : Type*} (ht : 1 ≤ t) (hm : t < m)
    (x y : Ω → A) (E : Line2Enum φ.rangeRestrict) :
    cosetLine2ReductionWith (blockHom G B hB).rangeRestrict x y (L.line2Enum ht hm E) =
      cosetLine2ReductionWith φ.rangeRestrict x y E := by
  unfold cosetLine2ReductionWith cosetLuksBruteForceWith
  rw [show (L.line2Enum ht hm E).elements = E.elements.map (L.imageEquiv ht hm) from rfl,
    L.liftAll_imageEquiv ht hm]
  congr 1

end MasterHintBlockLink
section Live
variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}
    (d : JohnsonCaseData I) (L : MasterHintBlockLink (t := d.t) d.system.permutes d.ϕ)

 noncomputable def masterLinkedLine2Enum (E : Line2Enum d.ϕ.rangeRestrict) : Line2Enum d.blockAction :=
  L.line2Enum d.johnson.t_pos (by have := d.johnson.t_pos; have := d.johnson.two_mul_t_le; omega) E

 theorem masterLinkedLine2Coset (E : Line2Enum d.ϕ.rangeRestrict) :
    line2Coset d (masterLinkedLine2Enum d L E) =
      liftWindow d.K I.Δ d.invariant I.x
        (cosetLine2ReductionWith d.ϕ.rangeRestrict (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) E) := by
  unfold line2Coset
  congr 1
  exact L.line2Reduction_imageEquiv d.johnson.t_pos
    (by have := d.johnson.t_pos; have := d.johnson.two_mul_t_le; omega) _ _ E
end Live
end Algo
