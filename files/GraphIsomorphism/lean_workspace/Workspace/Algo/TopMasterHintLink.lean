import Workspace.Algo.TopMasterHintDescentMatch
import Workspace.Master.AlignDominantData

/-! # The retained giant action agrees with its Johnson block action
A giant representation alone does not specify which block action line 2
uses. The retained validity data include the labeling equation supplied
by the Johnson construction. Faithfulness of the action on proper,
nonempty subsets then identifies the two kernels.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

/-- The labeling is live data; its equation is required for every group element. -/
structure MasterHintBlockLink {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    (hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B) {m t : ℕ}
    (φ : G →* Perm (Fin m)) where
  label : B ≃ binom (Fin m) t
  action : ∀ g : G, label.permCongrHom (blockHom G B hB g) = tAction t (φ g)

namespace MasterHintBlockLink
variable {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    {hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B} {m t : ℕ}
    {φ : G →* Perm (Fin m)} (L : MasterHintBlockLink (t := t) hB φ)

 include L in
 theorem kernel (ht : 1 ≤ t) (hm : t < m) : kerSubgroup φ = blockKernel G B hB := by
  have hker : φ.ker = (blockHom G B hB).ker := by
    ext g
    change φ g = 1 ↔ blockHom G B hB g = 1
    constructor
    · intro h
      apply L.label.permCongrHom.injective
      rw [L.action, h, map_one, map_one]
    · intro h
      apply tAction_injective ht (by simpa only [Fintype.card_fin] using hm)
      rw [← L.action, h, map_one, map_one]
  exact congrArg (fun H : Subgroup G => H.map G.subtype) hker

 include L in
 theorem intransitive [Fintype Ω] (ht : 1 ≤ t) (hm : t < m)
    (hs : IsInvariantPartitionOn G Set.univ B)
    (h2 : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) : ¬IsTransitive (kerSubgroup φ) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := h2
  rw [L.kernel ht hm]
  exact not_isTransitive_blockKernel hs hU hV hUV

 include L in
 theorem orbit_half [Fintype Ω] (ht : 1 ≤ t) (hm : t < m)
    (hG : IsTransitive G) (hs : IsInvariantPartitionOn G Set.univ B)
    (h2 : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) (u : Ω) :
    2 * (orbit (kerSubgroup φ) u).ncard ≤ Fintype.card Ω := by
  obtain ⟨U, hU, V, hV, hUV⟩ := h2
  rw [L.kernel ht hm]
  exact two_mul_ncard_orbit_le hG hs hU hV hUV u

end MasterHintBlockLink

/-- The extra semantic invariant for a retained Johnson hint. It does not
change the mathematical Johnson-case statement or choose a new action. -/
def MasterHintLinked {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {I : SIInstance Ω A} (d : JohnsonCaseData I) : Prop :=
  Nonempty (MasterHintBlockLink (t := d.t) d.system.permutes d.ϕ)

 theorem masterHintLinked_kernel {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {I : SIInstance Ω A} {d : JohnsonCaseData I} (h : MasterHintLinked d) :
    kerSubgroup d.ϕ = kerSubgroup d.blockAction := by
  obtain ⟨L⟩ := h
  rw [d.kerSubgroup_blockAction]
  apply L.kernel d.johnson.t_pos
  have h1 := d.johnson.t_pos
  have h2 := d.johnson.two_mul_t_le
  omega

 theorem masterHintLinked_orbit_half {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {I : SIInstance Ω A} {d : JohnsonCaseData I} (h : MasterHintLinked d) (u : I.Δ) :
    2 * (orbit (kerSubgroup d.ϕ) u).ncard ≤ I.windowSize := by
  obtain ⟨L⟩ := h
  have hm : d.t < d.m := by have := d.johnson.t_pos; have := d.johnson.two_mul_t_le; omega
  have hh := L.orbit_half d.johnson.t_pos hm d.transitive d.system.isInvariantPartitionOn d.two_blocks u
  have hn : Fintype.card I.Δ = I.windowSize := by
    rw [← Nat.card_eq_fintype_card, SIInstance.windowSize, Nat.card_coe_set_eq]
  exact hn ▸ hh

end Algo
