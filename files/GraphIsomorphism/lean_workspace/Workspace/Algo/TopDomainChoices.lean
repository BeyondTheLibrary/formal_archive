import Workspace.Algo.TopWindowLive

/-! # Supplying transported top-action choices
The window computation supplies an orbit order and an odd representative.
Their images under the displayed domain equivalence are valid choices for
the paper's subtype action. No equality to a default choice is required.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

 theorem topd_orbit {Ω Ω' : Type*} (e : Ω ≃ Ω') (N : Subgroup (Perm Ω))
    (M : Subgroup (Perm Ω')) (hNM : e.permCongr '' (N : Set (Perm Ω)) = M) (u : Ω) :
    e '' orbit N u = orbit M (e u) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 hz
    have hm : e.permCongr (g : Perm Ω) ∈ M := by
      change e.permCongr (g : Perm Ω) ∈ (M : Set (Perm Ω'))
      rw [← hNM]
      exact ⟨g, g.2, rfl⟩
    refine mem_orbit_iff.2 ⟨⟨_, hm⟩, ?_⟩
    change e.permCongr (g : Perm Ω) (e u) = e z
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using congrArg e hg
  · intro hv
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 hv
    obtain ⟨a, ha, he⟩ := (hNM ▸ g.2 : (g : Perm Ω') ∈ e.permCongr '' (N : Set (Perm Ω)))
    refine ⟨a u, mem_orbit_iff.2 ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    change (g : Perm Ω') (e u) = v at hg
    rw [← he] at hg
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using hg

noncomputable def topdOrbitEnum {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (N : Subgroup (Perm Ω)) (M : Subgroup (Perm Ω'))
    (hNM : e.permCongr '' (N : Set (Perm Ω)) = M) (E : OrbitEnum N) : OrbitEnum M where
  windows := E.windows.map (fun W => e '' W)
  spec := by
    have hnN : (orbitList N).Nodup := by
      unfold orbitList
      exact List.Nodup.map orbitRel.Quotient.orbit_injective (Finset.nodup_toList _)
    have hnM : (orbitList M).Nodup := by
      unfold orbitList
      exact List.Nodup.map orbitRel.Quotient.orbit_injective (Finset.nodup_toList _)
    have hi : Function.Injective (fun W : Set Ω => e '' W) := by
      intro A B h
      ext u
      have hh := Set.ext_iff.mp h (e u)
      simpa only [Set.mem_image, Equiv.apply_eq_iff_eq, exists_eq_right] using hh
    have hn : (E.windows.map (fun W => e '' W)).Nodup :=
      List.Nodup.map hi (E.spec.nodup_iff.mpr hnN)
    have hf : E.windows.map (fun W => e '' W) ⊆ orbitList M := by
      intro W hW
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hW
      obtain ⟨u, rfl⟩ := mem_orbitList (E.spec.mem_iff.mp hA)
      rw [topd_orbit e N M hNM]
      exact orbit_mem_orbitList M (e u)
    have hb : orbitList M ⊆ E.windows.map (fun W => e '' W) := by
      intro W hW
      obtain ⟨v, rfl⟩ := mem_orbitList hW
      refine List.mem_map.2 ⟨orbit N (e.symm v), E.spec.mem_iff.mpr (orbit_mem_orbitList N _), ?_⟩
      rw [topd_orbit e N M hNM, Equiv.apply_symm_apply]
    exact (hn.subperm hf).antisymm (hnM.subperm hb)

noncomputable def TopdCompat.odd {Ω Ω' : Type*} {m : ℕ} {e : Ω ≃ Ω'}
    {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Ω')}
    {ϕ : G →* Perm (Fin m)} {ψ : H →* Perm (Fin m)} (h : TopdCompat e ϕ ψ)
    (O : TopActionOdd ϕ) : TopActionOdd ψ where
  representative := e.permCongr O.representative
  spec := by
    intro hr
    obtain ⟨hg, hodd⟩ := O.spec (by rwa [h.range])
    have hh := h.coe ⟨O.representative, hg⟩
    have hm : e.permCongr O.representative ∈ H := by
      rw [← hh]
      exact (h.group ⟨_, hg⟩).2
    refine ⟨hm, ?_⟩
    have he := h.hom ⟨O.representative, hg⟩
    have hs : h.group ⟨O.representative, hg⟩ = ⟨e.permCongr O.representative, hm⟩ := Subtype.ext hh
    rw [← hs, he]
    exact hodd

noncomputable def TopdCompat.orbits {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    {m : ℕ} {e : Ω ≃ Ω'} {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Ω')}
    {ϕ : G →* Perm (Fin m)} {ψ : H →* Perm (Fin m)} (h : TopdCompat e ϕ ψ)
    (E : OrbitEnum (kerSubgroup ϕ)) : OrbitEnum (kerSubgroup ψ) :=
  topdOrbitEnum e _ _ h.kernel E

end Algo
