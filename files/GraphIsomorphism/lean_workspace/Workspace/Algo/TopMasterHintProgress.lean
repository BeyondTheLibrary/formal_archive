import Workspace.Algo.TopMasterHintLink

/-! # The retained block action forces multiple computed kernel orbits
If the orbit scan returned at most one orbit, the restricted kernel would
be transitive on the numbered window. The retained block equation rules
this out, since a block kernel fixes each of two disjoint nonempty blocks.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

 theorem masterWinOrbit_pair {n : ℕ} {gs : RawGens} {D : List ℕ}
    (hw : RawGens.WF n gs) (hlt : ∀ u ∈ D, u < n)
    (h1 : (winOrbits (gs, D)).length ≤ 1) (u v : Fin n) (hu : u.val ∈ D) (hv : v.val ∈ D) :
    ∃ g : decGroup n gs, (g : Perm (Fin n)) u = v := by
  obtain ⟨U, hU, huU⟩ := List.mem_flatten.mp (winOrbits_cover hw hlt hu)
  obtain ⟨V, hV, hvV⟩ := List.mem_flatten.mp (winOrbits_cover hw hlt hv)
  have he : U = V := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hU
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hV
    have he : i = j := by omega
    subst j
    rfl
  subst V
  obtain ⟨j, hj, rfl⟩ := winOrbits_mem hU
  obtain ⟨_, gu, hgu⟩ := (mem_rawOrbit_iff hw (hlt j hj) u.val).mp huU
  obtain ⟨_, gv, hgv⟩ := (mem_rawOrbit_iff hw (hlt j hj) v.val).mp hvV
  refine ⟨gv * gu⁻¹, ?_⟩
  change (gv : Perm (Fin n)) ((gu : Perm (Fin n))⁻¹ u) = v
  have hgu' : (gu : Perm (Fin n)) ⟨j, hlt j hj⟩ = u := hgu
  have hgv' : (gv : Perm (Fin n)) ⟨j, hlt j hj⟩ = v := hgv
  rw [← hgu']
  change (gv : Perm (Fin n)) ((gu : Perm (Fin n)).symm ((gu : Perm (Fin n)) _)) = v
  rw [Equiv.symm_apply_apply, hgv']

section Hint
variable {n m t : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hw : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {φ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 φ)

 include hx hw hnd hlt hinv hp in
 theorem masterHintDesc_multiple_orbits
    {B : Set (Set (Fin p.1.1.length))}
    (hs : IsInvariantPartitionOn (decGroup p.1.1.length (masterHintTop p).1.1.2) Set.univ B)
    (L : MasterHintBlockLink (t := t) hs.permutes φ)
    (ht : 1 ≤ t) (hm : t < m) (h2 : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) :
    1 < (winOrbits (topKernel (masterDescAction (masterHintDescInput p)), p.1.1)).length := by
  by_contra h
  have h1 : (winOrbits (topKernel (masterDescAction (masterHintDescInput p)), p.1.1)).length ≤ 1 := by omega
  apply L.intransitive ht hm hs h2
  obtain ⟨U, hU, _, _, _⟩ := h2
  obtain ⟨u, hu⟩ := hs.nonempty U hU
  refine ⟨u, Set.eq_univ_iff_forall.mpr (fun v => ?_)⟩
  let e := winEquiv n p.1.1 hnd hlt
  have hA := masterHintDescInput_wf hx hw hnd hlt hinv hp
  obtain ⟨g, hg⟩ := masterWinOrbit_pair
    (wf_topKernel (p := (masterDescAction (masterHintDescInput p), [], [], [])) hA.1)
    hlt h1 (e u).val (e v).val (e u).property (e v).property
  have hgker : g.val ∈ kerSubgroup (masterHintDescHom hx hw hnd hlt hinv (ϕ := φ)) :=
    (masterDescKernel_spec hA).le g.property
  obtain ⟨hgG, hgφ⟩ := mem_kerSubgroup.mp hgker
  let a := camActionRange (p := masterRestrictionAction p.1)
    (masterRestrictionAction_wf (W := p.1) hx hw hnd hlt hinv) ⟨g.val, hgG⟩
  have ha : a.val ∈ kerSubgroup φ := mem_kerSubgroup.mpr ⟨a.property, hgφ⟩
  refine ⟨⟨a.val, ha⟩, ?_⟩
  change a.val u = v
  apply e.injective
  change e (e.symm (restrictHom (decGroup n p.1.2.1) (winSet n p.1.1) hinv ⟨g.val, hgG⟩ (e u))) = e v
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext hg

 include hx hw hnd hlt hinv hp in
 theorem masterHintDesc_match_of_link (a b : ℕ)
    (hxs : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hys : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    {B : Set (Set (Fin p.1.1.length))}
    (hs : IsInvariantPartitionOn (decGroup p.1.1.length (masterHintTop p).1.1.2) Set.univ B)
    (L : MasterHintBlockLink (t := t) hs.permutes φ)
    (ht : 1 ≤ t) (hm : t < m) (h2 : ∃ U ∈ B, ∃ V ∈ B, U ≠ V)
    (hr : masterHintRoute p = 1) :
    let F := masterDescOpenOps 3 masterHintDescSelect
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some p.2) (F.width (p.1, some p.2)) 0 (F.init (p.1, some p.2))
      (masterDescStrongTree n 3 (masterHintDescInput p)) :=
  masterHintDesc_match a b hxs hys hw hnd hlt hinv hp hr
    (masterHintDesc_multiple_orbits hx hw hnd hlt hinv hp hs L ht hm h2)

end Hint
end Algo
