import Workspace.Algo.TopMasterLineTwoTree

/-! # Image enumerations from the computed coset representatives
A kernel-coset cover gives each image exactly once within the image-group
cardinality bound. The output order is the representative order already
read by the raw descent fold.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

section Enumerate
variable {Ω H : Type*} [Fintype Ω] [DecidableEq Ω] [Group H] [Fintype H] [DecidableEq H]
    {G : Subgroup (Perm Ω)} (φ : G →* H) (R : CosetRepEnum (kerSubgroup φ) G)

 noncomputable def masterCosetTypedReps : List G :=
  R.reps.attach.map (fun r => ⟨r.val, R.mem r.property⟩)

 theorem masterCosetTypedReps_val : (masterCosetTypedReps φ R).map Subtype.val = R.reps := by
  simp [masterCosetTypedReps, List.map_map]

 theorem masterCosetImage_cover (a : φ.range) :
    a ∈ (masterCosetTypedReps φ R).map φ.rangeRestrict := by
  obtain ⟨g, hg⟩ := a.property
  have hc : g.val ∈ ⋃ r ∈ R.reps, r • (kerSubgroup φ : Set (Perm Ω)) := R.cover ▸ g.property
  obtain ⟨r, hr, ν, hν, he⟩ := Set.mem_iUnion₂.mp hc
  obtain ⟨hνG, hνφ⟩ := mem_kerSubgroup.mp hν
  have hrG := R.mem hr
  have he' : (⟨r, hrG⟩ : G) * ⟨ν, hνG⟩ = g := Subtype.ext he
  have hφ : φ ⟨r, hrG⟩ = a.val := by
    have hh := congrArg φ he'
    rw [map_mul, hνφ, mul_one] at hh
    exact hh.trans hg
  apply List.mem_map.mpr
  refine ⟨⟨r, hrG⟩, ?_, Subtype.ext hφ⟩
  exact List.mem_map.mpr ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩

 noncomputable def masterCosetImageEnum (O : OrbitEnum (kerSubgroup φ)) : Line2Enum φ.rangeRestrict where
  elements := (masterCosetTypedReps φ R).map φ.rangeRestrict
  cover := masterCosetImage_cover φ R
  length := by
    simp only [List.length_map, masterCosetTypedReps, List.length_attach]
    simpa only [masterKernel_index, Nat.card_eq_fintype_card] using R.length
  orbits := ⟨O.windows, by simpa only [kerSubgroup, MonoidHom.ker_rangeRestrict] using O.spec⟩

 theorem masterCosetImageEnum_tree {A : Type*} (x y : Ω → A) (O : OrbitEnum (kerSubgroup φ)) :
    cosetLine2ReductionWith φ.rangeRestrict x y (masterCosetImageEnum φ R O) =
      strongDescent (kerSubgroup φ) x y R.reps O.windows := by
  rw [masterLine2_strong φ.rangeRestrict x y _ (masterCosetTypedReps φ R) rfl,
    masterCosetTypedReps_val]
  change strongDescent (kerSubgroup φ.rangeRestrict) x y R.reps O.windows = _
  rw [show kerSubgroup φ.rangeRestrict = kerSubgroup φ by
    simp only [kerSubgroup, MonoidHom.ker_rangeRestrict]]

end Enumerate

section Raw
variable {n m c : ℕ} {p : MasterDescInput}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ)
    (hg : masterDescFuel c p = List.range (masterDescWidth p))
    (hid : decPerm n p.1.2.2.1 = 1)

 noncomputable def masterDescCosetEnum : CosetRepEnum (kerSubgroup φ) (decGroup n p.1.2.1) where
  reps := aggnrReps n (masterDescLists c p)
  cover := by
    have h := masterDescLists_cover hp hg
    change decCoset n (some (p.1.2.1, p.1.2.2.1)) = _ at h
    rw [decCoset_some, hid, one_smul] at h
    rw [show (masterDescLists c p).2.1 = topKernel (masterDescAction p) from rfl,
      masterDescKernel_spec hp] at h
    exact h
  length := by
    rw [aggnrReps_length, masterDescLists_count hp hg, masterKernel_index]
    exact le_of_eq (masterDescWidth_spec hp)

 noncomputable def masterDescFullOrbitEnum (hfull : p.1.1 = rawOne p.1.2.2.2.1) :
    OrbitEnum (kerSubgroup φ) where
  windows := (winOrbits (topKernel (masterDescAction p), p.1.1)).map (winSet n)
  spec := by
    have h := perm_topKernelWindows hp.1 hp.2.1 hp.2.2.2.2
    rw [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1] at h
    change ((winOrbits (topKernel (masterDescAction p), p.1.1)).map (winSet n)).Perm _
    rw [hfull]
    exact h

 noncomputable def masterDescLine2Enum (hfull : p.1.1 = rawOne p.1.2.2.2.1) :
    Line2Enum φ.rangeRestrict :=
  masterCosetImageEnum φ (masterDescCosetEnum hp hg hid) (masterDescFullOrbitEnum hp hfull)

 theorem masterDescLine2_tree (hfull : p.1.1 = rawOne p.1.2.2.2.1) :
    cosetLine2ReductionWith φ.rangeRestrict (decWinSI n p.1).x (decWinSI n p.1).y
      (masterDescLine2Enum hp hg hid hfull) = masterDescStrongTree n c p := by
  rw [masterDescLine2Enum, masterCosetImageEnum_tree]
  unfold masterDescStrongTree
  dsimp only
  rw [show (masterDescLists c p).2.1 = topKernel (masterDescAction p) from rfl,
    masterDescKernel_spec hp]
  rfl
end Raw
end Algo
