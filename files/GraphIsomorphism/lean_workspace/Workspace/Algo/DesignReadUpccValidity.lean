import Workspace.Algo.DesignReadSkeleton

/-! # Validity of the computed UPCC exit

The dominant skeleton is coherent and homogeneous. If no non-diagonal
constituent is disconnected, it is primitive. The rank test supplies rank
at least three. Recoding its occurring colors gives exactly the natural
coloring required by the UPCC output type.
-/
set_option quotPrecheck false
namespace Algo
open Babai RAM Equiv
open scoped Classical

section
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "e" => (designDominantEquiv hw hk hl x hb hab)
local notation "cols" => (fun u v : D => binColor (designDomPairs z,(e u,e v)))

/-- The raw names and the actual skeleton have exactly the same color classes. -/
theorem designDomPairs_kernel (h2 : l+2 ≤ k) (u v u' v' : D) :
    ((((Y).skel2 (by omega)).induced D).color u v =
      (((Y).skel2 (by omega)).induced D).color u' v') ↔
      cols u v = cols u' v' := by
  dsimp only
  rw [PartitionStructure.induced_color_eq_iff,KAryPartStruct.skel2_color_eq_iff',
    designDomPairs_named hw hk hl x hb hab h2,designDomPairs_named hw hk hl x hb hab h2]

theorem designDomPairs_natKernel (h2 : l+2 ≤ k) :
    SameKernel cols ((((Y).skel2 (by omega)).induced D).natColor) := by
  intro u v u' v'
  change cols u v = cols u' v' ↔
    ((((Y).skel2 (by omega)).induced D).color u v).val =
      ((((Y).skel2 (by omega)).induced D).color u' v').val
  rw [← Fin.ext_iff]
  exact (designDomPairs_kernel hw hk hl x hb hab h2 u v u' v').symm

/-- The actual two raw tests imply UPCC validity, without assuming primitivity. -/
theorem designReadUpcc_isUPCCColoring (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    (hc : designReadHasComponents z = false) (hu : designReadHasUpcc z = true) :
    IsUPCCColoring (fun u v : D => binColor (designReadUpccTable z,(e u,e v))) := by
  have hup := hu
  simp only [designReadHasUpcc,designReadHasSkeleton,length_tupleOf,hk,
    Bool.and_eq_true,decide_eq_true_eq] at hup
  have h2 : l+2 ≤ k := hup.1
  let K := ((Y).skel2 (by omega)).induced D
  have hrank : 3 ≤ K.rank := by
    have hr := cliqueRank_spec hw hk hl h2 x hb hab
    change cliqueRank z = K.rank at hr
    omega
  have hne : (D).Nonempty := by
    let u := (K.colorWitness ⟨0,by omega⟩).1
    exact ⟨u.val,u.property⟩
  obtain ⟨hKcoh,hKhom⟩ := designDominant_coherent hα Y
    ((decWL n k p).restrTo_isCoherent hcoh hl x) (by omega) hne
  have hnc : ¬ ∃ j,IsDisconnectedColor cols j := by
    intro h
    have he : ∃ j,IsDisconnectedColor (namedBin (designDomPairs z).1.length (designDomPairs z)) j := by
      rw [designDomPairs_length]
      obtain ⟨j,hj⟩ := h
      refine ⟨j,?_⟩
      exact (isDisconnectedColor_map (c := cols)
        (c' := namedBin (dominantList z).length (designDomPairs z)) e (fun _ _ => rfl) j).mpr hj
    have hs : designReadHasComponents z = true :=
      (designReadHasComponents_spec z).mpr ⟨by simpa only [length_tupleOf,hk] using h2,he⟩
    rw [hc] at hs
    contradiction
  have hKprim : K.IsPrimitive := by
    by_contra hp
    have hd := exists_isDisconnectedColor hKhom hp
    exact hnc ((exists_isDisconnectedColor_congr (designDomPairs_natKernel hw hk hl x hb hab h2)).mpr hd)
  let P := PartitionStructure.ofNamedColoring cols
  have hker : ∀ u v u' v' : D,K.color u v = K.color u' v' ↔ P.color u v = P.color u' v' := by
    intro u v u' v'
    exact (designDomPairs_kernel hw hk hl x hb hab h2 u v u' v').trans
      (PartitionStructure.ofNamedColoring_color_eq_iff cols u v u' v').symm
  refine ⟨P,PartitionStructure.isCoherent_congr hker hKcoh,
    PartitionStructure.isUniprimitive_congr hker ⟨hKprim,hrank⟩,?_⟩
  funext u v
  exact (designReadUpccTable_names z e u v).symm

end
end Algo
